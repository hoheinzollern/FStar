(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"

module Microsoft.FStar.Tc.Env

open Microsoft.FStar
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util
open Microsoft.FStar.Absyn.Const
open Microsoft.FStar.Util
open Microsoft.FStar.Profiling 
open Microsoft.FStar.Tc
open Microsoft.FStar.Tc.Errors
open Microsoft.FStar.Absyn.Util
   
type binding =
  | Binding_var of bvvdef * typ
  | Binding_typ of btvdef * knd
  | Binding_lid of lident * typ
  | Binding_sig of sigelt 

type sigtable = Util.smap<sigelt>
let default_table_size = 200
let strlid_of_sigelt se = match lid_of_sigelt se with 
  | None -> None
  | Some l -> Some (text_of_lid l)
let signature_to_sigtables s = 
  let ht = Util.smap_create default_table_size in
  let _ = List.iter (fun se -> 
    let lids = lids_of_sigelt se in
    List.iter (fun l -> Util.smap_add ht l.str se) lids) s in
  ht
      
let modules_to_sigtables mods = 
  signature_to_sigtables (List.collect (fun (_,m) -> m.declarations) mods)

type level = 
  | Expr
  | Type
  | Kind

type env = {
  range:Range.range;             (* the source location of the term being checked *)
  curmodule: lident;             (* Name of this module *)
  gamma:list<binding>;           (* Local typing environment and signature elements *)
  modules:list<modul>;           (* already fully type checked modules *)
  expected_typ:option<typ>;      (* type expected by the context *)
  level:level;                   (* current term being checked is at level *)
  sigtab:sigtable;               (* a dictionary of long-names to sigelts *)
  is_pattern:bool;               (* is the current term being checked a pattern? *)
  instantiate_targs:bool;        (* instantiate implicit type arguments? default=true *)
  instantiate_vargs:bool         (* instantiate implicit value agruments? default=true *)
}

let rec add_sigelt env se = match se with 
  | Sig_bundle(ses, _) -> add_sigelts env ses
  | _ -> 
    let lids = lids_of_sigelt se in
    List.iter (fun l -> Util.smap_add env.sigtab l.str se) lids
and add_sigelts (env:env) ses = 
  ses |> List.iter (add_sigelt env)

let initial_env module_lid =
  { range=Syntax.dummyRange;
    curmodule=module_lid;
    gamma= [];
    modules= [];
    expected_typ=None;
    level=Expr;
    sigtab=Util.smap_create default_table_size;
    is_pattern=false;
    instantiate_targs=true;
    instantiate_vargs=true
  }

let finish_module env m = 
  let sigs = env.gamma |> List.collect (function 
    | Binding_sig se -> [se]
    | _ -> [])  in
  add_sigelts env sigs;
  {env with 
    gamma=[];
    modules=m::env.modules}


let set_level env level = {env with level=level}
let is_level env level = env.level=level
let modules env = env.modules
let current_module env = env.curmodule
let set_current_module env lid = {env with curmodule=lid} 
let set_range e r = {e with range=r}
let get_range e = e.range
let find_in_sigtab env lid = Util.smap_try_find env.sigtab (text_of_lid lid)

let lookup_bvvdef env (bvvd:bvvdef) : option<typ> = 
  Util.find_map env.gamma (function
    | Binding_var (id, t) when (Util.bvd_eq id bvvd) -> Some t
    | _ -> None) 
      
let lookup_bvar env (bv:bvvar) = 
  match lookup_bvvdef env bv.v with
    | None -> raise (Error(Tc.Errors.variable_not_found bv.v, Util.range_of_bvd bv.v))
    | Some t -> t 
    
let lookup_qname env (lid:lident) : option<either<typ, sigelt>>  = 
  let in_cur_mod (l:lident) = (* TODO: need a more efficient namespace check! *)
    let cur = current_module env in 
    if l.nsstr = cur.str then true (* fast case; works for everything except records *)
    else if Util.starts_with l.nsstr cur.str
    then let lns = l.ns@[l.ident] in
         let cur = cur.ns@[cur.ident] in
         let rec aux c l = match c, l with 
          | [], _ -> true
          | _, [] -> false
          | hd::tl, hd'::tl' when (hd.idText=hd'.idText) -> aux tl tl'
          | _ -> false in
         aux cur lns
    else false in
  if in_cur_mod lid 
  then 
    Util.find_map env.gamma (function 
    | Binding_lid(l,t) -> if lid_equals lid l then Some (Inl t) else None
    | Binding_sig s -> 
      let lids = lids_of_sigelt s in 
      if lids |> Util.for_some (lid_equals lid) then Some (Inr s) else None
    | _ -> None) 
  else match find_in_sigtab env lid with
    | Some se -> Some (Inr se) 
    | None -> None

let try_lookup_val_decl env lid = 
  match lookup_qname env lid with
    | Some (Inr (Sig_val_decl(_, t, _, _, _))) -> Some t
    | _ -> None

let lookup_val_decl (env:env) lid = 
  match lookup_qname env lid with
    | Some (Inr (Sig_val_decl(_, t, _, _, _))) -> t
    | _ -> raise (Error(Tc.Errors.name_not_found lid, range_of_lid lid))

let lookup_lid env lid = 
  let not_found () = 
    let _ = Util.smap_fold env.sigtab (fun k _ _ -> Util.print_string (Util.format1 "%s, " k)) () in
    raise (Error(Tc.Errors.name_not_found lid, range_of_lid lid)) in
  let mapper = function
    | Inl t
    | Inr (Sig_datacon(_, t, _, _))  
    | Inr (Sig_logic_function(_, t, _, _))
    | Inr (Sig_val_decl (_, t, _, _, _)) 
    | Inr (Sig_let((_, [(_, t, _)]), _)) -> Some t 
    | Inr (Sig_let((_, lbs), _)) -> 
        Util.find_map lbs (function 
          | (Inl _, _, _) -> failwith "impossible"
          | (Inr lid', t, e) -> 
            if lid_equals lid lid' 
            then Some t
            else None) 
    | t -> None
  in
    match Util.bind_opt (lookup_qname env lid) mapper with 
      | Some t -> t
      | None -> not_found ()

let lookup_datacon env lid = 
  match lookup_qname env lid with
    | Some (Inr (Sig_datacon (_, t, _, _))) -> t
    | _ -> raise (Error(Tc.Errors.name_not_found lid, range_of_lid lid))
      
let is_datacon env lid = 
  match lookup_qname env lid with
    | Some (Inr (Sig_datacon (_, t, _, _))) -> true
    | _ -> false

let is_logic_function env lid =
  match lookup_qname env lid with 
    | Some (Inr (Sig_logic_function (_, t, _, _))) -> true
    | _ -> false
    
let is_logic_data env lid = 
  match lookup_qname env lid with 
    | Some (Inr (Sig_tycon(_, _, _, _, _, tags, _))) -> 
        Util.for_some (fun t -> t=Logic_data) tags 
    | _ -> false
  
let is_logic_array env lid =
  match lookup_qname env lid with 
    | Some (Inr (Sig_tycon(_, _, _, _, _, tags, _))) -> 
        Util.for_some (function 
            | Logic_array _ -> true 
            | _ -> false) tags 
    | _ -> false

let is_record env lid =
  match lookup_qname env lid with 
    | Some (Inr (Sig_tycon(_, _, _, _, _, tags, _))) -> 
        Util.for_some (fun t -> t=Logic_record) tags 
    | _ -> false

let lookup_datacons_of_typ (env:env) lid = 
  match lookup_qname env lid with 
    | Some (Inr (Sig_tycon(_, _, _, _, datas, _, _))) -> Some (List.map (fun l -> (l, lookup_lid env l)) datas)
    | _ -> None
    
let lookup_typ_abbrev env lid =
  match lookup_qname env lid with 
    | Some (Inr (Sig_typ_abbrev (lid, tps, _, t, _))) -> Some (Util.close_with_lam tps t)
    | _ -> None
        
let lookup_btvdef env (btvd:btvdef): option<knd> = 
  Util.find_map env.gamma (function
    | Binding_typ (id, k) when Util.bvd_eq id btvd -> Some k
    | _ -> None)  
    
let lookup_btvar env (btv:btvar) = 
  match lookup_btvdef env btv.v with
    | None -> raise (Error(Tc.Errors.variable_not_found btv.v, Util.range_of_bvd btv.v))
    | Some k -> k 

let lookup_typ_lid env (ftv:lident) : knd = 
  match lookup_qname env ftv with
    | Some (Inr (Sig_tycon (lid, tps, k, _, _, _, _))) 
    | Some (Inr (Sig_typ_abbrev (lid, tps, k, _, _))) -> 
      Util.close_kind tps k
    | _ ->
      raise (Error(Tc.Errors.name_not_found ftv, range_of_lid ftv))

let lookup_operator env (opname:ident) = 
  let primName = lid_of_path ["Prims"; ("_dummy_" ^ opname.idText)] dummyRange in
    lookup_lid env primName
      
let rec push_sigelt env s : env = 
  match s with 
    | Sig_bundle(ses, _) -> List.fold_left push_sigelt env ses 
    | _ -> {env with gamma=Binding_sig s::env.gamma}
        
let push_local_binding env b = {env with gamma=b::env.gamma}
      
let uvars_in_env env = 
  let ext out uvs = 
    {out with uvars_k=uvs.uvars_k@out.uvars_k; 
              uvars_t=uvs.uvars_t@out.uvars_t;
              uvars_e=uvs.uvars_e@out.uvars_e} in
  let rec aux out g = match g with 
    | [] -> out
    | Binding_lid(_, t)::tl
    | Binding_var(_, t)::tl -> aux (ext out (Util.uvars_in_typ t)) tl
    | Binding_typ(_, k)::tl -> aux (ext out (Util.uvars_in_kind k)) tl 
    | Binding_sig _::_ -> out in (* this marks a top-level scope ... no more uvars beyond this *)
  aux empty_uvars env.gamma

let push_module env (m:modul) = 
    add_sigelts env m.exports;
    {env with 
      modules=m::env.modules; 
      gamma=[];
      expected_typ=None}

let set_expected_typ env t = 
  {env with expected_typ = Some t}
let expected_typ env = match env.expected_typ with 
  | None -> None
  | Some t -> Some t
let clear_expected_typ env = {env with expected_typ=None}, expected_typ env

let fold_env env f a = List.fold_right (fun e a -> f a e) env.gamma a

let idents env : (list<btvdef> * list<bvvdef>) = 
  fold_env env (fun (tvs, xvs) b -> match b with 
    | Binding_var(x, _) -> (tvs, x::xvs)
    | Binding_typ(a, _) -> (a::tvs, xvs)
    | _ -> (tvs, xvs)) ([],[])

let lidents env : list<lident> =
  let keys = List.fold_left (fun keys -> function 
    | Binding_sig s -> Util.lids_of_sigelt s@keys
    | _ -> keys) [] env.gamma in
  Util.smap_fold env.sigtab (fun _ v keys -> Util.lids_of_sigelt v@keys) keys  
    
//let quantifier_pattern_env env t = 
//  let vars, _ = Util.collect_forall_xt t in
//  let vars = match vars with 
//    | [] -> fst (Util.collect_exists_xt t)
//    | _ -> vars in
//  List.fold_left (fun env -> function
//    | Inr (x, t) -> push_local_binding env (Binding_var(x, t))
//    | Inl (a, k) -> push_local_binding env (Binding_typ(a, k))) env vars 
