
open Prims
let no_free_vars = {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}

let singleton_bv = (fun x -> (let _129_4 = (let _129_3 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Util.set_add x _129_3))
in {FStar_Syntax_Syntax.free_names = _129_4; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}))

let singleton_uv = (fun x -> (let _129_8 = (let _129_7 = (FStar_Syntax_Syntax.new_uv_set ())
in (FStar_Util.set_add x _129_7))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = _129_8; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}))

let singleton_univ = (fun x -> (let _129_12 = (let _129_11 = (FStar_Syntax_Syntax.new_universe_uvar_set ())
in (FStar_Util.set_add x _129_11))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = _129_12}))

let union = (fun f1 f2 -> (let _129_19 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_names f2.FStar_Syntax_Syntax.free_names)
in (let _129_18 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_uvars f2.FStar_Syntax_Syntax.free_uvars)
in (let _129_17 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_univs f2.FStar_Syntax_Syntax.free_univs)
in {FStar_Syntax_Syntax.free_names = _129_19; FStar_Syntax_Syntax.free_uvars = _129_18; FStar_Syntax_Syntax.free_univs = _129_17}))))

let rec free_univs = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_bvar (_)) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unknown) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(free_univs u)
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_List.fold_left (fun out x -> (let _129_24 = (free_univs x)
in (union out _129_24))) no_free_vars us)
end
| FStar_Syntax_Syntax.U_unif (u) -> begin
if ((FStar_Unionfind.uvar_id u) = 11303) then begin
(FStar_All.failwith "11303!")
end else begin
(singleton_univ u)
end
end))

let rec free_names_and_uvs' = (fun tm -> (let aux_binders = (fun bs acc -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n _38_31 -> (match (_38_31) with
| (x, _38_30) -> begin
(let _129_40 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _129_40))
end)) acc)))
in (let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_38_34) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(singleton_bv x)
end
| FStar_Syntax_Syntax.Tm_uvar (x, t) -> begin
(singleton_uv (x, t))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(free_univs u)
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let f = (free_names_and_uvars t)
in (FStar_List.fold_left (fun out u -> (let _129_46 = (free_univs u)
in (union out _129_46))) f us))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, _38_64) -> begin
(let _129_47 = (free_names_and_uvars t)
in (aux_binders bs _129_47))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _129_48 = (free_names_and_uvars_comp c)
in (aux_binders bs _129_48))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(let _129_49 = (free_names_and_uvars t)
in (aux_binders (((bv, None))::[]) _129_49))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _129_50 = (free_names_and_uvars t)
in (free_names_and_uvars_args args _129_50))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(let _129_59 = (let _129_58 = (free_names_and_uvars t)
in (FStar_List.fold_left (fun n _38_87 -> (match (_38_87) with
| (p, wopt, t) -> begin
(let n1 = (match (wopt) with
| None -> begin
no_free_vars
end
| Some (w) -> begin
(free_names_and_uvars w)
end)
in (let n2 = (free_names_and_uvars t)
in (let n = (let _129_53 = (union n2 n)
in (union n1 _129_53))
in (let _129_57 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _129_57 (FStar_List.fold_left (fun n x -> (let _129_56 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _129_56))) n))))))
end)) _129_58))
in (FStar_All.pipe_right pats _129_59))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, _38_99) -> begin
(let _129_61 = (free_names_and_uvars t1)
in (let _129_60 = (free_names_and_uvars t2)
in (union _129_61 _129_60)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(let _129_68 = (let _129_67 = (free_names_and_uvars t)
in (FStar_List.fold_left (fun n lb -> (let _129_66 = (let _129_65 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp)
in (let _129_64 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef)
in (union _129_65 _129_64)))
in (union n _129_66))) _129_67))
in (FStar_All.pipe_right (Prims.snd lbs) _129_68))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _129_69 = (free_names_and_uvars t)
in (FStar_List.fold_right free_names_and_uvars_args args _129_69))
end
| FStar_Syntax_Syntax.Tm_meta (t, _38_115) -> begin
(free_names_and_uvars t)
end))))
and free_names_and_uvars = (fun t -> (let t = (FStar_Syntax_Subst.compress t)
in (match ((FStar_ST.read t.FStar_Syntax_Syntax.vars)) with
| Some (n) -> begin
if (should_invalidate_cache n) then begin
(let _38_122 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.vars None)
in (free_names_and_uvars t))
end else begin
n
end
end
| _38_125 -> begin
(let n = (free_names_and_uvs' t)
in (let _38_127 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.vars (Some (n)))
in n))
end)))
and free_names_and_uvars_args = (fun args acc -> (FStar_All.pipe_right args (FStar_List.fold_left (fun n _38_135 -> (match (_38_135) with
| (x, _38_134) -> begin
(let _129_75 = (free_names_and_uvars x)
in (union n _129_75))
end)) acc)))
and free_names_and_uvars_binders = (fun bs acc -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n _38_142 -> (match (_38_142) with
| (x, _38_141) -> begin
(let _129_78 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _129_78))
end)) acc)))
and free_names_and_uvars_comp = (fun c -> (match ((FStar_ST.read c.FStar_Syntax_Syntax.vars)) with
| Some (n) -> begin
if (should_invalidate_cache n) then begin
(let _38_146 = (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars None)
in (free_names_and_uvars_comp c))
end else begin
n
end
end
| _38_149 -> begin
(let n = (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (t)) | (FStar_Syntax_Syntax.Total (t)) -> begin
(free_names_and_uvars t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _129_80 = (free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ)
in (free_names_and_uvars_args ct.FStar_Syntax_Syntax.effect_args _129_80))
end)
in (let _38_156 = (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars (Some (n)))
in n))
end))
and should_invalidate_cache = (fun n -> ((let _129_83 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_uvars FStar_Util.set_elements)
in (FStar_All.pipe_right _129_83 (FStar_Util.for_some (fun _38_162 -> (match (_38_162) with
| (u, _38_161) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Fixed (_38_164) -> begin
true
end
| _38_167 -> begin
false
end)
end))))) || (let _129_85 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_univs FStar_Util.set_elements)
in (FStar_All.pipe_right _129_85 (FStar_Util.for_some (fun u -> (match ((FStar_Unionfind.find u)) with
| Some (_38_170) -> begin
true
end
| None -> begin
false
end)))))))

let names = (fun t -> (let _129_88 = (free_names_and_uvars t)
in _129_88.FStar_Syntax_Syntax.free_names))

let uvars = (fun t -> (let _129_91 = (free_names_and_uvars t)
in _129_91.FStar_Syntax_Syntax.free_uvars))

let univs = (fun t -> (let _129_94 = (free_names_and_uvars t)
in _129_94.FStar_Syntax_Syntax.free_univs))

let names_of_binders = (fun bs -> (let _129_97 = (free_names_and_uvars_binders bs no_free_vars)
in _129_97.FStar_Syntax_Syntax.free_names))



