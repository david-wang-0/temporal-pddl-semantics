
section \<open>Executable Temporal PDDL Checker\<close>
theory TEMPORAL_PDDL_Checker
imports
  TEMPORAL_PDDL_Semantics
  Error_Monad_Add
  "HOL.String"
  (*"HOL-Library.Code_Char"     TODO: This might lead to performance loss! CHECK! *)
  "HOL-Library.Code_Target_Nat"
  "HOL-Library.While_Combinator"
  "Containers.Containers"

  "HOL-Library.Tree"
begin

subsection \<open>Generic DFS Reachability Checker\<close>
text \<open>Used for subtype checks\<close>

definition "E_of_succ succ \<equiv> { (u,v). v\<in>set (succ u) }"
lemma succ_as_E: "set (succ x) = E_of_succ succ `` {x}"
  unfolding E_of_succ_def by auto

context
  fixes succ :: "'a \<Rightarrow> 'a list"
begin

  private abbreviation (input) "E \<equiv> E_of_succ succ"


definition "dfs_reachable D w \<equiv>
  let (V,w,brk) = while (\<lambda>(V,w,brk). \<not>brk \<and> w\<noteq>[]) (\<lambda>(V,w,_).
    case w of v#w \<Rightarrow>
    if D v then (V,v#w,True)
    else if v\<in>V then (V,w,False)
    else
      let V = insert v V in
      let w = succ v @ w in
      (V,w,False)
    ) ({},w,False)
  in brk"


context
  fixes w\<^sub>0 :: "'a list"
  assumes finite_dfs_reachable[simp, intro!]: "finite (E\<^sup>* `` set w\<^sub>0)"
begin

  private abbreviation (input) "W\<^sub>0 \<equiv> set w\<^sub>0"

definition "dfs_reachable_invar D V W brk \<longleftrightarrow>
    W\<^sub>0 \<subseteq> W \<union> V
  \<and> W \<union> V \<subseteq> E\<^sup>* `` W\<^sub>0
  \<and> E``V \<subseteq> W \<union> V
  \<and> Collect D \<inter> V = {}
  \<and> (brk \<longrightarrow> Collect D \<inter> E\<^sup>* `` W\<^sub>0 \<noteq> {})"

lemma card_decreases: "
   \<lbrakk>finite V; y \<notin> V; dfs_reachable_invar D V (Set.insert y W) brk \<rbrakk>
   \<Longrightarrow> card (E\<^sup>* `` W\<^sub>0 - Set.insert y V) < card (E\<^sup>* `` W\<^sub>0 - V)"
  apply (rule psubset_card_mono)
  apply (auto simp: dfs_reachable_invar_def)
  done

lemma all_neq_Cons_is_Nil[simp]: (* Odd term remaining in goal \<dots> *)
  "(\<forall>y ys. x2 \<noteq> y # ys) \<longleftrightarrow> x2 = []" by (cases x2) auto

lemma dfs_reachable_correct: "dfs_reachable D w\<^sub>0 \<longleftrightarrow> Collect D \<inter> E\<^sup>* `` set w\<^sub>0 \<noteq> {}"
  unfolding dfs_reachable_def
  apply (rule while_rule[where
    P="\<lambda>(V,w,brk). dfs_reachable_invar D V (set w) brk \<and> finite V"
    and r="measure (\<lambda>V. card (E\<^sup>* `` (set w\<^sub>0) - V)) <*lex*> measure length <*lex*> measure (\<lambda>True\<Rightarrow>0 | False\<Rightarrow>1)"
    ])
  subgoal by (auto simp: dfs_reachable_invar_def)
  subgoal
    apply (auto simp: neq_Nil_conv succ_as_E[of succ] split: if_splits)
    by (auto simp: dfs_reachable_invar_def Image_iff intro: rtrancl.rtrancl_into_rtrancl)
  subgoal by (fastforce simp: dfs_reachable_invar_def dest: Image_closed_trancl)
  subgoal by blast
  subgoal by (auto simp: neq_Nil_conv card_decreases)
  done

end

definition "tab_succ l \<equiv> Mapping.lookup_default [] (fold (\<lambda>(u,v). Mapping.map_default u [] (Cons v)) l Mapping.empty)"


lemma Some_eq_map_option [iff]: "(Some y = map_option f xo) = (\<exists>z. xo = Some z \<and> f z = y)"
  by (auto simp add: map_option_case split: option.split)


lemma tab_succ_correct: "E_of_succ (tab_succ l) = set l"
proof -
  have "set (Mapping.lookup_default [] (fold (\<lambda>(u,v). Mapping.map_default u [] (Cons v)) l m) u) = set l `` {u} \<union> set (Mapping.lookup_default [] m u)"
    for m u
    apply (induction l arbitrary: m)
    by (auto
      simp: Mapping.lookup_default_def Mapping.map_default_def Mapping.default_def
      simp: lookup_map_entry' lookup_update' keys_is_none_rep Option.is_none_def
      split: if_splits
    )
  from this[where m=Mapping.empty] show ?thesis
    by (auto simp: E_of_succ_def tab_succ_def lookup_default_empty)
qed

end

lemma finite_imp_finite_dfs_reachable:
  "\<lbrakk>finite E; finite S\<rbrakk> \<Longrightarrow> finite (E\<^sup>*``S)"
  apply (rule finite_subset[where B="S \<union> (Relation.Domain E \<union> Relation.Range E)"])
  apply (auto simp: intro: finite_Domain finite_Range elim: rtranclE)
  done

lemma dfs_reachable_tab_succ_correct: "dfs_reachable (tab_succ l) D vs\<^sub>0 \<longleftrightarrow> Collect D \<inter> (set l)\<^sup>*``set vs\<^sub>0 \<noteq> {}"
  apply (subst dfs_reachable_correct)
  by (simp_all add: tab_succ_correct finite_imp_finite_dfs_reachable)



subsection \<open>Implementation Refinements\<close>

subsubsection \<open>Of-Type\<close>

definition "of_type_impl G oT T \<equiv> (\<forall>pt\<in>set (primitives oT). dfs_reachable G ((=) pt) (primitives T))"


fun ty_term' where
  "ty_term' varT objT (term.VAR v) = varT v"
| "ty_term' varT objT (term.CONST c) = Mapping.lookup objT c"

lemma ty_term'_correct_aux: "ty_term' varT objT t = ty_term varT (Mapping.lookup objT) t"
  by (cases t) auto

lemma ty_term'_correct[simp]: "ty_term' varT objT = ty_term varT (Mapping.lookup objT)"
  using ty_term'_correct_aux by auto

context ast_domain begin

  definition "of_type1 pt T \<longleftrightarrow> pt \<in> subtype_rel\<^sup>* `` set (primitives T)"

  lemma of_type_refine1: "of_type oT T \<longleftrightarrow> (\<forall>pt\<in>set (primitives oT). of_type1 pt T)"
    unfolding of_type_def of_type1_def by auto

  definition "STG \<equiv> (tab_succ (map subtype_edge (types D)))"

  lemma subtype_rel_impl: "subtype_rel = E_of_succ (tab_succ (map subtype_edge (types D)))"
    by (simp add: tab_succ_correct subtype_rel_def)

  lemma of_type1_impl: "of_type1 pt T \<longleftrightarrow> dfs_reachable (tab_succ (map subtype_edge (types D))) ((=)pt) (primitives T)"
    by (simp add: subtype_rel_impl of_type1_def dfs_reachable_tab_succ_correct tab_succ_correct)

  lemma of_type_impl_correct: "of_type_impl STG oT T \<longleftrightarrow> of_type oT T"
    unfolding of_type1_impl STG_def of_type_impl_def of_type_refine1 ..

  definition mp_constT :: "(object, type) mapping" where
    "mp_constT = Mapping.of_alist (consts D)"

  lemma mp_objT_correct[simp]: "Mapping.lookup mp_constT = constT"
    unfolding mp_constT_def constT_def
    by transfer (simp add: Map_To_Mapping.map_apply_def)


  text \<open>Lifting the subtype-graph through wf-checker\<close>
  context
    fixes ty_ent :: "'ent \<rightharpoonup> type"  \<comment> \<open>Entity's type, None if invalid\<close>
  begin

    definition "is_of_type' stg v T \<longleftrightarrow> (
      case ty_ent v of
        Some vT \<Rightarrow> of_type_impl stg vT T
      | None \<Rightarrow> False)"

    lemma is_of_type'_correct: "is_of_type' STG v T = is_of_type ty_ent v T"
      unfolding is_of_type'_def is_of_type_def of_type_impl_correct ..

    fun wf_pred_atom' where "wf_pred_atom' stg (p,vs) \<longleftrightarrow> 
      (case sig p of
          None \<Rightarrow> False
        | Some Ts \<Rightarrow> list_all2 (is_of_type' stg) vs Ts)"

    lemma wf_pred_atom'_correct: "wf_pred_atom' STG pvs = wf_pred_atom ty_ent pvs"
      by (cases pvs) (auto simp: is_of_type'_correct[abs_def] split:option.split)

    fun wf_func_args' where "wf_func_args' stg (f,args) \<longleftrightarrow> 
      (case func_sig f of
          None \<Rightarrow> False
        | Some Ts \<Rightarrow> list_all2 (is_of_type' stg) args Ts)"

    lemma wf_func_args'_correct: "wf_func_args' STG fargs = wf_func_args ty_ent fargs"
      by (cases fargs) (auto simp: is_of_type'_correct[abs_def] split:option.split)

    fun wf_atom' :: "_ \<Rightarrow> 'ent atom \<Rightarrow> bool" where
      "wf_atom' stg (atom.predAtm p vs) \<longleftrightarrow> wf_pred_atom' stg (p,vs)"
    | "wf_atom' stg (atom.eqAtm a b) = (ty_ent a \<noteq> None \<and> ty_ent b \<noteq> None)"

    lemma wf_atom'_correct: "wf_atom' STG a = wf_atom ty_ent a"
      by (cases a) (auto simp: wf_pred_atom'_correct is_of_type'_correct[abs_def] split: option.splits)

    fun wf_fmla' :: "_ \<Rightarrow> ('ent atom) formula \<Rightarrow> bool" where
      "wf_fmla' stg (Atom a) \<longleftrightarrow> wf_atom' stg a"
    | "wf_fmla' stg \<bottom> \<longleftrightarrow> True"
    | "wf_fmla' stg (\<phi>1 \<^bold>\<and> \<phi>2) \<longleftrightarrow> (wf_fmla' stg \<phi>1 \<and> wf_fmla' stg \<phi>2)"
    | "wf_fmla' stg (\<phi>1 \<^bold>\<or> \<phi>2) \<longleftrightarrow> (wf_fmla' stg \<phi>1 \<and> wf_fmla' stg \<phi>2)"
    | "wf_fmla' stg (\<phi>1 \<^bold>\<rightarrow> \<phi>2) \<longleftrightarrow> (wf_fmla' stg \<phi>1 \<and> wf_fmla' stg \<phi>2)"
    | "wf_fmla' stg (\<^bold>\<not>\<phi>) \<longleftrightarrow> wf_fmla' stg \<phi>"

    lemma wf_fmla'_correct: "wf_fmla' STG \<phi> \<longleftrightarrow> wf_fmla ty_ent \<phi>"
      by (induction \<phi> rule: wf_fmla.induct) (auto simp: wf_atom'_correct)

    fun wf_fmla_atom1' where
      "wf_fmla_atom1' stg (Atom (predAtm p vs)) \<longleftrightarrow> wf_pred_atom' stg (p,vs)"
    | "wf_fmla_atom1' stg _ \<longleftrightarrow> False"

    lemma wf_fmla_atom1'_correct: "wf_fmla_atom1' STG \<phi> = wf_fmla_atom ty_ent \<phi>"
      by (cases \<phi> rule: wf_fmla_atom.cases) (auto
        simp: wf_atom'_correct is_of_type'_correct[abs_def] split: option.splits)

    fun wf_effect' where
      "wf_effect' stg (Effect a d) \<longleftrightarrow>
          (\<forall>ae\<in>set a. wf_fmla_atom1' stg ae)
        \<and> (\<forall>de\<in>set d.  wf_fmla_atom1' stg de)"

    lemma wf_effect'_correct: "wf_effect' STG e = wf_effect ty_ent e"
      by (cases e) (auto simp: wf_fmla_atom1'_correct)

    fun wf_duration_const' :: "_ \<Rightarrow> 'ent duration_constraint \<Rightarrow> bool" where
      "wf_duration_const' stg No_Const \<longleftrightarrow> True"
    | "wf_duration_const' stg (Time_Const op d) \<longleftrightarrow> d \<ge> 0"
    | "wf_duration_const' stg (Func_Const op f vs) \<longleftrightarrow> 
        (case func_sig f of
            None \<Rightarrow> False
          | Some Ts \<Rightarrow> list_all2 (is_of_type' stg) vs Ts)"

    lemma wf_duration_const'_correct: "wf_duration_const' STG d = wf_duration_const ty_ent d"
      by (cases d) (auto simp: is_of_type'_correct[abs_def] split:option.split)

    definition "wf_duration_consts' stg = list_all (wf_duration_const' stg)" 
  
    lemma wf_duration_consts'_correct: "wf_duration_consts' STG ds = wf_duration_consts ty_ent ds"
      unfolding wf_duration_consts'_def wf_duration_consts_def using wf_duration_const'_correct by presburger
  end \<comment> \<open>Context fixing \<open>ty_ent\<close>\<close>

  fun wf_action_schema' :: "_ \<Rightarrow> _ \<Rightarrow> ast_action_schema \<Rightarrow> bool" where
    "wf_action_schema' stg conT (Simple_Action_Schema n params pre eff) \<longleftrightarrow> (
      let
        tyv = ty_term' (map_of params) conT
      in
        distinct (map fst params)
      \<and> wf_fmla' tyv stg pre
      \<and> wf_effect' tyv stg eff)"
  | "wf_action_schema' stg conT (Durative_Action_Schema n params d cond eff) \<longleftrightarrow> (
      let
        tyv = ty_term' (map_of params) conT
      in
        distinct (map fst params)
      \<and> (\<forall>(t,c) \<in> set cond. wf_fmla' tyv stg c)
      \<and> (\<forall>(t,e) \<in> set eff. wf_effect' tyv stg e \<and> t \<noteq> Over_All)
      \<and> wf_duration_consts' tyv stg d)"

  lemma wf_action_schema'_correct: "wf_action_schema' STG mp_constT s = wf_action_schema s"
    by (cases s) 
       (auto simp: wf_fmla'_correct wf_effect'_correct wf_duration_consts'_correct Let_def 
             split: option.splits)

  definition wf_domain' :: "_ \<Rightarrow> _ \<Rightarrow> bool" where
    "wf_domain' stg conT \<equiv>
      wf_types
    \<and> distinct (map (predicate_decl.pred) (predicates D))
    \<and> (\<forall>p\<in>set (predicates D). wf_predicate_decl p)
    \<and> distinct (map (function_decl.func) (functions D))
    \<and> (\<forall>f\<in>set (functions D). wf_function_decl f)
    \<and> distinct (map fst (consts D))
    \<and> (\<forall>(n,T)\<in>set (consts D). wf_type T)
    \<and> distinct (map ast_action_schema.name (actions D))
    \<and> (\<forall>a\<in>set (actions D). wf_action_schema' stg conT a)
    "

  lemma wf_domain'_correct: "wf_domain' STG mp_constT = wf_domain"
    unfolding wf_domain_def wf_domain'_def
    by (auto simp: wf_action_schema'_correct)


end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

subsubsection \<open>Ground Action Interference \& Application of Effects\<close>

context ast_problem begin

  text \<open>Implementation of executable refinements for @{const acts_non_intrf} 
  \& @{const apply_happ}\<close>

  (*lemma intersect_filter: "xs \<inter> (set ys) = {} \<longleftrightarrow> filter (\<lambda>x. x \<in> xs) ys = []"
    by (induction ys arbitrary: xs) auto

  lemma intersect_union_filter: "xs \<inter> (set ys \<union> set zs) = {} \<longleftrightarrow> filter (\<lambda>x. x \<in> xs) (ys @ zs) = []"
    by (induction ys arbitrary: xs zs) (auto simp: intersect_filter)

  definition acts_non_intrf_exec :: "ground_action \<Rightarrow> ground_action \<Rightarrow> bool" where
    "acts_non_intrf_exec a b \<longleftrightarrow> (
      let 
        Add\<^sub>a = (adds o effect) a; Del\<^sub>a = (dels o effect) a; GPre\<^sub>a = Atom ` atoms (precondition a);
        Add\<^sub>b = (adds o effect) b; Del\<^sub>b = (dels o effect) b; GPre\<^sub>b = Atom ` atoms (precondition b) in
        filter (\<lambda>x. x \<in> GPre\<^sub>a) (Add\<^sub>b @ Del\<^sub>b) = [] \<and>
        filter (\<lambda>x. x \<in> GPre\<^sub>b) (Add\<^sub>a @ Del\<^sub>a) = [] \<and>
        filter (\<lambda>x. x \<in> set Add\<^sub>a) Del\<^sub>b = [] \<and>
        filter (\<lambda>x. x \<in> set Add\<^sub>b) Del\<^sub>a = [])"

  text \<open>Justification of refinement for @{const acts_non_intrf}\<close>
  lemma acts_non_intrf_refine: 
    "acts_non_intrf a b \<longleftrightarrow> acts_non_intrf_exec a b"
    unfolding acts_non_intrf_def acts_non_intrf_exec_def Let_def
    by (auto simp: intersect_filter intersect_union_filter)*)

  text \<open>a list of simulataneous \& non-interfering grounded actions are all applied at once\<close>
  fun apply_happ_exec :: "happening \<Rightarrow> world_model \<Rightarrow> world_model" where
    "apply_happ_exec (t\<^sub>i,A\<^sub>i) s = 
      (let 
        adds = (concat o (map (adds o effect))) A\<^sub>i; 
        dels = (concat o (map (dels o effect))) A\<^sub>i in 
        fold Set.insert adds (fold Set.remove dels s))"

  lemma fold_set_remove: "fold Set.remove xs s = s - set xs"
    by (induction xs arbitrary: s) auto

  lemma fold_set_insert: "fold Set.insert xs s = s \<union> set xs"
    by (induction xs arbitrary: s) auto

  text \<open>Justification of refinement for @{const apply_happ}\<close>
  lemma apply_happ_exec_refine: "apply_happ_exec h s = apply_happ h s"
    by (cases h) (auto simp: fold_set_remove fold_set_insert)

end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>

subsubsection \<open>Well-Formedness\<close>

context ast_problem begin

  text \<open> We start by defining a mapping from objects to types. The container
    framework will generate efficient, red-black tree based code for that
    later. \<close>

  type_synonym objT = "(object, type) mapping"

  definition mp_objT :: "(object, type) mapping" where
    "mp_objT = Mapping.of_alist (consts D @ objects P)"

  lemma mp_objT_correct[simp]: "Mapping.lookup mp_objT = objT"
    unfolding mp_objT_def objT_alt
    by transfer (simp add: Map_To_Mapping.map_apply_def)

  text \<open>We refine the typecheck to use the mapping\<close>

  definition "is_obj_of_type_impl stg mp n T = (
    case Mapping.lookup mp n of None \<Rightarrow> False | Some oT \<Rightarrow> of_type_impl stg oT T
  )"

  lemma is_obj_of_type_impl_correct[simp]:
    "is_obj_of_type_impl STG mp_objT = is_obj_of_type"
    apply (intro ext)
    apply (auto simp: is_obj_of_type_impl_def is_obj_of_type_def of_type_impl_correct split: option.split)
    done

  fun wf_func_assign' :: "objT \<Rightarrow> _ \<Rightarrow> object atom formula \<Rightarrow> bool" where 
    "wf_func_assign' ot stg (Atom (eqAtm (FuncEnt f args) (TimeEnt d))) 
      \<longleftrightarrow> wf_func_args' (Mapping.lookup ot) stg (f,args)"
  | "wf_func_assign' ot stg _ \<longleftrightarrow> False"

  lemma wf_func_asign'_correct[simp]: "wf_func_assign' mp_objT STG f = wf_func_assign f"
    by (cases f rule: wf_func_assign.cases) (auto simp: wf_func_args'_correct[abs_def])

  text \<open>We refine the well-formedness checks to use the mapping\<close>

  definition wf_fact' :: "objT \<Rightarrow> _ \<Rightarrow> fact \<Rightarrow> bool" where
    "wf_fact' ot stg \<equiv> wf_pred_atom' (Mapping.lookup ot) stg"

  lemma wf_fact'_correct[simp]: "wf_fact' mp_objT STG = wf_fact"
    by (auto simp: wf_fact'_def wf_fact_def wf_pred_atom'_correct[abs_def])


  definition "wf_fmla_atom2' mp stg f
    = (case f of formula.Atom (predAtm p vs) \<Rightarrow> (wf_fact' mp stg (p,vs)) | _ \<Rightarrow> False)"

  lemma wf_fmla_atom2'_correct[simp]:
    "wf_fmla_atom2' mp_objT STG \<phi> = wf_fmla_atom objT \<phi>"
    apply (cases \<phi> rule: wf_fmla_atom.cases)
    by (auto simp: wf_fmla_atom2'_def wf_fact_def split: option.splits)

  definition "wf_problem' stg conT mp \<equiv>
      wf_domain' stg conT
    \<and> distinct (map fst (objects P) @ map fst (consts D))
    \<and> (\<forall>(n,T)\<in>set (objects P). wf_type T)
    \<and> distinct (init P)
    \<and> (\<forall>f\<in>set (init P). wf_fmla_atom2' mp stg f \<or> wf_func_assign' mp stg f)
    \<and> wf_fmla' (Mapping.lookup mp) stg (goal P)"

  lemma wf_problem'_correct:
    "wf_problem' STG mp_constT mp_objT = wf_problem"
    unfolding wf_problem_def wf_problem'_def wf_world_model_def
    by (auto simp: wf_domain'_correct wf_fmla'_correct)

  text \<open>Instantiating actions will yield well-founded effects.
    Corollary of @{thm wf_inst_action_schema} 
             and @{thm wf_inst_durative_action_schema}.\<close>

  lemma wf_effect_inst_weak:
    fixes n params pre eff
    defines "a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a \<equiv> Simple_Action_Schema n params pre eff"  
    assumes "a = instantiate_action_schema a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a args ta" 
        and "action_params_match a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a args" 
        and "wf_action_schema a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a"
    shows "wf_effect_inst (effect a)"
    using assms wf_inst_action_schema
    by (cases a) (auto simp: wf_effect_inst_alt Let_def)

  lemma wf_effect_durative_inst_weak:
    fixes n params d cond eff
    defines "a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a \<equiv> Durative_Action_Schema n params d cond eff"  
    assumes "a = inst_snap_action a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a args ta" 
        and "action_params_match a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a args" 
        and "wf_action_schema a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a"
    shows "wf_effect_inst (effect a)"
    using assms wf_inst_durative_action_schema
    by (cases a) (auto simp: wf_effect_inst_alt Let_def)

end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>


subsubsection \<open>Happening Execution\<close>

context ast_domain begin

  text \<open>We first lift action schema lookup into the error monad.\<close>
  definition "resolve_action_schemaE n \<equiv>
    lift_opt
      (resolve_action_schema n)
      (ERR (shows ''No such action schema '' o shows n))"

  lemma resolve_action_schemaE_return_iff[return_iff]: 
    "(resolve_action_schemaE n = Inr a) \<longleftrightarrow> (resolve_action_schema n = Some a)"
    using resolve_action_schemaE_def by (simp add: lift_opt_return_iff)

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

context ast_problem begin

  text \<open>We define a function to determine whether a formula holds in
    a world model\<close>
  definition "holds M F \<equiv> (valuation M) \<Turnstile> F"

  text \<open>Justification of this function\<close>

  lemma holds_for_wf_fmlas:
    assumes "wm_basic s"
    shows "holds s F \<longleftrightarrow> close_world s \<TTurnstile> F"
    unfolding holds_def using assms valuation_iff_close_world by blast  

  text \<open>The first refinement summarizes the enabledness check and the 
    application of a happening. Moreover, we implement the precondition 
    evaluation by our @{const holds} function. This way, we can eliminate 
    redundant resolving and instantiation of the action.
  \<close>
  definition en_exE :: "happening \<Rightarrow> world_model \<Rightarrow> _+world_model" where
    "en_exE \<equiv> \<lambda>(t\<^sub>i,A\<^sub>i) \<Rightarrow> \<lambda>s. do {
      check_allm (\<lambda>a. check (holds s (precondition a)) (ERRS ''Precondition not satisfied'')) A\<^sub>i;
      check_pairwise (\<lambda>a b. check (a \<noteq> b \<longrightarrow> acts_non_intrf a b) (ERRS ''Actions in happening interfering'')) A\<^sub>i;
      Error_Monad.return (apply_happ_exec (t\<^sub>i,A\<^sub>i) s)
    }"

  lemma symmetric_pred_check_pairwise:
    assumes "\<forall>x\<^sub>1 x\<^sub>2. A x\<^sub>1 x\<^sub>2 \<longleftrightarrow> A x\<^sub>2 x\<^sub>1" 
        and "isOK (check_pairwise (\<lambda>x\<^sub>1 x\<^sub>2. check (x\<^sub>1 \<noteq> x\<^sub>2 \<longrightarrow> A x\<^sub>1 x\<^sub>2) e) as)" 
    shows "\<forall>x\<^sub>1 \<in> set as.\<forall>x\<^sub>2 \<in> set as. x\<^sub>1 \<noteq> x\<^sub>2 \<longrightarrow> A x\<^sub>1 x\<^sub>2"
    using assms by (auto simp: return_iff) (smt in_set_conv_nth linorder_neqE_nat)

  text \<open>Justification of implementation.\<close>
  lemma (in wf_ast_problem) en_exE_return_iff:
    assumes "wm_basic s"
        and "\<forall>a \<in> set A\<^sub>i. wf_ground_action a"
    shows "en_exE (t\<^sub>i,A\<^sub>i) s = Inr s' \<longleftrightarrow> happ_enabled (t\<^sub>i,A\<^sub>i) s \<and> s' = apply_happ (t\<^sub>i,A\<^sub>i) s"
    unfolding en_exE_def
    using assms holds_for_wf_fmlas[OF \<open>wm_basic s\<close>] (*acts_non_intrf_refine*) 
          symmetric_pred_check_pairwise[OF acts_non_intrf_symmetric]
          apply_happ_exec_refine
    by auto

  text \<open>Next, we use the efficient implementation @{const is_obj_of_type_impl}
    for the type check, and omit the well-formedness check, as effects obtained
    from instantiating well-formed action schemas are always well-formed
    (@{thm [source] wf_effect_inst_weak}).\<close>
  abbreviation "action_params_match2 stg mp a args
    \<equiv> list_all2 (is_obj_of_type_impl stg mp)
        args (map snd (ast_action_schema.parameters a))"

end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>

subsubsection \<open>Construction of Induced Happening Sequence\<close>

context ast_problem begin

  text \<open>implemented own version of @{const insort_insert}, because @{const insort_insert} 
  requiers sort type; rat is not of sort type\<close> 
  fun insort_htp :: "time \<Rightarrow> time list \<Rightarrow> time list" where
    "insort_htp x [] = [x]"
  | "insort_htp x (y#ys) = 
      (if x < y then x#y#ys
      else if x = y then y#ys
      else y # (insort_htp x ys))"

  text \<open>Basic properties text of @{const insort_htp}: 
    preserves sorted-ness \& distinct-ness, inserts element\<close>

  lemma insort_htps_insort_insert: "sorted xs \<Longrightarrow> insort_htp x xs = insort_insert x xs"
    by (induction x xs rule: insort_htp.induct) (auto simp: insort_insert_key_def)

  lemma sorted_insort_htps: "sorted xs \<Longrightarrow> sorted (insort_htp x xs)"
    using insort_htps_insort_insert sorted_insort_insert by auto

  lemma set_insort_htps: "set (insort_htp x xs) = insert x (set xs)"
    by (induction x xs rule: insort_htp.induct) auto

  lemma distinct_insort_htps: "sorted xs \<Longrightarrow> distinct xs \<Longrightarrow> distinct (insort_htp x xs)"
    using set_insort_htps by (induction x xs rule: insort_htp.induct) auto

  lemma insort_htps_non_Nil: "insort_htp x xs \<noteq> []"
    by (induction x xs rule: insort_htp.induct) auto

  text \<open>Implementation of executable refinement for happening time points. Produces a 
  strictly sorted sequence of all @{const is_htp}\<close>
  fun htps_exec :: "plan \<Rightarrow> time list" where
    "htps_exec [] = []" 
  | "htps_exec ((t\<^sub>\<pi>,Simple_Plan_Action n args)#\<pi>s) = 
      insort_htp t\<^sub>\<pi> (htps_exec \<pi>s)"
  | "htps_exec ((t\<^sub>\<pi>,Durative_Plan_Action n args d)#\<pi>s) = 
      insort_htp t\<^sub>\<pi> (insort_htp (t\<^sub>\<pi>+d) (htps_exec \<pi>s))"

  text \<open>Basic properties of @{const htps_exec}\<close>

  lemma htps_exec_Nil: "htps_exec \<pi>s = [] \<longleftrightarrow> \<pi>s = []"
    by (induction \<pi>s rule: htps_exec.induct) (auto simp: insort_htps_non_Nil split: if_splits)

  lemma htps_exec_sorted: "sorted (htps_exec \<pi>s)"
    using sorted_insort_htps by (induction \<pi>s rule: htps_exec.induct) auto

  lemma htps_exec_distinct: "distinct (htps_exec \<pi>s)"
    using htps_exec_sorted distinct_insort_htps sorted_insort_htps
    by (induction \<pi>s rule: htps_exec.induct) auto

  text \<open>Correctness proof for @{const htps_exec}\<close>

  text \<open>Every time point in @{const htps_exec} is a happening time point.\<close>
  lemma htps_exec_is_htps: "t\<^sub>i \<in> set (htps_exec \<pi>s) \<Longrightarrow> is_htp \<pi>s t\<^sub>i"
  proof (induction \<pi>s)
    case Nil
    then show ?case by simp
  next
    case (Cons \<pi> \<pi>s)
    obtain t\<^sub>\<pi> \<pi>' where "\<pi> = (t\<^sub>\<pi>,\<pi>')"
      by (meson surj_pair)
    then show ?case
      using \<open>\<pi> = (t\<^sub>\<pi>,\<pi>')\<close> set_insort_htps  Cons.IH Cons.prems
      by (cases \<pi>') (auto simp: is_htp_def durative_acts_def is_act_simple_def)
  qed

  lemma htps_exec_Cons_subset: "set (htps_exec \<pi>s) \<subseteq> set (htps_exec (\<pi> # \<pi>s))"
    by (induction "\<pi> # \<pi>s" rule: htps_exec.induct) (auto simp: set_insort_htps)

  lemma htps_exec_app_subset: "set (htps_exec \<pi>s\<^sub>2) \<subseteq> set (htps_exec (\<pi>s\<^sub>1 @ \<pi>s\<^sub>2))"
    using htps_exec_Cons_subset
    by (induction \<pi>s\<^sub>1 arbitrary: \<pi>s\<^sub>2 rule: htps_exec.induct) (auto simp: set_insort_htps)

  text \<open>Every happening time point is included in @{const htps_exec}.\<close>
  lemma is_htps_htps_exec: "is_htp \<pi>s t\<^sub>i \<Longrightarrow> t\<^sub>i \<in> set (htps_exec \<pi>s)"
  proof (induction \<pi>s)
    case Nil
    then show ?case 
      unfolding is_htp_def durative_acts_def is_act_simple_def by simp
  next
    case (Cons \<pi> \<pi>s)
    have "(\<exists>\<pi>'. (t\<^sub>i,\<pi>') \<in> set (\<pi>#\<pi>s)) \<or> (\<exists>(t\<^sub>\<pi>,\<pi>') \<in> durative_acts (\<pi>#\<pi>s). t\<^sub>i = t\<^sub>\<pi> + (duration \<pi>'))"
      using Cons.prems unfolding is_htp_def by simp
    then show ?case
    proof
      assume "\<exists>\<pi>'. (t\<^sub>i,\<pi>') \<in> set (\<pi>#\<pi>s)"
      then obtain \<pi>' where "(t\<^sub>i,\<pi>') \<in> set (\<pi>#\<pi>s)"
        by auto
      then obtain \<pi>s\<^sub>1 \<pi>s\<^sub>2 where "(\<pi>#\<pi>s) = \<pi>s\<^sub>1 @ ((t\<^sub>i,\<pi>')#\<pi>s\<^sub>2)"
        by (meson split_list)
      then have "t\<^sub>i \<in> set (htps_exec ((t\<^sub>i,\<pi>')#\<pi>s\<^sub>2))"
        using set_insort_htps by (cases \<pi>') auto
      then show ?case
        using \<open>(\<pi>#\<pi>s) = \<pi>s\<^sub>1 @ ((t\<^sub>i,\<pi>')#\<pi>s\<^sub>2)\<close> htps_exec_app_subset by auto
    next
      assume "\<exists>(t\<^sub>\<pi>,\<pi>') \<in> durative_acts (\<pi>#\<pi>s). t\<^sub>i = t\<^sub>\<pi> + (duration \<pi>')"
      then obtain t\<^sub>\<pi> \<pi>' where "(t\<^sub>\<pi>,\<pi>') \<in> durative_acts (\<pi>#\<pi>s) \<and> t\<^sub>i = t\<^sub>\<pi> + (duration \<pi>')"
        by auto
      then obtain \<pi>s\<^sub>1 \<pi>s\<^sub>2 where "(\<pi>#\<pi>s) = \<pi>s\<^sub>1 @ ((t\<^sub>\<pi>,\<pi>')#\<pi>s\<^sub>2)"
        using dur_acts_subset by (meson split_list subsetD)
      then have "t\<^sub>i \<in> set (htps_exec ((t\<^sub>\<pi>,\<pi>')#\<pi>s\<^sub>2))"
        using set_insort_htps \<open>(t\<^sub>\<pi>,\<pi>') \<in> durative_acts (\<pi>#\<pi>s) \<and> t\<^sub>i = t\<^sub>\<pi> + (duration \<pi>')\<close>
        unfolding durative_acts_def is_act_simple_def by (cases \<pi>') auto
      then show ?case
        using \<open>(\<pi>#\<pi>s) = \<pi>s\<^sub>1 @ ((t\<^sub>\<pi>,\<pi>')#\<pi>s\<^sub>2)\<close> htps_exec_app_subset by auto
    qed
  qed

  lemma is_htp_iff_htps_exec: "\<forall>t. is_htp \<pi>s t \<longleftrightarrow> t \<in> set (htps_exec \<pi>s)"
    using htps_exec_is_htps is_htps_htps_exec by blast

  definition consec_htps_in_interval :: "time list \<Rightarrow> time \<Rightarrow> time \<Rightarrow> (time \<times> time) list" where 
    "consec_htps_in_interval htps t\<^sub>i t\<^sub>j = 
      filter (\<lambda>(t,t'). t\<^sub>i \<le> t \<and> t' \<le> t\<^sub>j) (zip (butlast htps) (tl htps))"

  text \<open>Construct all ground actions for a given plan action\<close>
  fun simplify_action :: "time list \<Rightarrow> (time \<times> plan_action) \<Rightarrow> (time \<times> ground_action) list" where
    "simplify_action htps (t,Simple_Plan_Action n args) = (
      let a = the (resolve_action_schema n) in
        [(t, instantiate_action_schema a args At_Start)]
      )"
  | "simplify_action htps (t,Durative_Plan_Action n args d) = (
      let a = the (resolve_action_schema n) in
        (t,inst_snap_action a args At_Start) # 
        (t+d,inst_snap_action a args At_End) # 
        (map (\<lambda>(t\<^sub>i,t\<^sub>j).((t\<^sub>i+t\<^sub>j) / 2,inst_snap_action a args Over_All)) (consec_htps_in_interval htps t (t+d)))
      )"

  text \<open>Auxiliary lemmas to prove properties about 'zip (butlast xs) (tl xs)', 
  which are needed to ultimatly prove properties about @{const consec_htps}.\<close>

  lemma zip_butlast_tl_hd: 
    assumes "distinct (x\<^sub>1 # xs)" 
        and "(x\<^sub>1, x\<^sub>2) \<in> set (zip (butlast (x\<^sub>1 # xs)) (tl (x\<^sub>1 # xs)))" 
    shows "xs \<noteq> [] \<and> x\<^sub>2 = hd xs"
    using assms
    apply (induction xs)
    apply (auto split: if_splits)
    apply (meson in_set_butlastD in_set_zipE set_ConsD)
    done (* TODO: clean up proof! *)

  lemma zip_butlast_sublist:
    assumes "distinct (xs\<^sub>1 @ x\<^sub>1 # xs\<^sub>2)"
        and "(x\<^sub>1, x\<^sub>2) \<in> set (zip (butlast (xs\<^sub>1 @ x\<^sub>1 # xs\<^sub>2)) (tl (xs\<^sub>1 @ x\<^sub>1 # xs\<^sub>2)))"
    shows "(x\<^sub>1, x\<^sub>2) \<in> set (zip (butlast (x\<^sub>1 # xs\<^sub>2)) (tl (x\<^sub>1 # xs\<^sub>2)))"
    using assms
    apply (induction xs\<^sub>1)
    apply (auto split: if_splits)
    using set_zip_leftD apply fastforce
    apply (smt append_is_Nil_conv list.collapse list.discI old.prod.inject set_ConsD set_zip_leftD zip_Cons_Cons)
    done (* TODO: clean up proof! *)

  lemma zip_butlast_tl_app1: 
    assumes "distinct xs" 
        and "(x\<^sub>1, x\<^sub>2) \<in> set (zip (butlast xs) (tl xs))" 
    shows "\<exists>xs\<^sub>1 xs\<^sub>2. xs = xs\<^sub>1 @ x\<^sub>1 # x\<^sub>2 # xs\<^sub>2"
    using assms
  proof (induction xs)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x xs)
    have "x\<^sub>1 \<in> set (x # xs)"
      by (meson Cons.prems in_set_butlastD set_zip_leftD)
    then obtain xs\<^sub>1 xs\<^sub>2 where "x # xs = xs\<^sub>1 @ x\<^sub>1 # xs\<^sub>2"
      by (meson split_list)
    then have "distinct (xs\<^sub>1 @ x\<^sub>1 # xs\<^sub>2)"
      using Cons.prems by auto
    then have "distinct (x\<^sub>1#xs\<^sub>2)"
      using Cons.prems by auto
    have "(x\<^sub>1, x\<^sub>2) \<in> set (zip (butlast (xs\<^sub>1 @ x\<^sub>1 # xs\<^sub>2)) (tl (xs\<^sub>1 @ x\<^sub>1 # xs\<^sub>2)))"
      using \<open>x # xs = xs\<^sub>1 @ x\<^sub>1 # xs\<^sub>2\<close> Cons.prems by auto
    then have "(x\<^sub>1, x\<^sub>2) \<in> set (zip (butlast (x\<^sub>1 # xs\<^sub>2)) (tl (x\<^sub>1 # xs\<^sub>2)))"
      using zip_butlast_sublist[OF \<open>distinct (xs\<^sub>1 @ (x\<^sub>1 # xs\<^sub>2))\<close>] by auto
    obtain xs\<^sub>2' where "xs\<^sub>2 = x\<^sub>2 # xs\<^sub>2'"
      using zip_butlast_tl_hd[OF \<open>distinct (x\<^sub>1 # xs\<^sub>2)\<close> 
                                 \<open>(x\<^sub>1, x\<^sub>2) \<in> set (zip (butlast (x\<^sub>1 # xs\<^sub>2)) (tl (x\<^sub>1 # xs\<^sub>2)))\<close>]
            list.exhaust_sel by blast
    then show ?case
      using \<open>x # xs = xs\<^sub>1 @ x\<^sub>1 # xs\<^sub>2\<close>
      by auto
  qed

  lemma zip_butlast_tl_app2: 
    "(x\<^sub>1, x\<^sub>2) \<in> set (zip (butlast (xs\<^sub>1 @ x\<^sub>1 # x\<^sub>2 # xs\<^sub>2)) (tl (xs\<^sub>1 @ x\<^sub>1 # x\<^sub>2 # xs\<^sub>2)))" 
  proof -
    let ?xs="xs\<^sub>1 @ x\<^sub>1 # x\<^sub>2 # xs\<^sub>2"
    let ?butlast="butlast ?xs"
    let ?tl="tl ?xs"
    have "x\<^sub>1 = ?xs ! (length xs\<^sub>1)" and "(length xs\<^sub>1) < length ?butlast"
      using nth_append_length by auto
    then have "x\<^sub>1 = ?butlast ! (length xs\<^sub>1)"
      using nth_butlast by fastforce
    have "x\<^sub>2 = ?xs ! (length xs\<^sub>1 + 1)" and "?xs \<noteq> []"
      using nth_append_length[where xs="xs\<^sub>1 @ [x\<^sub>1]"] by auto
    then have "x\<^sub>2 = ?tl ! (length xs\<^sub>1)"
      using nth_tl[OF \<open>?xs \<noteq> []\<close>] by auto
    have "(length xs\<^sub>1) < length ?butlast" and "(length xs\<^sub>1) < length ?tl"
      by auto
    then show ?thesis
      using \<open>x\<^sub>1 = ?butlast ! (length xs\<^sub>1)\<close> \<open>x\<^sub>2 = ?tl ! (length xs\<^sub>1)\<close> in_set_zip
      by (metis fst_conv snd_conv)
  qed

  lemma zip_butlast_tl_app: 
    assumes "distinct xs" 
    shows "(x\<^sub>1, x\<^sub>2) \<in> set (zip (butlast xs) (tl xs)) \<longleftrightarrow> (\<exists>xs\<^sub>1 xs\<^sub>2. xs = xs\<^sub>1 @ x\<^sub>1 # x\<^sub>2 # xs\<^sub>2)"
    using zip_butlast_tl_app1[OF \<open>distinct xs\<close>] zip_butlast_tl_app2 by fastforce

  lemma sorted_distinct_zip_le: 
    assumes "strict_sorted xs" 
        and "(x\<^sub>1, x\<^sub>2) \<in> set (zip (butlast xs) (tl xs))"
    shows "x\<^sub>1 < x\<^sub>2"
    using assms
  proof (induction xs)
    case Nil
    then show ?case 
      by simp
  next
    case (Cons x xs)
    obtain xs\<^sub>1 xs\<^sub>2 where "x # xs = xs\<^sub>1 @ (x\<^sub>1 # x\<^sub>2 # xs\<^sub>2)"
      by (meson Cons.prems zip_butlast_tl_app strict_sorted_iff)
    then show ?case
      using Cons.prems by (auto simp: sorted_append strict_sorted_iff)
  qed

  lemma strict_sorted_zip_butlast_tl_leq_or_geq:
    assumes "strict_sorted xs"
        and "(x\<^sub>1,x\<^sub>2) \<in> set (zip (butlast xs) (tl xs))" 
        and "x \<in> set xs"
    shows "x \<le> x\<^sub>1 \<or> x\<^sub>2 \<le> x"
  proof -
    have "distinct xs"
      using \<open>strict_sorted xs\<close> by (auto simp: strict_sorted_iff)
    then obtain xs\<^sub>1 xs\<^sub>2 where "xs = xs\<^sub>1 @ x\<^sub>1 # x\<^sub>2 # xs\<^sub>2"
      using assms zip_butlast_tl_app[OF \<open>distinct xs\<close>] by auto
    then have "x \<in> set xs\<^sub>1 \<or> x = x\<^sub>1 \<or> x = x\<^sub>2 \<or> x \<in> set xs\<^sub>2"
      using assms by auto
    then show ?thesis
    proof (elim disjE)
      assume "x \<in> set xs\<^sub>1"
      then show ?thesis
        using assms \<open>xs = xs\<^sub>1 @ x\<^sub>1 # x\<^sub>2 # xs\<^sub>2\<close>
        by (auto simp: sorted_wrt_append)
    next
      assume "x = x\<^sub>1"
      then show ?thesis
        by auto
    next
      assume " x = x\<^sub>2"
      then show ?thesis
        by auto
    next
      assume "x \<in> set xs\<^sub>2"
      then show ?thesis
        using assms \<open>xs = xs\<^sub>1 @ x\<^sub>1 # x\<^sub>2 # xs\<^sub>2\<close>
        by (auto simp: sorted_wrt_append)
    qed
  qed

  lemma consec_htps_in_zip_butlast_tl:
    assumes "htps = htps_exec \<pi>s"
        and "consec_htps \<pi>s t\<^sub>i t\<^sub>j"
      shows "(t\<^sub>i,t\<^sub>j) \<in> set (zip (butlast htps) (tl htps))"
  proof -
    have "strict_sorted htps"
      using assms htps_exec_sorted htps_exec_distinct by (simp add: strict_sorted_iff)
    have "\<forall>t \<in> set htps. t \<le> t\<^sub>i \<or> t\<^sub>j \<le> t" and "t\<^sub>i \<in> set htps" and "t\<^sub>j \<in> set htps" and "t\<^sub>i < t\<^sub>j"
      using assms is_htp_iff_htps_exec unfolding consec_htps_def by auto
    then obtain htps\<^sub>1 htps\<^sub>2' where "htps = htps\<^sub>1 @ t\<^sub>i # htps\<^sub>2'"
      by (meson split_list)
    then have "t\<^sub>j \<in> set htps\<^sub>2'"
      using \<open>strict_sorted htps\<close> \<open>t\<^sub>j \<in> set htps\<close> \<open>t\<^sub>i < t\<^sub>j\<close>
      by (auto simp: sorted_wrt_append)
    then obtain htps\<^sub>2 htps\<^sub>3 where "htps\<^sub>2' = htps\<^sub>2 @ t\<^sub>j # htps\<^sub>3"
      by (meson split_list)
    then have "\<forall>t \<in> set htps\<^sub>2. t \<le> t\<^sub>i \<or> t\<^sub>j \<le> t"
      using \<open>\<forall>t \<in> set htps. t \<le> t\<^sub>i \<or> t\<^sub>j \<le> t\<close> \<open>htps = htps\<^sub>1 @ t\<^sub>i # htps\<^sub>2'\<close> by auto
    then have "htps\<^sub>2 = []"
      using \<open>strict_sorted htps\<close> \<open>htps = htps\<^sub>1 @ t\<^sub>i # htps\<^sub>2'\<close> \<open>htps\<^sub>2' = htps\<^sub>2 @ t\<^sub>j # htps\<^sub>3\<close>
      by (induction htps\<^sub>2) (auto simp: sorted_wrt_append)
    then show ?thesis
      using \<open>htps = htps\<^sub>1 @ t\<^sub>i # htps\<^sub>2'\<close> \<open>htps\<^sub>2' = htps\<^sub>2 @ t\<^sub>j # htps\<^sub>3\<close>
      by (auto simp: zip_butlast_tl_app2)
  qed

  text \<open>Executable refinement for @{const consec_htps}.\<close>
  lemma happ_time_pts_exec_iff_consec_htps:
    "(t\<^sub>i,t\<^sub>j) \<in> set (zip (butlast (htps_exec \<pi>s)) (tl (htps_exec \<pi>s))) \<longleftrightarrow> consec_htps \<pi>s t\<^sub>i t\<^sub>j"
  proof -
    have "strict_sorted (htps_exec \<pi>s)"
      using htps_exec_sorted htps_exec_distinct by (simp add: strict_sorted_iff)
    then show ?thesis
      using is_htp_iff_htps_exec sorted_distinct_zip_le
            strict_sorted_zip_butlast_tl_leq_or_geq consec_htps_in_zip_butlast_tl
      by (metis consec_htps_def in_set_butlastD in_set_tlD in_set_zipE)
  qed

  text \<open>Justification for @{const consec_htps_in_interval}.\<close>
  lemma consec_htps_in_interval_iff:
    assumes "t\<^sub>i \<le> t\<^sub>j"
    shows "\<forall>t t'. (consec_htps \<pi>s t t' \<and> t\<^sub>i \<le> t \<and> t' \<le> t\<^sub>j) 
            \<longleftrightarrow> (t,t') \<in> set (consec_htps_in_interval (htps_exec \<pi>s) t\<^sub>i t\<^sub>j)"
    unfolding consec_htps_in_interval_def
    using assms happ_time_pts_exec_iff_consec_htps is_htps_htps_exec
    by (auto simp: consec_htps_def)

  text \<open>All returned actions from @{const simplify_action} are correct instantiations of a @{type plan_action} 
  for an induced simple plan.\<close>
  lemma (in wf_ast_problem) simp_act_inst_of_plan_act: 
    assumes "wf_plan \<pi>s" 
        and "(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s" 
        and "(t\<^sub>a,a) \<in> set (simplify_action (htps_exec \<pi>s) (t\<^sub>\<pi>,\<pi>))" 
    shows "inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a)"
    using assms 
  proof (cases \<pi>)
    case 1: (Simple_Plan_Action n args)
    show ?thesis 
      using \<open>(t\<^sub>a,a) \<in> set (simplify_action (htps_exec \<pi>s) (t\<^sub>\<pi>,\<pi>))\<close> 
      unfolding inst_of_plan_action.simps 1 simplify_action.simps Let_def by simp
  next
    case (Durative_Plan_Action n args d)
    let ?htps="htps_exec \<pi>s"
    let ?a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a="the (resolve_action_schema n)"
    let ?a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t="inst_snap_action ?a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a args At_Start"
    let ?a\<^sub>e\<^sub>n\<^sub>d="inst_snap_action ?a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a args At_End"
    let ?a\<^sub>i\<^sub>n\<^sub>v="inst_snap_action ?a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a args Over_All"
    let ?t\<^sub>i\<^sub>n\<^sub>v="\<exists>t\<^sub>i t\<^sub>j. (t\<^sub>i,t\<^sub>j) \<in> set (consec_htps_in_interval ?htps t\<^sub>\<pi> (t\<^sub>\<pi> + d)) \<and> t\<^sub>a = (t\<^sub>i+t\<^sub>j) / 2"
    have "(a = ?a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t \<and> t\<^sub>\<pi> = t\<^sub>a) \<or> (a = ?a\<^sub>e\<^sub>n\<^sub>d \<and> t\<^sub>a = t\<^sub>\<pi> + d) \<or> (a = ?a\<^sub>i\<^sub>n\<^sub>v \<and> ?t\<^sub>i\<^sub>n\<^sub>v)"
      using \<open>(t\<^sub>a,a) \<in> set (simplify_action ?htps (t\<^sub>\<pi>,\<pi>))\<close> Durative_Plan_Action
      by (auto simp: Let_def) blast+
    then show ?thesis
    proof (elim disjE)
      assume "a = ?a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t \<and> t\<^sub>\<pi> = t\<^sub>a"
      then show ?thesis
        using Durative_Plan_Action by auto
    next
      assume "a = ?a\<^sub>e\<^sub>n\<^sub>d \<and> t\<^sub>a = t\<^sub>\<pi>+d"
      then show ?thesis
        using Durative_Plan_Action by auto
    next
      assume "a = ?a\<^sub>i\<^sub>n\<^sub>v \<and> ?t\<^sub>i\<^sub>n\<^sub>v"
      then have "res_inst_snap_action \<pi> Over_All = Some a"
        using Durative_Plan_Action by auto
      obtain t\<^sub>i t\<^sub>j where "(t\<^sub>i,t\<^sub>j) \<in> set (consec_htps_in_interval ?htps t\<^sub>\<pi> (t\<^sub>\<pi>+d))" 
                    and "t\<^sub>a = (t\<^sub>i+t\<^sub>j) / 2"
        using \<open>a = ?a\<^sub>i\<^sub>n\<^sub>v \<and> ?t\<^sub>i\<^sub>n\<^sub>v\<close> by auto
      have "t\<^sub>\<pi> \<le> t\<^sub>\<pi> + duration \<pi>"
        using assms Durative_Plan_Action unfolding wf_plan_def
        by (auto simp: Let_def split: option.splits ast_action_schema.splits)
      then have "consec_htps \<pi>s t\<^sub>i t\<^sub>j \<and> t\<^sub>\<pi> \<le> t\<^sub>i \<and> t\<^sub>j \<le> t\<^sub>\<pi> + d"
        using Durative_Plan_Action \<open>(t\<^sub>i,t\<^sub>j) \<in> set (consec_htps_in_interval ?htps t\<^sub>\<pi> (t\<^sub>\<pi> + d))\<close>
              consec_htps_in_interval_iff 
        by (auto simp: consec_htps_def)
      then have "t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j"
        using \<open>t\<^sub>a = (t\<^sub>i+t\<^sub>j) / 2\<close>
        by (auto simp: consec_htps_def)
      then show ?thesis
        using Durative_Plan_Action \<open>res_inst_snap_action \<pi> Over_All = Some a\<close> 
              \<open>consec_htps \<pi>s t\<^sub>i t\<^sub>j \<and> t\<^sub>\<pi> \<le> t\<^sub>i \<and> t\<^sub>j \<le> t\<^sub>\<pi> + d\<close>
        by auto
    qed
  qed 

  text \<open>Function to insort a happening into a happening sequence.\<close>
  fun insort_happ :: "happening \<Rightarrow> happening list \<Rightarrow> happening list" where
    "insort_happ (t\<^sub>i,A\<^sub>i) [] = [(t\<^sub>i,A\<^sub>i)]"
  | "insort_happ (t\<^sub>i,A\<^sub>i) ((t\<^sub>j,A\<^sub>j)#hs) = 
      (if t\<^sub>i < t\<^sub>j then (t\<^sub>i,A\<^sub>i)#(t\<^sub>j,A\<^sub>j)#hs
      else if t\<^sub>i = t\<^sub>j then (t\<^sub>j,A\<^sub>i @ A\<^sub>j)#hs
      else (t\<^sub>j,A\<^sub>j)#(insort_happ (t\<^sub>i,A\<^sub>i) hs))"

  text \<open>Properties of @{const insort_happ}\<close>

  lemma insort_happ_insort_insert: 
    "sorted (map fst hs) \<Longrightarrow> insort_insert (fst h) (map fst hs) = map fst (insort_happ h hs)"
    by (induction h hs rule: insort_happ.induct) (auto simp: insort_insert_key_def split: if_splits)

  text \<open>@{const insort_happ} preserves sorted-ness.\<close>
  lemma insort_happ_distinct: "strict_sorted (map fst hs) \<Longrightarrow> distinct (map fst (insort_happ h hs))"
    using strict_sorted_iff
    by (metis insort_happ_insort_insert distinct_insort_insert)

  lemma insort_happ_not_Nil:
    assumes "A\<^sub>i \<noteq> []" and "\<forall>(t\<^sub>j,A\<^sub>j) \<in> set hs. A\<^sub>j \<noteq> []" 
    shows "\<forall>(t\<^sub>j,A\<^sub>j) \<in> set (insort_happ (t\<^sub>i,A\<^sub>i) hs). A\<^sub>j \<noteq> []"
    using assms by (induction "(t\<^sub>i,A\<^sub>i)" hs rule: insort_happ.induct) auto

  (* Generalisation of following lemmas *)
  lemma insort_happ_action_subset_relaxed:
    assumes "(\<exists>H''. (t, H'') \<in> set hs \<and> set H \<subseteq> set H'') \<or> set H \<subseteq> set H'"
    shows "\<exists>A. (t, A) \<in> set (insort_happ (t, H') hs) \<and> set H \<subseteq> set A"
    using assms
    apply (induction "(t, H')" hs rule: insort_happ.induct)
     apply simp
    by force

  lemma insort_happ_action_subset: 
    "\<forall>(t\<^sub>a,A) \<in> set hs \<union> {h}. \<exists>A'. (t\<^sub>a,A') \<in> set (insort_happ h hs) \<and> set A \<subseteq> set A'"
    by (induction h hs rule: insort_happ.induct) auto+

  lemma insort_happ2_action_subset: 
    "\<exists>A'. (t\<^sub>2,A') \<in> set (insort_happ (t\<^sub>1,A\<^sub>1) (insort_happ (t\<^sub>2,A\<^sub>2) hs)) \<and> set A\<^sub>2 \<subseteq> set A'"
    using insort_happ_action_subset
    by (induction "(t\<^sub>2,A\<^sub>2)" hs rule: insort_happ.induct) auto
  (* TODO: lemma needed for proof of 'simp_plan_corr_dur_acts_end_aux'; try to proof without it *)

  

  lemma insort_happ_sorted: "sorted (map fst hs) \<Longrightarrow> sorted (map fst (insort_happ h hs))"
    by (metis insort_happ_insort_insert sorted_insort_insert)

  lemma insort_happ_strict_sorted: 
    "strict_sorted (map fst hs) \<Longrightarrow> strict_sorted (map fst (insort_happ h hs))"
    using insort_happ_sorted insort_happ_distinct
    by (simp add: strict_sorted_iff) 

  text \<open>Function to insort multiple happening into a happening sequence.\<close>
  fun insort_mult_happs :: "happening list \<Rightarrow> happening list \<Rightarrow> happening list" where
    "insort_mult_happs [] hs\<^sub>2 = hs\<^sub>2"
  | "insort_mult_happs (h#hs\<^sub>1) hs\<^sub>2 = insort_happ h (insort_mult_happs hs\<^sub>1 hs\<^sub>2)"

  fun insort_timed_ground_acts :: "(time \<times> ground_action) list \<Rightarrow> happening list \<Rightarrow> happening list" where
    "insort_timed_ground_acts [] hs = hs"
  | "insort_timed_ground_acts ((t\<^sub>a,a)#as) hs = 
    insort_happ (t\<^sub>a,[a]) (insort_timed_ground_acts as hs)"

  lemma insort_timed_ground_acts_correct: 
    "insort_mult_happs (map (\<lambda>(t,a). (t,[a])) as) hs = insort_timed_ground_acts as hs"
    by (induction as hs rule: insort_timed_ground_acts.induct) auto

  text \<open>Properties of @{const insort_mult_happs}\<close>

  lemma insort_mult_happs_strict_sorted: 
    "strict_sorted (map fst hs\<^sub>2) \<Longrightarrow> strict_sorted (map fst (insort_mult_happs hs\<^sub>1 hs\<^sub>2))"
    by (induction hs\<^sub>1 arbitrary: hs\<^sub>2) (auto simp: insort_happ_strict_sorted)

  lemma insort_mult_happs_not_Nil: 
    assumes "\<forall>(t\<^sub>a,A) \<in> set xs. A \<noteq> []" and "\<forall>(t\<^sub>a,A) \<in> set ys. A \<noteq> []" 
    shows "\<forall>(t\<^sub>a,A) \<in> set (insort_mult_happs xs ys). A \<noteq> []"
    using assms
  proof (induction xs ys rule: insort_mult_happs.induct)
    case (1 ys)
    then show ?case by simp
  next
    case (2 x xs ys)
    then show ?case
    proof (cases x)
      case (Pair t\<^sub>a A)
      then have "\<forall>(t\<^sub>a,A) \<in> set xs. A \<noteq> []" and "A \<noteq> []"
        using \<open>\<forall>(t\<^sub>a,A) \<in> set (x#xs). A \<noteq> []\<close>
        by auto
      then show ?thesis 
        using Pair "2.IH"[OF \<open>\<forall>(t\<^sub>a,A) \<in> set xs. A \<noteq> []\<close> \<open>\<forall>(t\<^sub>a,A) \<in> set ys. A \<noteq> []\<close>]
              insort_happ_not_Nil[OF \<open>A \<noteq> []\<close>] by auto
    qed
  qed

  lemma insort_mult_happs_action_subset1: 
    "(t\<^sub>a,A) \<in> set hs\<^sub>1 \<Longrightarrow> \<exists>as'. (t\<^sub>a,as') \<in> set (insort_mult_happs hs\<^sub>1 hs\<^sub>2) \<and> set A \<subseteq> set as'"
  proof (induction hs\<^sub>1)
    case Nil
    then show ?case
      by auto
  next
    case (Cons h hs\<^sub>1)
    have "(t\<^sub>a,A) = h \<or> (t\<^sub>a,A) \<noteq> h"
      by simp
    then show ?case
    proof
      assume "(t\<^sub>a,A) = h"
      then show ?case
        using insort_happ_action_subset by auto
    next
      assume "(t\<^sub>a,A) \<noteq> h"
      then have "(t\<^sub>a,A) \<in> set hs\<^sub>1"
        using Cons.prems by auto
      then obtain A' where "(t\<^sub>a,A') \<in> set (insort_mult_happs hs\<^sub>1 hs\<^sub>2)" and "set A \<subseteq> set A'"
        using Cons.IH by auto
      then obtain A'' where "(t\<^sub>a,A'') \<in> set (insort_happ h (insort_mult_happs hs\<^sub>1 hs\<^sub>2))" 
                       and "set A' \<subseteq> set A''"
        using insort_happ_action_subset[where h="h" and hs="insort_mult_happs hs\<^sub>1 hs\<^sub>2"] by auto
      then show ?case
        using \<open>set A \<subseteq> set A'\<close> by auto
    qed
  qed

  lemma insort_mult_happs_action_subset2: 
    assumes "(t\<^sub>a,A) \<in> set hs\<^sub>2" 
    shows "\<exists>A'. (t\<^sub>a,A') \<in> set (insort_mult_happs hs\<^sub>1 hs\<^sub>2) \<and> set A \<subseteq> set A'"
  proof (induction hs\<^sub>1)
    case Nil
    then show ?case 
      using assms by auto
  next
    case (Cons h hs\<^sub>1)
    obtain A' where "(t\<^sub>a,A') \<in> set (insort_mult_happs hs\<^sub>1 hs\<^sub>2)" and "set A \<subseteq> set A'"
      using assms Cons.IH by auto
    then obtain A'' where "(t\<^sub>a,A'') \<in> set (insort_happ h (insort_mult_happs hs\<^sub>1 hs\<^sub>2))" 
                       and "set A' \<subseteq> set A''"
      using insort_happ_action_subset[where h="h" and hs="insort_mult_happs hs\<^sub>1 hs\<^sub>2"] by auto
    then show ?case
      using \<open>set A \<subseteq> set A'\<close> by auto
  qed

  lemma insort_mult_happs_action_subset: 
    "\<forall>(t\<^sub>a,A) \<in> set hs\<^sub>1 \<union> set hs\<^sub>2. \<exists>A'. (t\<^sub>a,A') \<in> set (insort_mult_happs hs\<^sub>1 hs\<^sub>2) \<and> set A \<subseteq> set A'"
    using insort_mult_happs_action_subset1 insort_mult_happs_action_subset2 by fastforce

  lemma insort_happ2_insort_mult_happs_action_subset_aux:
    assumes "(t\<^sub>a,A) \<in> set hs\<^sub>1" 
    shows "\<exists>A'. (t\<^sub>a,A') \<in> set (insort_happ (t\<^sub>1,A\<^sub>1) (insort_happ (t\<^sub>2,A\<^sub>2) (insort_mult_happs hs\<^sub>1 hs\<^sub>2))) \<and> set A \<subseteq> set A'"
  proof -
    have "\<exists>A'. (t\<^sub>a,A') \<in> set (insort_mult_happs hs\<^sub>1 hs\<^sub>2) \<and> set A \<subseteq> set A'"
      using assms insort_mult_happs_action_subset[where hs\<^sub>1="hs\<^sub>1" and hs\<^sub>2="hs\<^sub>2"]
      by (auto split: prod.splits)
    then obtain A' where "(t\<^sub>a,A') \<in> set (insort_mult_happs hs\<^sub>1 hs\<^sub>2)" and "set A \<subseteq> set A'"
      by auto
    then obtain A'' where "(t\<^sub>a,A'') \<in> set (insort_happ (t\<^sub>2,A\<^sub>2) (insort_mult_happs hs\<^sub>1 hs\<^sub>2))" 
                       and "set A' \<subseteq> set A''"
      using insort_happ_action_subset[where h="(t\<^sub>2,A\<^sub>2)" and hs="insort_mult_happs hs\<^sub>1 hs\<^sub>2"] by auto
    then obtain A''' where "(t\<^sub>a,A''') \<in> set (insort_happ (t\<^sub>1,A\<^sub>1) (insort_happ (t\<^sub>2,A\<^sub>2) (insort_mult_happs hs\<^sub>1 hs\<^sub>2)))" 
                        and "set A'' \<subseteq> set A'''"
      using insort_happ_action_subset[where h="(t\<^sub>1,A\<^sub>1)" 
                                       and hs="insort_happ (t\<^sub>2,A\<^sub>2) (insort_mult_happs hs\<^sub>1 hs\<^sub>2)"]
      by auto
    show ?thesis
      using \<open>(t\<^sub>a,A) \<in> set hs\<^sub>1\<close> 
            \<open>(t\<^sub>a,A''') \<in> set (insort_happ (t\<^sub>1,A\<^sub>1) (insort_happ (t\<^sub>2,A\<^sub>2) (insort_mult_happs hs\<^sub>1 hs\<^sub>2)))\<close> 
            \<open>set A \<subseteq> set A'\<close> \<open>set A' \<subseteq> set A''\<close> \<open>set A'' \<subseteq> set A'''\<close> by auto
  qed                                                                                                                       
  (* TODO: lemma needed for proof of simp_plan_corr_dur_acts_overall_aux; try to proof without it *)

  lemma insort_happ2_insort_mult_happs_action_subset:
    "\<forall>(t\<^sub>a,A) \<in> set hs\<^sub>1. \<exists>A'. (t\<^sub>a,A') \<in> set (insort_happ (t\<^sub>1,A\<^sub>1) (insort_happ (t\<^sub>2,A\<^sub>2) (insort_mult_happs hs\<^sub>1 hs\<^sub>2))) \<and> set A \<subseteq> set A'"
    using insort_happ2_insort_mult_happs_action_subset_aux by auto                                                                                                      
  (* TODO: merge this with 'insort_happ2_insort_mult_happs_action_subset_aux' *)

  text \<open>We can define a function to construct a simplified plan for a given temporal plan.\<close>
  fun simplify_plan :: "time list \<Rightarrow> plan \<Rightarrow> happening list" where
    "simplify_plan htps [] = []"
  | "simplify_plan htps (\<pi>#\<pi>s) = 
      insort_mult_happs (map (\<lambda>(t\<^sub>a,a). (t\<^sub>a,[a])) (simplify_action htps \<pi>)) (simplify_plan htps \<pi>s)"

  text \<open>Definition of subset on happening sequences. This is used to simplify some proofs.\<close>

  definition happ_seq_member :: "happening \<Rightarrow> happening list \<Rightarrow> bool" (infix "\<in>\<^sub>h\<^sub>s" 53) where
    "happ_seq_member h hs \<longleftrightarrow> (case h of (t\<^sub>a,A) \<Rightarrow> \<exists>A\<^sub>2. set A \<subseteq> set A\<^sub>2 \<and> (t\<^sub>a,A\<^sub>2) \<in> set hs)"

  definition happ_seq_subset :: "happening list \<Rightarrow> happening list \<Rightarrow> bool" (infix "\<subseteq>\<^sub>h\<^sub>s" 53) where
    "happ_seq_subset hs\<^sub>1 hs\<^sub>2 \<longleftrightarrow> (\<forall>h\<^sub>1 \<in> set hs\<^sub>1. h\<^sub>1 \<in>\<^sub>h\<^sub>s hs\<^sub>2)"

  text \<open>Properties of @{const happ_seq_subset}\<close>

  lemma happ_seq_subset_Nil: "[] \<subseteq>\<^sub>h\<^sub>s hs"
    unfolding happ_seq_subset_def by auto

  lemma happ_seq_subset_refl: "hs \<subseteq>\<^sub>h\<^sub>s hs"
    unfolding happ_seq_subset_def happ_seq_member_def by auto

  lemma happ_seq_subset_trans: "hs\<^sub>1 \<subseteq>\<^sub>h\<^sub>s hs\<^sub>2 \<and> hs\<^sub>2 \<subseteq>\<^sub>h\<^sub>s hs\<^sub>3 \<Longrightarrow> hs\<^sub>1 \<subseteq>\<^sub>h\<^sub>s hs\<^sub>3"
    unfolding happ_seq_subset_def happ_seq_member_def
    by (auto split: prod.splits) (metis (full_types) dual_order.trans)

  lemma insort_happ_subset: "hs \<subseteq>\<^sub>h\<^sub>s insort_happ h hs"
  proof -
    have "hs = [] \<or> hs \<noteq> []"
      by simp
    then show ?thesis
    proof
      assume "hs = []"
      then show ?thesis
        unfolding happ_seq_subset_def by auto
    next
      assume "hs \<noteq> []"
      then show ?thesis
        unfolding happ_seq_subset_def happ_seq_member_def
        using insort_happ_action_subset by blast
    qed
  qed

  lemma insort_mult_happs_subset: "hs\<^sub>1 \<subseteq>\<^sub>h\<^sub>s insort_mult_happs hs\<^sub>2 hs\<^sub>1"
  proof (induction hs\<^sub>2 hs\<^sub>1 rule: insort_mult_happs.induct)
    case (1 hs)
    then show ?case
      using happ_seq_subset_refl by simp
  next
    case (2 a A hs)
    have "insort_mult_happs (a # A) hs = insort_happ a (insort_mult_happs A hs)"
      by simp
    then have "insort_mult_happs A hs \<subseteq>\<^sub>h\<^sub>s insort_mult_happs (a # A) hs"
      using insort_happ_subset by auto
    then show ?case
      using "2.IH" happ_seq_subset_trans by blast
  qed

  text \<open>Happening sequence subset for simplify plan.\<close>
  lemma simplify_plan_happs_subset_Cons: "simplify_plan htps \<pi>s \<subseteq>\<^sub>h\<^sub>s simplify_plan htps (\<pi>#\<pi>s)"
    using insort_mult_happs_subset happ_seq_subset_refl
    by (induction \<pi>s arbitrary: \<pi>) auto

  lemma simplify_plan_happs_subset_app: "simplify_plan htps \<pi>s\<^sub>2 \<subseteq>\<^sub>h\<^sub>s simplify_plan htps (\<pi>s\<^sub>1 @ \<pi>s\<^sub>2)"
    using simplify_plan_happs_subset_Cons
    apply (induction \<pi>s\<^sub>1 arbitrary: \<pi>s\<^sub>2)
    apply (auto simp: happ_seq_subset_refl)
    using happ_seq_subset_trans apply blast
    done

  text \<open>Properties of @{const simplify_plan}\<close>

  text \<open>All happenings in a simplified plan are always non-Nil.\<close>
  lemma simp_plan_happ_not_Nil:
    fixes \<pi>s
    defines "htps \<equiv> htps_exec \<pi>s"
    shows "\<forall>(t\<^sub>a,A) \<in> set (simplify_plan htps \<pi>s). A \<noteq> []"
  proof (induction \<pi>s)
    case Nil
    then show ?case by simp
  next
    case (Cons \<pi> \<pi>s) 
    have "\<forall>(t\<^sub>a,A) \<in> set (map (\<lambda>(t\<^sub>a,a). (t\<^sub>a,[a])) (simplify_action htps \<pi>)). A \<noteq> []"
      by auto
    then show ?case 
      using "Cons.IH" insort_mult_happs_not_Nil simplify_plan.simps(2) 
      by presburger
  qed

  text \<open>A simplified plan produced by @{const simplify_plan} is strictly sorted.\<close>
  lemma simp_plan_strict_sorted: "strict_sorted (map fst (simplify_plan htps \<pi>s))"
    by (induction \<pi>s) (auto simp: insort_mult_happs_strict_sorted)

  text \<open>A simplified plan contains all grounded actions for every @{const Simple_Plan_Action}.\<close>
  lemma simp_plan_corr_simp_acts: 
    assumes "hs = simplify_plan htps \<pi>s" 
        and "(t\<^sub>\<pi>,\<pi>) \<in> simple_acts \<pi>s"
    shows "\<exists>A. (t\<^sub>\<pi>,A) \<in> set hs \<and> the (res_inst \<pi> At_Start) \<in> set A"
    using assms
  proof -
    obtain \<pi>s\<^sub>1 \<pi>s\<^sub>2 where "\<pi>s = \<pi>s\<^sub>1 @ ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)"
      using assms simple_acts_subset by (meson split_list subsetD)
    then obtain hs' where "hs' = simplify_plan htps ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)"
      by simp
    have "(t\<^sub>\<pi>,\<pi>) = hd ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)"
      by auto
    have "(t\<^sub>\<pi>, \<pi>) \<in> simple_acts ((t\<^sub>\<pi>, \<pi>) # \<pi>s\<^sub>2)"
      using assms \<open>\<pi>s = \<pi>s\<^sub>1 @ ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close>
      unfolding simple_acts_def is_act_simple_def by (auto split: plan_action.splits)
    have "\<exists>as. (t\<^sub>\<pi>,as) \<in> set hs' \<and> set [the (res_inst \<pi> At_Start)] \<subseteq> set as"
      using \<open>(t\<^sub>\<pi>,\<pi>) = hd ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close> 
            \<open>(t\<^sub>\<pi>, \<pi>) \<in> simple_acts ((t\<^sub>\<pi>, \<pi>) # \<pi>s\<^sub>2)\<close>
      unfolding \<open>hs' = simplify_plan htps ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close> simple_acts_def is_act_simple_def simplify_plan.simps
      apply (induction \<pi>)
      unfolding simplify_action.simps Let_def list.map prod.case
      unfolding insort_mult_happs.simps comp_def list.sel set_filter res_inst.simps option.sel
      using insort_happ_action_subset_relaxed by fastforce+
    hence "\<exists>as. (t\<^sub>\<pi>,as) \<in> set hs' \<and> the (res_inst \<pi> At_Start) \<in> set as" by auto
    have "hs' \<subseteq>\<^sub>h\<^sub>s hs"
      using assms simplify_plan_happs_subset_app 
            \<open>hs' = simplify_plan htps ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close> 
            \<open>\<pi>s = \<pi>s\<^sub>1 @ ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close>
      by blast
    show ?thesis
      using \<open>\<exists>as. (t\<^sub>\<pi>,as) \<in> set hs' \<and> the (res_inst \<pi> At_Start) \<in> set as\<close>
            \<open>hs' \<subseteq>\<^sub>h\<^sub>s hs\<close>
      unfolding happ_seq_subset_def happ_seq_member_def by blast
  qed

  lemma simp_plan_corr_dur_acts_start_aux: 
    assumes "hs = simplify_plan htps \<pi>s" 
        and "(t\<^sub>\<pi>,\<pi>) = hd \<pi>s" 
        and "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s"
    shows "(\<exists>A. (t\<^sub>\<pi>,A) \<in> set hs \<and> (the (res_inst_snap_action \<pi> At_Start)) \<in> set A)"
    using assms insort_happ_action_subset
    unfolding durative_acts_def is_act_simple_def
    apply (induction \<pi>s)
    apply (auto simp: Let_def split: plan_action.splits)
    apply (meson list.set_intros(1) subsetD)
    done (* TODO: clean up proof! *)

  text \<open>A simplified plan contains all @{const At_Start}-snap-actions.\<close>
  lemma simp_plan_corr_dur_acts_start: 
    fixes \<pi>
    defines "a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t \<equiv> the (res_inst_snap_action \<pi> At_Start)"
    assumes "hs = simplify_plan htps \<pi>s" 
        and "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s"
    shows "\<exists>A. (t\<^sub>\<pi>,A) \<in> set hs \<and> a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t \<in> set A"
    using assms
  proof -
    obtain \<pi>s\<^sub>1 \<pi>s\<^sub>2 where "\<pi>s = \<pi>s\<^sub>1 @ ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)"
      using assms dur_acts_subset by (meson split_list subsetD)
    then obtain hs' where "hs' = simplify_plan htps ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)"
      by simp
    have "(t\<^sub>\<pi>,\<pi>) = hd ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)"
      by auto
    have "(t\<^sub>\<pi>, \<pi>) \<in> durative_acts ((t\<^sub>\<pi>, \<pi>) # \<pi>s\<^sub>2)"
      using assms \<open>\<pi>s = \<pi>s\<^sub>1 @ ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close>
      unfolding durative_acts_def is_act_simple_def by (auto split: plan_action.splits)
    have "\<exists>as. (t\<^sub>\<pi>,as) \<in> set hs' \<and> a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t \<in> set as"
      using assms simp_plan_corr_dur_acts_start_aux[OF \<open>hs' = simplify_plan htps ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close> 
                                                       \<open>(t\<^sub>\<pi>,\<pi>) = hd ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close> 
                                                       \<open>(t\<^sub>\<pi>,\<pi>) \<in> durative_acts ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close>] 
      by simp
    have "hs' \<subseteq>\<^sub>h\<^sub>s hs"
      using assms simplify_plan_happs_subset_app 
            \<open>hs' = simplify_plan htps ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close> 
            \<open>\<pi>s = \<pi>s\<^sub>1 @ ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close>
      by blast
    show ?thesis
      using \<open>\<exists>as. (t\<^sub>\<pi>,as) \<in> set hs' \<and> a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t \<in> set as\<close>
            \<open>hs' \<subseteq>\<^sub>h\<^sub>s hs\<close>
      unfolding happ_seq_subset_def happ_seq_member_def by blast
  qed

  lemma simp_plan_corr_dur_acts_end_aux: 
    assumes "hs = simplify_plan htps \<pi>s" 
        and "(t\<^sub>\<pi>,\<pi>) = hd \<pi>s" 
        and "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s"
    shows "(\<exists>A. (t\<^sub>\<pi> + (duration \<pi>),A) \<in> set hs \<and> (the (res_inst_snap_action \<pi> At_End)) \<in> set A)"
    using assms insort_happ2_action_subset
    unfolding durative_acts_def is_act_simple_def
    apply (induction \<pi>s)
    apply (auto simp: Let_def split: plan_action.splits)
    apply (meson list.set_intros(1) subsetD)
    done (* TODO: clean up proof! *)

  text \<open>A simplified plan contains all @{const At_End}-snap-actions.\<close>
  lemma simp_plan_corr_dur_acts_end: 
    fixes \<pi>
    defines "a\<^sub>e\<^sub>n\<^sub>d \<equiv> the (res_inst_snap_action \<pi> At_End)"
    assumes "hs = simplify_plan htps \<pi>s" 
        and "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s"
    shows "\<exists>A. (t\<^sub>\<pi> + (duration \<pi>),A) \<in> set hs \<and> a\<^sub>e\<^sub>n\<^sub>d \<in> set A"
    using assms
  proof -
    obtain \<pi>s\<^sub>1 \<pi>s\<^sub>2 where "\<pi>s = \<pi>s\<^sub>1 @ ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)"
      using assms dur_acts_subset by (meson split_list subsetD) 
    then obtain hs' where "hs' = simplify_plan htps ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)"
      by simp
    have "(t\<^sub>\<pi>,\<pi>) = hd ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)"
      by auto
    have "(t\<^sub>\<pi>, \<pi>) \<in> durative_acts ((t\<^sub>\<pi>, \<pi>) # \<pi>s\<^sub>2)"
      using assms \<open>\<pi>s = \<pi>s\<^sub>1 @ ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close>
      unfolding durative_acts_def is_act_simple_def by (auto split: plan_action.splits)
    have "\<exists>as. (t\<^sub>\<pi> + (duration \<pi>),as) \<in> set hs' \<and> a\<^sub>e\<^sub>n\<^sub>d \<in> set as"
      using assms simp_plan_corr_dur_acts_end_aux[OF \<open>hs' = simplify_plan htps ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close> 
                                                     \<open>(t\<^sub>\<pi>,\<pi>) = hd ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close> 
                                                     \<open>(t\<^sub>\<pi>,\<pi>) \<in> durative_acts ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close>] 
      by simp
    have "hs' \<subseteq>\<^sub>h\<^sub>s hs"
      using assms simplify_plan_happs_subset_app 
            \<open>hs' = simplify_plan htps ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close> 
            \<open>\<pi>s = \<pi>s\<^sub>1 @ ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close>
      by blast
    show ?thesis
      using \<open>\<exists>as. (t\<^sub>\<pi> + (duration \<pi>),as) \<in> set hs' \<and> a\<^sub>e\<^sub>n\<^sub>d \<in> set as\<close>
            \<open>hs' \<subseteq>\<^sub>h\<^sub>s hs\<close>
      unfolding happ_seq_subset_def happ_seq_member_def by blast
  qed

  (* Does this lemma already exist? *)
  lemma member_map: "a \<in> set A \<Longrightarrow> f a \<in> set (map f A)"
    by simp

  lemma simp_plan_corr_dur_acts_overall_aux: 
    assumes "strict_sorted htps"
        and "hs = simplify_plan htps \<pi>s"
        and "(t\<^sub>\<pi>,\<pi>) = hd \<pi>s" 
        and "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s"
    shows "\<forall>t\<^sub>i t\<^sub>j. (t\<^sub>i,t\<^sub>j) \<in> set (consec_htps_in_interval htps t\<^sub>\<pi> (t\<^sub>\<pi> + duration \<pi>)) \<longrightarrow>
            (\<exists>(t',A) \<in> set hs. t\<^sub>i < t' \<and> t' < t\<^sub>j \<and> (the (res_inst_snap_action \<pi> Over_All)) \<in> set A)"
    using assms
    unfolding durative_acts_def is_act_simple_def
  proof (induction \<pi>s)
    case Nil
    then show ?case 
      by simp
  next
    case (Cons \<pi> \<pi>s)
    fix t\<^sub>i t\<^sub>j
    obtain t\<^sub>\<pi> \<pi>' where "\<pi> = (t\<^sub>\<pi>,\<pi>')"
      by (meson surj_pair)
    then show ?case
    proof (cases \<pi>')
      case (Simple_Plan_Action n args)
      then show ?thesis 
        using Cons.prems \<open>\<pi> = (t\<^sub>\<pi>,\<pi>')\<close> by simp
      next
        case (Durative_Plan_Action n args d)
        let ?to_happ = "\<lambda>(t\<^sub>a,a). (t\<^sub>a,[a])"
        let ?snap_act = "inst_snap_action (the (resolve_action_schema n)) args"
        let ?chtps_in_intv = "consec_htps_in_interval htps t\<^sub>\<pi> (t\<^sub>\<pi> + duration \<pi>')"
        let ?hs\<^sub>1 = "map (\<lambda>(t\<^sub>i,t\<^sub>j).((t\<^sub>i+t\<^sub>j) / 2,?snap_act Over_All)) ?chtps_in_intv"
        have 1: "\<forall>(t\<^sub>a,A) \<in> set (map ?to_happ ?hs\<^sub>1). \<exists>A'. (t\<^sub>a,A') \<in> set (simplify_plan htps (\<pi>#\<pi>s)) \<and> set A \<subseteq> set A'"
          using \<open>\<pi> = (t\<^sub>\<pi>,\<pi>')\<close> Durative_Plan_Action insort_happ2_insort_mult_happs_action_subset
          by (auto simp: Let_def)
        have "\<forall>(t\<^sub>i, t\<^sub>j) \<in> set ?chtps_in_intv. ((t\<^sub>i+t\<^sub>j) / 2,?snap_act Over_All) \<in> set ?hs\<^sub>1"
          by auto
        then have "\<forall>(t\<^sub>i, t\<^sub>j) \<in> set ?chtps_in_intv. 
                    ?to_happ ((t\<^sub>i+t\<^sub>j) / 2,?snap_act Over_All) \<in> set (map ?to_happ ?hs\<^sub>1)"
          by (smt member_map case_prodI2 case_prod_conv) (* TODO: why can I not proof this easier? *)
        then have "\<forall>(t\<^sub>i, t\<^sub>j) \<in> set ?chtps_in_intv. 
                    (\<exists>A. ((t\<^sub>i+t\<^sub>j) / 2,A) \<in> set hs \<and> 
                      t\<^sub>i < (t\<^sub>i+t\<^sub>j) / 2 \<and> (t\<^sub>i+t\<^sub>j) / 2 < t\<^sub>j \<and> 
                        (the (res_inst_snap_action \<pi>' Over_All)) \<in> set A)"
          using 1 Durative_Plan_Action \<open>hs = simplify_plan htps (\<pi>#\<pi>s)\<close> 
                sorted_distinct_zip_le[OF \<open>strict_sorted htps\<close>]
          by (auto simp: consec_htps_in_interval_def)
        then have "\<forall>t\<^sub>i t\<^sub>j. (t\<^sub>i, t\<^sub>j) \<in> set ?chtps_in_intv \<longrightarrow> 
                    (\<exists>(t',A) \<in> set hs. t\<^sub>i < t' \<and> t' < t\<^sub>j \<and> 
                      (the (res_inst_snap_action \<pi>' Over_All)) \<in> set A)"
          by fastforce
        then show ?thesis
          using Cons.prems \<open>\<pi> = (t\<^sub>\<pi>,\<pi>')\<close> Durative_Plan_Action by simp
    qed
  qed (* TODO: clean up! *)

  text \<open>A simplified plan contains all @{const Over_All}-snap-actions.\<close>
  lemma (in wf_ast_problem) simp_plan_corr_dur_acts_overall:
    fixes \<pi> \<pi>s
    defines "htps \<equiv> htps_exec \<pi>s" 
        and "a\<^sub>i\<^sub>n\<^sub>v \<equiv> the (res_inst_snap_action \<pi> Over_All)"
    assumes "wf_plan \<pi>s" 
        and "hs = simplify_plan htps \<pi>s" 
        and "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s"
    shows "\<forall>t\<^sub>i t\<^sub>j. (consec_htps \<pi>s t\<^sub>i t\<^sub>j \<and> t\<^sub>\<pi> \<le> t\<^sub>i \<and> t\<^sub>j \<le> t\<^sub>\<pi> + duration \<pi>) \<longrightarrow> 
            (\<exists>(t',A) \<in> set hs. t\<^sub>i < t' \<and> t' < t\<^sub>j \<and> a\<^sub>i\<^sub>n\<^sub>v \<in> set A)"
    (*shows "\<forall>t\<^sub>i t\<^sub>j. (consec_htps \<pi>s t\<^sub>i t\<^sub>j \<and> t\<^sub>\<pi> \<le> t\<^sub>i \<and> t\<^sub>j \<le> t\<^sub>\<pi> + duration \<pi>) \<longrightarrow> 
            (\<exists>t'. t\<^sub>i < t' \<and> t' < t\<^sub>j \<and> (\<exists>as. (t',as) \<in> set hs \<and> a\<^sub>i\<^sub>n\<^sub>v \<in> set as))"*)
    using assms
  proof -
    have "strict_sorted htps"
      using assms htps_exec_sorted htps_exec_distinct by (simp add: strict_sorted_iff)
    have "t\<^sub>\<pi> \<le> t\<^sub>\<pi> + duration \<pi>"
      using assms unfolding wf_plan_def durative_acts_def is_act_simple_def
      by (auto simp: Let_def split: option.splits plan_action.splits ast_action_schema.splits)
    obtain \<pi>s\<^sub>1 \<pi>s\<^sub>2 where "\<pi>s = \<pi>s\<^sub>1 @ ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)"
      using assms dur_acts_subset by (meson split_list subsetD) 
    then have "(t\<^sub>\<pi>,\<pi>) = hd ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)" and "(t\<^sub>\<pi>, \<pi>) \<in> durative_acts ((t\<^sub>\<pi>, \<pi>) # \<pi>s\<^sub>2)"
      using assms unfolding durative_acts_def is_act_simple_def by (auto split: plan_action.splits)
    obtain hs' where "hs' = simplify_plan htps ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)"
      by simp
    then have "hs' \<subseteq>\<^sub>h\<^sub>s hs"
      using assms simplify_plan_happs_subset_app \<open>\<pi>s = \<pi>s\<^sub>1 @ ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close> by blast
    have "\<forall>t\<^sub>i t\<^sub>j. (t\<^sub>i,t\<^sub>j) \<in> set (consec_htps_in_interval htps t\<^sub>\<pi> (t\<^sub>\<pi> + (duration \<pi>))) 
          \<longrightarrow> (\<exists>(t',A) \<in> set hs'. t\<^sub>i < t' \<and> t' < t\<^sub>j \<and> a\<^sub>i\<^sub>n\<^sub>v \<in> set A)"
      using assms simp_plan_corr_dur_acts_overall_aux[OF \<open>strict_sorted htps\<close>
                                                         \<open>hs' = simplify_plan htps ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close> 
                                                         \<open>(t\<^sub>\<pi>,\<pi>) = hd ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close> 
                                                         \<open>(t\<^sub>\<pi>,\<pi>) \<in> durative_acts ((t\<^sub>\<pi>,\<pi>)#\<pi>s\<^sub>2)\<close>]
      by auto
    then have "\<forall>t\<^sub>i t\<^sub>j. (consec_htps \<pi>s t\<^sub>i t\<^sub>j \<and> t\<^sub>\<pi> \<le> t\<^sub>i \<and> t\<^sub>j \<le> t\<^sub>\<pi> + (duration \<pi>)) 
              \<longrightarrow> (\<exists>(t',as) \<in> set hs'. t\<^sub>i < t' \<and> t' < t\<^sub>j \<and> a\<^sub>i\<^sub>n\<^sub>v \<in> set as)"
      using htps_def consec_htps_in_interval_iff[OF \<open>t\<^sub>\<pi> \<le> t\<^sub>\<pi> + (duration \<pi>)\<close>] by auto
    then show ?thesis
      using \<open>hs' \<subseteq>\<^sub>h\<^sub>s hs\<close> unfolding happ_seq_subset_def happ_seq_member_def by blast
  qed

  text \<open>Flatten a happening into individual timed grounded actions. This is used to simplify proofs.\<close>
  fun set_happ_acts :: "happening list \<Rightarrow> (time \<times> ground_action) set" where
    "set_happ_acts [] = {}"
  | "set_happ_acts ((t\<^sub>a,A)#hs) = {(t\<^sub>a',a'). t\<^sub>a = t\<^sub>a' \<and> a' \<in> set A} \<union> set_happ_acts hs"

  lemma set_happ_acts_refine:
    "(\<exists>A. (t\<^sub>a,A) \<in> set hs \<and> a \<in> set A) \<longleftrightarrow> ((t\<^sub>a,a) \<in> set_happ_acts hs)"
    by (induction hs) auto

  lemma set_happ_acts_insort_happ: 
    "set_happ_acts (insort_happ h hs) = set_happ_acts [h] \<union> set_happ_acts hs"
    by (induction h hs rule: insort_happ.induct) auto

  lemma set_happ_acts_insort_mult_happs: 
    "set_happ_acts (insort_mult_happs hs\<^sub>1 hs\<^sub>2) = set_happ_acts hs\<^sub>1 \<union> set_happ_acts hs\<^sub>2"
    using set_happ_acts_insort_happ
    by (induction hs\<^sub>1) auto

  lemma set_happ_acts_to_happ: "set_happ_acts (map (\<lambda>(t\<^sub>a,a). (t\<^sub>a,[a])) xs) = set xs"
  proof (induction xs)
    case Nil
    then show ?case 
      by auto
  next
    case (Cons x xs)
    then show ?case 
      by (cases x) (auto split: prod.splits)
  qed

  lemma simp_plan_corr_inst_plan_act_aux:
    assumes "strict_sorted htps"
        and "hs = simplify_plan htps \<pi>s" 
    shows "\<forall>(t\<^sub>a,a) \<in> set_happ_acts hs. \<exists>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s. (t\<^sub>a,a) \<in> set (simplify_action htps (t\<^sub>\<pi>,\<pi>))"
    using assms set_happ_acts_insort_mult_happs set_happ_acts_to_happ
    by (induction \<pi>s arbitrary: hs) auto

  text \<open>Every ground action in a simplified plan is the instantiation of a plan action.\<close>
  lemma (in wf_ast_problem) simp_plan_corr_inst_plan_act: 
    fixes \<pi>s
    defines "htps \<equiv> htps_exec \<pi>s"
    assumes "wf_plan \<pi>s" 
        and "hs = simplify_plan htps \<pi>s" 
        and "(t\<^sub>a,A) \<in> set hs" 
        and "a \<in> set A"
    shows "\<exists>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s. inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a)"
  proof -
    have "strict_sorted htps"
      using assms htps_exec_sorted htps_exec_distinct by (simp add: strict_sorted_iff)
    have "\<exists>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s. (t\<^sub>a,a) \<in> set (simplify_action htps (t\<^sub>\<pi>,\<pi>))"
      using assms
            simp_plan_corr_inst_plan_act_aux[OF \<open>strict_sorted htps\<close> \<open>hs = simplify_plan htps \<pi>s\<close>]
            set_happ_acts_refine by blast
    then obtain t\<^sub>\<pi> \<pi> where "(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s" and "(t\<^sub>a,a) \<in> set (simplify_action htps (t\<^sub>\<pi>,\<pi>))"
      by auto
    show ?thesis
      using assms \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> \<open>(t\<^sub>a,a) \<in> set (simplify_action htps (t\<^sub>\<pi>,\<pi>))\<close>
            simp_act_inst_of_plan_act by blast
  qed

  text \<open>Finally the correctness proof for @{const simplify_plan}\<close>
  lemma (in wf_ast_problem) simplify_plan_correct: 
    fixes \<pi>s
    defines "htps \<equiv> htps_exec \<pi>s"
    assumes "wf_plan \<pi>s"
    shows "ind_happ_seq \<pi>s (simplify_plan htps \<pi>s)"
    unfolding ind_happ_seq_def            
    using assms
          simp_plan_happ_not_Nil
          simp_plan_strict_sorted 
          simp_plan_corr_simp_acts 
          simp_plan_corr_dur_acts_start
          simp_plan_corr_dur_acts_end
          simp_plan_corr_dur_acts_overall
          simp_plan_corr_inst_plan_act
    by auto

  (* concise lemma for paper *)
  lemma (in wf_ast_problem)
    assumes "wf_plan \<pi>s"
    shows "ind_happ_seq \<pi>s (simplify_plan (htps_exec \<pi>s) \<pi>s)"
    using assms by (rule simplify_plan_correct)

  (*text \<open>@{const simplify_plan} always produces the same happening sequences 
  regardless of the plan ordering.\<close>
  lemma (in wf_ast_problem) simp_plan_eq_plan_order:
    assumes "set \<pi>s = set \<pi>s'" and "wf_plan \<pi>s" and "wf_plan \<pi>s'"
    shows "ind_happ_seq \<pi>s (simplify_plan (htps_exec \<pi>s') \<pi>s')"
  proof -
    show ?thesis
      using simplify_plan_correct
      sorry
  qed*)

  text \<open>With the correctness proof of @{const simplify_plan}. 
  We can easily proof that for every plan there exists an induced happening sequence.\<close>
  lemma (in wf_ast_problem) ind_happ_seq_exists: 
    assumes "wf_plan \<pi>s"
    shows "\<exists>hs. ind_happ_seq \<pi>s hs"
    using assms simplify_plan_correct by auto

  lemma (in wf_ast_problem) simplify_plan_wf_ground_action_aux:
    fixes \<pi>s
    defines "htps \<equiv> htps_exec \<pi>s"
    assumes "wf_plan \<pi>s"
        and "hs = simplify_plan htps \<pi>s"
        and "(t\<^sub>a,A) \<in> set hs"
        and "a \<in> set A"
    shows "wf_ground_action a"
  proof -
    obtain t\<^sub>\<pi> \<pi> where "(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s" and "inst_of_plan_action \<pi>s (t\<^sub>\<pi>, \<pi>) (t\<^sub>a, a)"
      using assms simp_plan_corr_inst_plan_act by blast
    then show ?thesis
      using assms wf_inst_of_plan_action by simp
  qed

  lemma (in wf_ast_problem) simplify_plan_wf_ground_action:
    fixes \<pi>s
    defines "htps \<equiv> htps_exec \<pi>s"
    assumes "wf_plan \<pi>s"
        and "hs = simplify_plan htps \<pi>s"
    shows "\<forall>(t\<^sub>a,A) \<in> set hs. \<forall>a \<in> set A. wf_ground_action a"
    using assms simplify_plan_wf_ground_action_aux by (induction hs) auto

  text \<open>Recursive refinement for @{const valid_happ_seq}.\<close>
  fun valid_happ_seq_from :: "world_model \<Rightarrow> happening list \<Rightarrow> bool" where
    "valid_happ_seq_from s [] \<longleftrightarrow> close_world s \<TTurnstile> (goal P)"
  | "valid_happ_seq_from s (h#hs) \<longleftrightarrow> 
    (happ_enabled h s \<and> valid_happ_seq_from (apply_happ_exec h s) hs)"

  text \<open>Justification of the refinement for @{const valid_happ_seq}.\<close>
  lemma valid_happ_seq_from_refine: 
    assumes "wf_happ_seq hs"
    shows "valid_happ_seq_from M hs \<longleftrightarrow> (\<exists>M'. valid_happ_seq M hs M' \<and> M' \<^sup>c\<TTurnstile>\<^sub>= (goal P))"
    using assms apply_happ_exec_refine
    by (induction hs arbitrary: M) (auto split: prod.splits simp: pairwise_def)

  definition mp_Fevl :: "(object, rat) mapping" where
    "mp_Fevl = Mapping.of_alist (fold (\<lambda>a fev. case a of Atom (eqAtm f (TimeEnt t)) \<Rightarrow> (f,t)#fev | _ \<Rightarrow> fev) (init P) [])"

  lemma mp_func_eval_correct[simp]: "Mapping.lookup mp_Fevl = func_eval"
    unfolding mp_Fevl_def func_eval_def by transfer (simp add: Map_To_Mapping.map_apply_def)

  fun duration_matches' :: "(object, rat) mapping \<Rightarrow> time \<Rightarrow> term duration_constraint \<Rightarrow> (variable \<times> type) list \<Rightarrow> object list \<Rightarrow> bool" where
    "duration_matches' mp_fe d No_Const params args \<longleftrightarrow> d \<ge> 0"
  | "duration_matches' mp_fe d (Time_Const op d') params args \<longleftrightarrow> 
      (case op of
        LEQ \<Rightarrow> d \<le> d'
      | EQ \<Rightarrow> d = d'
      | GEQ \<Rightarrow> d \<ge> d')"
  | "duration_matches' mp_fe d (Func_Const op f vs) params args \<longleftrightarrow> 
      (let tsubst = subst_term (the o (map_of (zip (map fst params) args))) in
        case Mapping.lookup mp_fe (FuncEnt f (map tsubst vs)) of 
          None \<Rightarrow> False 
        | Some d' \<Rightarrow> (case op of
            LEQ \<Rightarrow> d \<le> d'
          | EQ \<Rightarrow> d = d'
          | GEQ \<Rightarrow> d \<ge> d'))"

  lemma (in wf_ast_problem) duration_matches'_correct:    
    "duration_matches' mp_Fevl d dc params args \<longleftrightarrow> duration_matches d dc params args"
    by (cases dc) (auto split: option.splits)
  
  definition "durations_match' mp_fe d xs params args = list_all (\<lambda>x. duration_matches' mp_fe d x params args) xs"

  lemma (in wf_ast_problem) durations_match'_correct:    
    "durations_match' mp_Fevl d dcs params args \<longleftrightarrow> durations_match d dcs params args"
    unfolding durations_match_def durations_match'_def using duration_matches'_correct by simp

  fun consec_htps_in_interval_exec :: "time list \<Rightarrow> time \<Rightarrow> time \<Rightarrow> (time \<times> time) list" where
    "consec_htps_in_interval_exec (t#t'#ts) t\<^sub>i t\<^sub>j = 
    (if t < t\<^sub>i then consec_htps_in_interval_exec (t'#ts) t\<^sub>i t\<^sub>j
    else if t\<^sub>i \<le> t \<and> t' \<le> t\<^sub>j then (t,t')#(consec_htps_in_interval_exec (t'#ts) t\<^sub>i t\<^sub>j)
    else [])"
  | "consec_htps_in_interval_exec ts t\<^sub>i t\<^sub>j = []"

  lemma consec_htps_in_interval_exec_correct: 
    assumes "strict_sorted ts"
    shows "consec_htps_in_interval ts t\<^sub>i t\<^sub>j = consec_htps_in_interval_exec ts t\<^sub>i t\<^sub>j"
    unfolding consec_htps_in_interval_def
    using assms
  proof (induction ts t\<^sub>i t\<^sub>j rule: consec_htps_in_interval_exec.induct)
    case (1 t t' ts t\<^sub>i t\<^sub>j)
    have "t < t\<^sub>i \<or> (t\<^sub>i \<le> t \<and> t' \<le> t\<^sub>j) \<or> (t\<^sub>i \<le> t \<and> t\<^sub>j < t')"
      by auto
    then show ?case 
    proof (elim disjE)
      assume "t < t\<^sub>i"
      then show ?case
        using "1.prems" "1.IH" by auto
    next
      assume "t\<^sub>i \<le> t \<and> t' \<le> t\<^sub>j"
      then show ?case
        using "1.prems" "1.IH" by auto
    next
      assume "t\<^sub>i \<le> t \<and> t\<^sub>j < t'"
      then have "\<forall>(t, t') \<in> set (zip (butlast (t#t'#ts)) (tl (t#t'#ts))). t\<^sub>j < t'"
        using \<open>strict_sorted (t # t' # ts)\<close>
        apply (induction ts)
        apply auto
        apply (metis dual_order.antisym less_eq_rat_def order_trans set_zip_rightD)
        done
      then have "\<not>(\<exists>(t, t') \<in> set (zip (butlast (t#t'#ts)) (tl (t#t'#ts))). t\<^sub>i \<le> t \<and> t' \<le> t\<^sub>j)"
        by fastforce
      then have "filter (\<lambda>(t, t'). t\<^sub>i \<le> t \<and> t' \<le> t\<^sub>j) (zip (t' # butlast ts) ts) = []"
        by (induction ts) auto
      then show ?case
        using "1.prems" "1.IH" 
        by auto
    qed
  next
    case ("2_1" t\<^sub>i t\<^sub>j)
    then show ?case by auto
  next
    case ("2_2" v t\<^sub>i t\<^sub>j)
    then show ?case by auto
  qed

  fun place_inv_snap_acts :: "time list \<Rightarrow> time \<Rightarrow> time \<Rightarrow> ground_action \<Rightarrow> (time \<times> ground_action) list" where
    "place_inv_snap_acts (t#t'#ts) t\<^sub>i t\<^sub>j a\<^sub>i\<^sub>n\<^sub>v = 
    (if t < t\<^sub>i then place_inv_snap_acts (t'#ts) t\<^sub>i t\<^sub>j a\<^sub>i\<^sub>n\<^sub>v
    else if t\<^sub>i \<le> t \<and> t' \<le> t\<^sub>j then ((t+t') div 2,a\<^sub>i\<^sub>n\<^sub>v)#(place_inv_snap_acts (t'#ts) t\<^sub>i t\<^sub>j a\<^sub>i\<^sub>n\<^sub>v)
    else [])"
  | "place_inv_snap_acts ts t\<^sub>i t\<^sub>j a\<^sub>i\<^sub>n\<^sub>v = []"
  (* TODO: performance optimization with Binary Search *)

  lemma place_inv_snap_acts_correct:
    assumes "strict_sorted ts"
    shows "place_inv_snap_acts ts t\<^sub>1 t\<^sub>2 a\<^sub>i\<^sub>n\<^sub>v = map (\<lambda>(t\<^sub>i,t\<^sub>j).((t\<^sub>i+t\<^sub>j) div 2,a\<^sub>i\<^sub>n\<^sub>v)) (consec_htps_in_interval ts t\<^sub>1 t\<^sub>2)"
    using assms consec_htps_in_interval_exec_correct
    by (induction ts t\<^sub>1 t\<^sub>2 a\<^sub>i\<^sub>n\<^sub>v rule: place_inv_snap_acts.induct) auto

  (* Tail-recursive performance test *)
  (*fun place_inv_snap_acts_acc :: "time list \<Rightarrow> time \<Rightarrow> time \<Rightarrow> ground_action \<Rightarrow> (time \<times> ground_action) list \<Rightarrow> (time \<times> ground_action) list" where
    "place_inv_snap_acts_acc (t#t'#ts) t\<^sub>i t\<^sub>j a\<^sub>i\<^sub>n\<^sub>v acc = 
    (if t < t\<^sub>i then place_inv_snap_acts_acc (t'#ts) t\<^sub>i t\<^sub>j a\<^sub>i\<^sub>n\<^sub>v acc
    else if t\<^sub>i \<le> t \<and> t' \<le> t\<^sub>j then place_inv_snap_acts_acc (t'#ts) t\<^sub>i t\<^sub>j a\<^sub>i\<^sub>n\<^sub>v (((t+t') div 2,a\<^sub>i\<^sub>n\<^sub>v)#acc)
    else acc)"
  | "place_inv_snap_acts_acc ts t\<^sub>i t\<^sub>j a\<^sub>i\<^sub>n\<^sub>v acc = acc"

  lemma place_inv_snap_acts_acc_correct:
    assumes "strict_sorted ts"
    shows "place_inv_snap_acts_acc ts t\<^sub>1 t\<^sub>2 a\<^sub>i\<^sub>n\<^sub>v acc = rev (place_inv_snap_acts ts t\<^sub>1 t\<^sub>2 a\<^sub>i\<^sub>n\<^sub>v) @ acc"
    using assms
    by (induction ts t\<^sub>1 t\<^sub>2 a\<^sub>i\<^sub>n\<^sub>v acc arbitrary: acc rule: place_inv_snap_acts_acc.induct) (auto split: if_splits)*)

  text \<open>Lift @{const simplify_action} into an Error Monad.\<close>
  fun simplify_actionE :: "_ \<Rightarrow> (object, type) mapping \<Rightarrow> (object, rat) mapping \<Rightarrow> time list \<Rightarrow> (time \<times> plan_action) \<Rightarrow> _+(time \<times> ground_action) list" where
    "simplify_actionE stg mp mp_fe htps (t\<^sub>\<pi>,Simple_Plan_Action n args) = do {
      check (t\<^sub>\<pi> \<ge> 0) (ERRS ''Invalid starting time point'');
      a \<leftarrow> resolve_action_schemaE n;
      check (case a of Simple_Action_Schema _ _ _ _ \<Rightarrow> True | _ \<Rightarrow> False) (ERRS ''Invalid Plan action type'');
      check (action_params_match2 stg mp a args) (ERRS ''Parameter mismatch'');
      Error_Monad.return [(t\<^sub>\<pi>,instantiate_action_schema a args At_Start)]
    }"
  | "simplify_actionE stg mp mp_fe htps (t\<^sub>\<pi>,Durative_Plan_Action n args d) = do {
      check (t\<^sub>\<pi> \<ge> 0) (ERRS ''Invalid starting time point'');
      a \<leftarrow> resolve_action_schemaE n;
      check (case a of Durative_Action_Schema _ _ _ _ _ \<Rightarrow> True | _ \<Rightarrow> False) (ERRS ''Invalid Plan action type'');
      check (action_params_match2 stg mp a args) (ERRS ''Parameter mismatch'');
      check (d \<ge> 0) (ERRS ''Invalid duration (negative)'');
      check (durations_match' mp_fe d (duration_constraint a) (parameters a) args) (ERRS ''Duration constraint not satisfied'');
      let a\<^sub>i\<^sub>n\<^sub>v = inst_snap_action a args Over_All in
        Error_Monad.return (
          (t\<^sub>\<pi>,inst_snap_action a args At_Start) # 
          (t\<^sub>\<pi>+d,inst_snap_action a args At_End) # 
          (place_inv_snap_acts htps t\<^sub>\<pi> (t\<^sub>\<pi>+d) a\<^sub>i\<^sub>n\<^sub>v)
        )
    }"

  text \<open>Justification of refinement for @{const simplify_action}.\<close>
  lemma (in wf_ast_problem) simplify_actionE_return_iff:
    assumes "wf_domain" and "strict_sorted htps"
    shows "simplify_actionE STG mp_objT mp_Fevl htps (t\<^sub>\<pi>,\<pi>) = Inr as 
      \<longleftrightarrow> (wf_plan_action \<pi> \<and> t\<^sub>\<pi> \<ge> 0 \<and> simplify_action htps (t\<^sub>\<pi>,\<pi>) = as)"
  proof
    assume assm1: "simplify_actionE STG mp_objT mp_Fevl htps (t\<^sub>\<pi>,\<pi>) = Inr as"
    obtain a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a where a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a_obt: "Some a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a = resolve_action_schema (name \<pi>)"
      using assm1 resolve_action_schema_def
      unfolding wf_domain_def by (cases \<pi>) (auto simp: return_iff)
    then have wf_act_schema_\<pi>: "wf_action_schema (the (resolve_action_schema (name \<pi>)))"
      using assms a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a_obt 
            resolve_action_schema_def 
            index_by_eq_SomeD[where n="name \<pi>" and x="a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a"]
      unfolding wf_domain_def by (metis option.sel)
    then show "wf_plan_action \<pi> \<and> t\<^sub>\<pi> \<ge> 0 \<and> simplify_action htps (t\<^sub>\<pi>,\<pi>) = as"
    proof (cases \<pi>)
      case case_\<pi>: (Simple_Plan_Action n args)
      obtain a where a_obt: "a = instantiate_action_schema a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a args At_Start\<and> as = [(t\<^sub>\<pi>,a)]"
        using assm1 a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a_obt case_\<pi> by (auto simp: return_iff)
      have wf_p_act: "wf_plan_action \<pi> \<and> t\<^sub>\<pi> \<ge> 0"
        using assm1 wf_act_schema_\<pi> case_\<pi> action_params_match_def wf_effect_inst_weak
        apply (auto simp: return_iff split: option.splits ast_action_schema.splits)
        apply (meson ast_action_schema.exhaust)+
        done
      show ?thesis 
        using a_obt a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a_obt case_\<pi> wf_p_act
        by (auto split: option.splits ast_action_schema.splits)
    next
      case case_\<pi>: (Durative_Plan_Action n args d)
      show ?thesis 
        using assm1 wf_act_schema_\<pi> case_\<pi> action_params_match_def 
              wf_effect_durative_inst_weak 
              durations_match'_correct 
              place_inv_snap_acts_correct[OF \<open>strict_sorted htps\<close>]
        apply (auto simp: return_iff split: ast_action_schema.splits)
        apply (auto simp: return_iff split: option.splits)
        apply (meson ast_action_schema.exhaust)+
        done
    qed
  next
    assume assm2: "wf_plan_action \<pi> \<and> t\<^sub>\<pi> \<ge> 0 \<and> simplify_action htps (t\<^sub>\<pi>,\<pi>) = as"
    obtain a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a where a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a_obt: "Some a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a = resolve_action_schema (name \<pi>)"
      using assm2 by (cases \<pi>) (auto split: option.splits)
    then show "simplify_actionE STG mp_objT mp_Fevl htps (t\<^sub>\<pi>,\<pi>) = Inr as"
      using assm2 action_params_match_def 
            durations_match'_correct 
            place_inv_snap_acts_correct[OF \<open>strict_sorted htps\<close>]
      by (cases \<pi>) (auto simp: return_iff split: option.splits ast_action_schema.splits)
  qed

  text \<open>Lift @{const simplify_plan} into an Error Monad.\<close>  
  fun simplify_planE :: "_ \<Rightarrow> (object, type) mapping \<Rightarrow> (object, rat) mapping \<Rightarrow> time list \<Rightarrow> plan \<Rightarrow> _+happening list" where
    "simplify_planE stg mp mp_fe htps [] = do { 
      Error_Monad.return [] 
    }" 
  | "simplify_planE stg mp mp_fe htps (\<pi>#\<pi>s) = do {
      as \<leftarrow> simplify_actionE stg mp mp_fe htps \<pi>;
      hs \<leftarrow> simplify_planE stg mp mp_fe htps \<pi>s;
      Error_Monad.return (insort_timed_ground_acts as hs)
    }"

  text \<open>Justification of refinement for @{const simplify_plan}\<close>
  lemma (in wf_ast_problem) simplify_planE_return_iff[return_iff]: 
    assumes "wf_domain" and "strict_sorted htps"
    shows "simplify_planE STG mp_objT mp_Fevl htps \<pi>s = Inr hs 
            \<longleftrightarrow> (simplify_plan htps \<pi>s = hs \<and> wf_plan \<pi>s)"
    using assms simplify_actionE_return_iff wf_plan_def insort_timed_ground_acts_correct
    by (induction \<pi>s arbitrary: hs) (auto simp: return_iff)

  (* Attempt to increase performance by implementing @{const simplify_plan} with an AVL tree *)
  type_synonym 'a tree_ht = "('a \<times> nat) tree"

  fun avl_height :: "happening tree_ht \<Rightarrow> nat" where
    "avl_height \<langle>\<rangle> = 0" 
  | "avl_height \<langle>l,((t,as),ht),r\<rangle> = ht"

  definition avl_node :: "happening tree_ht \<Rightarrow> happening \<Rightarrow> happening tree_ht \<Rightarrow> happening tree_ht" where
    "avl_node l h r = \<langle>l,(h,(max (avl_height l) (avl_height r) + 1)),r\<rangle>"

  definition avl_balL :: "happening tree_ht \<Rightarrow> happening \<Rightarrow> happening tree_ht \<Rightarrow> happening tree_ht" where
    "avl_balL l a r =
      (if avl_height l = avl_height r + 2 then
        case l of \<langle>bl,(b,_),br\<rangle> \<Rightarrow>
            if avl_height bl < avl_height br then
              case br of \<langle>cl,(c,_),cr\<rangle> \<Rightarrow> avl_node (avl_node bl b cl) c (avl_node cr a r )
            else avl_node bl b (avl_node br a r)
       else avl_node l a r)"

  definition avl_balR :: "happening tree_ht \<Rightarrow> happening \<Rightarrow> happening tree_ht \<Rightarrow> happening tree_ht" where
    "avl_balR l a r =
      (if avl_height r = avl_height l + 2 then
        case r of \<langle>bl,(b,_),br\<rangle> \<Rightarrow>
          if avl_height bl > avl_height br then
            case bl of \<langle>cl,(c,_),cr\<rangle> \<Rightarrow> avl_node (avl_node l a cl) c (avl_node cr b br)
          else avl_node (avl_node l a bl) b br
      else avl_node l a r)"

  fun insert_happ_to_tree :: "happening \<Rightarrow> happening tree_ht \<Rightarrow> happening tree_ht" where
    "insert_happ_to_tree (t\<^sub>i,A\<^sub>i) \<langle>\<rangle> = avl_node \<langle>\<rangle> (t\<^sub>i,A\<^sub>i) \<langle>\<rangle>"
  | "insert_happ_to_tree (t\<^sub>i,A\<^sub>i) \<langle>l,((t\<^sub>j,A\<^sub>j),h),r\<rangle> = (
    if t\<^sub>i < t\<^sub>j then avl_balL (insert_happ_to_tree (t\<^sub>i,A\<^sub>i) l) (t\<^sub>j,A\<^sub>j) r
    else if t\<^sub>i = t\<^sub>j then avl_node l (t\<^sub>j,A\<^sub>i @ A\<^sub>j) r
    else avl_balR l (t\<^sub>j,A\<^sub>j) (insert_happ_to_tree (t\<^sub>i,A\<^sub>i) r))"

  fun insert_timed_ground_acts_to_tree :: "(time \<times> ground_action) list \<Rightarrow> happening tree_ht \<Rightarrow> happening tree_ht" where
    "insert_timed_ground_acts_to_tree [] htree = htree"
  | "insert_timed_ground_acts_to_tree ((t\<^sub>a,a)#as) htree = 
    insert_happ_to_tree (t\<^sub>a,[a]) (insert_timed_ground_acts_to_tree as htree)"

  definition avl_inorder :: "happening tree_ht \<Rightarrow> happening list" where 
    "avl_inorder htree = map fst (inorder htree)"

  fun simplify_planE_avl' :: "_ \<Rightarrow> (object, type) mapping \<Rightarrow> (object, rat) mapping \<Rightarrow> time list \<Rightarrow> plan \<Rightarrow> _+happening tree_ht" where
    "simplify_planE_avl' G mp mp_fe htps [] = do { 
      Error_Monad.return \<langle>\<rangle>
    }" 
  | "simplify_planE_avl' G mp mp_fe htps (\<pi>#\<pi>s) = do {
      as \<leftarrow> simplify_actionE G mp mp_fe htps \<pi>;
      htree \<leftarrow> simplify_planE_avl' G mp mp_fe htps \<pi>s;
      Error_Monad.return (insert_timed_ground_acts_to_tree as htree)
    }"

  fun simplify_planE_avl :: "_ \<Rightarrow> (object, type) mapping \<Rightarrow> (object, rat) mapping \<Rightarrow> time list \<Rightarrow> plan \<Rightarrow> _+happening list" where
    "simplify_planE_avl G mp mp_fe htps \<pi>s = do { 
      htree \<leftarrow> simplify_planE_avl' G mp mp_fe htps \<pi>s;
      Error_Monad.return (avl_inorder htree)
    }"

  lemma insort_happ_consL:
    assumes "\<forall>(t\<^sub>j,A\<^sub>j) \<in> set hs\<^sub>1. t\<^sub>j < t\<^sub>i"
    shows "hs\<^sub>1 @ (insort_happ (t\<^sub>i,A\<^sub>i) hs\<^sub>2) = insort_happ (t\<^sub>i,A\<^sub>i) (hs\<^sub>1 @ hs\<^sub>2)"
    using assms by (induction hs\<^sub>1 arbitrary: t\<^sub>i A\<^sub>i hs\<^sub>2) auto

  lemma insort_happ_consR:
    assumes "\<forall>(t\<^sub>j,A\<^sub>j) \<in> set hs\<^sub>2. t\<^sub>i < t\<^sub>j"
    shows "(insort_happ (t\<^sub>i,A\<^sub>i) hs\<^sub>1) @ hs\<^sub>2 = insort_happ (t\<^sub>i,A\<^sub>i) (hs\<^sub>1 @ hs\<^sub>2)"
    using assms
  proof (induction hs\<^sub>2 arbitrary: t\<^sub>i A\<^sub>i hs\<^sub>1)
    case Nil
    then show ?case by auto
  next
    case (Cons h hs\<^sub>2)
    then show ?case by (induction hs\<^sub>1) auto
  qed

  lemma inorder_avl_balL: "avl_inorder (avl_balL l a r) = avl_inorder l @ a # avl_inorder r"
    unfolding avl_inorder_def avl_node_def avl_balL_def by (auto split: tree.splits)

  lemma inorder_avl_balR: "avl_inorder (avl_balR l a r) = avl_inorder l @ a # avl_inorder r"
    unfolding avl_inorder_def avl_node_def avl_balR_def by (auto split: tree.splits)

  (*lemma strict_sorted_app: "strict_sorted (a @ b) \<Longrightarrow> strict_sorted a \<and> strict_sorted b"
    by (induction a arbitrary: b) auto*)

  lemma strict_sorted_appl: "strict_sorted (a @ [y]) \<Longrightarrow> \<forall>x \<in> set a. x < y"
    by (induction a) auto

  lemma strict_sorted_consg: "strict_sorted (y # a) \<Longrightarrow> \<forall>x \<in> set a. y < x"
    by (induction a) auto

  lemma strict_sorted_avl_inorder_l:
    assumes "strict_sorted (map fst (avl_inorder \<langle>l, ((t\<^sub>i, A\<^sub>i), h), r\<rangle>))"
    shows "\<forall>(t\<^sub>j, A\<^sub>j) \<in> set (avl_inorder l). t\<^sub>j < t\<^sub>i"
  proof -
    have "strict_sorted (map fst (avl_inorder l) @ [t\<^sub>i])"
      using assms strict_sorted_app_iff[where a="map fst (avl_inorder l) @ [t\<^sub>i]"] 
      by (auto simp: avl_inorder_def)
    then show ?thesis
      using strict_sorted_appl[OF \<open>strict_sorted (map fst (avl_inorder l) @ [t\<^sub>i])\<close>] by auto
  qed

  lemma strict_sorted_avl_inorder_r:
    assumes "strict_sorted (map fst (avl_inorder \<langle>l, ((t\<^sub>i, A\<^sub>i), h), r\<rangle>))"
    shows "\<forall>(t\<^sub>j, A\<^sub>j) \<in> set (avl_inorder r). t\<^sub>i < t\<^sub>j"
  proof -
    have "strict_sorted (t\<^sub>i # map fst (avl_inorder r))"
      using assms strict_sorted_app_iff[where b="t\<^sub>i # map fst (avl_inorder r)"] 
      by (auto simp: avl_inorder_def)
    then show ?thesis
      using strict_sorted_consg[OF \<open>strict_sorted (t\<^sub>i # map fst (avl_inorder r))\<close>] by auto
  qed

  lemma insert_happ_to_tree_set:
    assumes "strict_sorted (map fst (avl_inorder htree))"
    shows "set (map fst (avl_inorder (insert_happ_to_tree (t\<^sub>i,A\<^sub>i) htree))) = set (map fst (avl_inorder htree)) \<union> {t\<^sub>i}"
    using assms
  proof (induction "(t\<^sub>i,A\<^sub>i)" htree rule: insert_happ_to_tree.induct)
    case 1
    then show ?case by (auto simp: avl_inorder_def avl_node_def)
  next
    case (2 l t\<^sub>j A\<^sub>j h r)
    then have "strict_sorted (map fst (avl_inorder \<langle>l, ((t\<^sub>j, A\<^sub>j), h), r\<rangle>))"
      by auto
    then have "strict_sorted (map fst (avl_inorder l @ (t\<^sub>j, A\<^sub>j) #  avl_inorder r))"
      unfolding avl_inorder_def by auto
    then have "strict_sorted (map fst (avl_inorder l) @ t\<^sub>j # map fst (avl_inorder r))"
          and "strict_sorted (map fst (avl_inorder l) @ [t\<^sub>j] @ map fst (avl_inorder r))"
      by auto
    then have "strict_sorted (map fst (avl_inorder l))" 
          and "strict_sorted (map fst (avl_inorder r))"
      using strict_sorted_app_iff[where a="map fst (avl_inorder l)" and b="t\<^sub>j # map fst (avl_inorder r)"]            
            strict_sorted_app_iff[where a="map fst (avl_inorder l) @ [t\<^sub>j]" and b="map fst (avl_inorder r)"]
      by auto
    have "t\<^sub>i < t\<^sub>j \<or> t\<^sub>i = t\<^sub>j \<or> t\<^sub>j < t\<^sub>i"
      by auto
    then show ?case
    proof (elim disjE)
      assume "t\<^sub>i < t\<^sub>j"
      then show ?case
        using inorder_avl_balL \<open>strict_sorted (map fst (avl_inorder l))\<close> "2.hyps" by (auto simp: avl_inorder_def)
    next
      assume "t\<^sub>i = t\<^sub>j"
      then show ?case
        by (auto simp: avl_inorder_def avl_node_def)
    next
      assume "t\<^sub>j < t\<^sub>i"                                
      then show ?case
        using inorder_avl_balR \<open>strict_sorted (map fst (avl_inorder r))\<close> "2.hyps" by (auto simp: avl_inorder_def)
    qed
  qed

  lemma insert_timed_ground_act_to_tree_strict_sorted: 
    assumes "strict_sorted (map fst (avl_inorder htree))"
    shows "strict_sorted (map fst (avl_inorder (insert_happ_to_tree h htree)))"
    using assms
  proof (induction h htree rule: insert_happ_to_tree.induct)
    case (1 t\<^sub>i A\<^sub>i)
    then show ?case 
      by (auto simp: avl_node_def avl_inorder_def)                                                                                         
  next
    case (2 t\<^sub>i A\<^sub>i l t\<^sub>j A\<^sub>j h r)
    then have "strict_sorted (map fst (avl_inorder \<langle>l, ((t\<^sub>j, A\<^sub>j), h), r\<rangle>))"
      by auto
    then have "strict_sorted (map fst (avl_inorder l @ (t\<^sub>j, A\<^sub>j) # avl_inorder r))"
      unfolding avl_inorder_def by auto
    then have "strict_sorted (map fst (avl_inorder l) @ t\<^sub>j # map fst (avl_inorder r))"
          and "strict_sorted (map fst (avl_inorder l) @ [t\<^sub>j] @ map fst (avl_inorder r))"
      by auto
    then have "strict_sorted (map fst (avl_inorder l))" 
          and "strict_sorted (map fst (avl_inorder l @ [(t\<^sub>j,A\<^sub>j)]))"
          and "strict_sorted (map fst (avl_inorder r))"
          and "strict_sorted (map fst ((t\<^sub>j,A\<^sub>j) # avl_inorder r))"
      using strict_sorted_app_iff[where a="map fst (avl_inorder l)" and b="t\<^sub>j # map fst (avl_inorder r)"]            
            strict_sorted_app_iff[where a="map fst (avl_inorder l) @ [t\<^sub>j]" and b="map fst (avl_inorder r)"]
      by auto
    have "t\<^sub>i < t\<^sub>j \<or> t\<^sub>i = t\<^sub>j \<or> t\<^sub>j < t\<^sub>i"
      by auto
    then show ?case
    proof (elim disjE)
      assume "t\<^sub>i < t\<^sub>j"
      then have "strict_sorted (map fst (avl_inorder (insert_happ_to_tree (t\<^sub>i,A\<^sub>i) l)))"
        using \<open>strict_sorted (map fst (avl_inorder l))\<close> "2.IH" by auto

      have "strict_sorted (map fst (avl_inorder l) @ map fst ((t\<^sub>j, A\<^sub>j) # avl_inorder r))"
        using \<open>strict_sorted (map fst (avl_inorder l @ (t\<^sub>j, A\<^sub>j) # avl_inorder r))\<close> by auto
      then have "\<forall>x \<in> set (map fst (avl_inorder l)). \<forall>y \<in> set (map fst ((t\<^sub>j, A\<^sub>j) # avl_inorder r)). x < y"
        using strict_sorted_app_iff[where a="map fst (avl_inorder l)" and b="map fst ((t\<^sub>j, A\<^sub>j) # avl_inorder r)"] 
        by auto
      then have "\<forall>x \<in> set (map fst (avl_inorder l)) \<union> {t\<^sub>i}. \<forall>y \<in> set (map fst ((t\<^sub>j, A\<^sub>j) # avl_inorder r)). x < y"
        using \<open>t\<^sub>i < t\<^sub>j\<close> strict_sorted_avl_inorder_r[OF \<open>strict_sorted (map fst (avl_inorder \<langle>l, ((t\<^sub>j, A\<^sub>j), h), r\<rangle>))\<close>] by auto
      then have "\<forall>x \<in> set (map fst (avl_inorder (insert_happ_to_tree (t\<^sub>i,A\<^sub>i) l))). \<forall>y \<in> set (map fst ((t\<^sub>j, A\<^sub>j) # avl_inorder r)). x < y"
        using insert_happ_to_tree_set[OF \<open>strict_sorted (map fst (avl_inorder l))\<close>] by auto
      then have "strict_sorted (map fst (avl_inorder (insert_happ_to_tree (t\<^sub>i,A\<^sub>i) l) @ (t\<^sub>j,A\<^sub>j) # avl_inorder r))"
        using \<open>strict_sorted (map fst (avl_inorder (insert_happ_to_tree (t\<^sub>i,A\<^sub>i) l)))\<close>
              \<open>strict_sorted (map fst ((t\<^sub>j,A\<^sub>j) # avl_inorder r))\<close>
              strict_sorted_app_iff[where a="map fst (avl_inorder (insert_happ_to_tree (t\<^sub>i,A\<^sub>i) l))" and b="map fst ((t\<^sub>j, A\<^sub>j) # avl_inorder r)"] 
        by auto
      then have "strict_sorted (map fst (avl_inorder (avl_balL (insert_happ_to_tree (t\<^sub>i,A\<^sub>i) l) (t\<^sub>j,A\<^sub>j) r)))"
        using inorder_avl_balL by auto
      then have "strict_sorted (map fst (avl_inorder (insert_happ_to_tree (t\<^sub>i, A\<^sub>i) \<langle>l, ((t\<^sub>j, A\<^sub>j), h), r\<rangle>)))"
        using \<open>t\<^sub>i < t\<^sub>j\<close> by auto
      then show ?case
        by auto
    next
      assume "t\<^sub>i = t\<^sub>j"
      then show ?case
        using "2.prems" by (auto simp: avl_inorder_def avl_node_def)
    next
      assume "t\<^sub>j < t\<^sub>i"
      then have "strict_sorted (map fst (avl_inorder (insert_happ_to_tree (t\<^sub>i,A\<^sub>i) r)))"
        using \<open>strict_sorted (map fst (avl_inorder r))\<close> "2.IH" by auto

      have "strict_sorted (map fst (avl_inorder l @ [(t\<^sub>j, A\<^sub>j)]) @ map fst (avl_inorder r))"
        using \<open>strict_sorted (map fst (avl_inorder l @ (t\<^sub>j, A\<^sub>j) # avl_inorder r))\<close> by auto
      then have "\<forall>x \<in> set (map fst (avl_inorder l @ [(t\<^sub>j, A\<^sub>j)])). \<forall>y \<in> set (map fst (avl_inorder r)). x < y"
        using strict_sorted_app_iff[where a="map fst (avl_inorder l @ [(t\<^sub>j, A\<^sub>j)])" and b="map fst (avl_inorder r)"] 
        by auto
      then have "\<forall>x \<in> set (map fst (avl_inorder l @ [(t\<^sub>j, A\<^sub>j)])). \<forall>y \<in> set (map fst (avl_inorder r)) \<union> {t\<^sub>i}. x < y"
        using \<open>t\<^sub>j < t\<^sub>i\<close> strict_sorted_avl_inorder_l[OF \<open>strict_sorted (map fst (avl_inorder \<langle>l, ((t\<^sub>j, A\<^sub>j), h), r\<rangle>))\<close>] by auto
      then have "\<forall>x \<in> set (map fst (avl_inorder l @ [(t\<^sub>j, A\<^sub>j)])). \<forall>y \<in> set (map fst (avl_inorder (insert_happ_to_tree (t\<^sub>i,A\<^sub>i) r))). x < y"
        using insert_happ_to_tree_set[OF \<open>strict_sorted (map fst (avl_inorder r))\<close>] by auto
      then have "strict_sorted (map fst (avl_inorder l @ (t\<^sub>j,A\<^sub>j) # avl_inorder (insert_happ_to_tree (t\<^sub>i,A\<^sub>i) r)))"
        using \<open>strict_sorted (map fst (avl_inorder l @ [(t\<^sub>j,A\<^sub>j)]))\<close>
              \<open>strict_sorted (map fst (avl_inorder (insert_happ_to_tree (t\<^sub>i,A\<^sub>i) r)))\<close>
              strict_sorted_app_iff[where a="map fst (avl_inorder l @ [(t\<^sub>j,A\<^sub>j)])" and b="map fst (avl_inorder (insert_happ_to_tree (t\<^sub>i,A\<^sub>i) r))"] 
        by auto
      then have "strict_sorted (map fst (avl_inorder (avl_balR l (t\<^sub>j,A\<^sub>j) (insert_happ_to_tree (t\<^sub>i,A\<^sub>i) r))))"
        using inorder_avl_balR by auto
      then have "strict_sorted (map fst (avl_inorder (insert_happ_to_tree (t\<^sub>i, A\<^sub>i) \<langle>l, ((t\<^sub>j, A\<^sub>j), h), r\<rangle>)))"
        using \<open>t\<^sub>j < t\<^sub>i\<close> by auto
      then show ?case
        by auto
    qed
  qed

  lemma insert_timed_ground_acts_to_tree_strict_sorted: 
    assumes "strict_sorted (map fst (avl_inorder htree))"
    shows "strict_sorted (map fst (avl_inorder (insert_timed_ground_acts_to_tree as htree)))"
    using assms insert_timed_ground_act_to_tree_strict_sorted
    by (induction as) auto

  (* TODO: clean up proof *)
  lemma insert_happ_to_tree_equiv: 
    assumes "strict_sorted (map fst (avl_inorder htree))"
    shows "avl_inorder (insert_happ_to_tree (t\<^sub>i,A\<^sub>i) htree) = insort_happ (t\<^sub>i,A\<^sub>i) (avl_inorder htree)"
    using assms
  proof (induction htree)
    case Leaf
    then show ?case
      by (auto simp: avl_node_def avl_inorder_def)
  next
    case (Node l a r)
    show ?case 
    proof (cases a)
      case (Pair a' ht)
        then have "\<langle>l,a,r\<rangle> = \<langle>l,(a',ht),r\<rangle>"
          by auto
        show ?thesis
          proof (cases a')
            case (Pair t\<^sub>j A\<^sub>j)
            then have "\<langle>l,a,r\<rangle> = \<langle>l,((t\<^sub>j,A\<^sub>j),ht),r\<rangle>"
              using \<open>\<langle>l,a,r\<rangle> = \<langle>l,(a',ht),r\<rangle>\<close> by auto
            then have "avl_inorder \<langle>l,a,r\<rangle> = avl_inorder l @ (t\<^sub>j,A\<^sub>j) # avl_inorder r"
              unfolding avl_inorder_def by auto
            then have "strict_sorted (map fst (avl_inorder l @ (t\<^sub>j,A\<^sub>j) # avl_inorder r))"
              using Node.prems by auto
            then have "strict_sorted (map fst (avl_inorder l @ [(t\<^sub>j,A\<^sub>j)]) @ map fst (avl_inorder r))"
                  and "strict_sorted (map fst (avl_inorder l) @ map fst ((t\<^sub>j,A\<^sub>j) # avl_inorder r))"
              by auto
            then have "strict_sorted (map fst (avl_inorder l @ [(t\<^sub>j,A\<^sub>j)]))" 
                  and "strict_sorted (map fst (avl_inorder l))"
                  and "strict_sorted (map fst ((t\<^sub>j,A\<^sub>j) # avl_inorder r))"
                  and "strict_sorted (map fst (avl_inorder r))"
              using strict_sorted_app_iff by blast+
            then have "strict_sorted (map fst (avl_inorder l) @ [t\<^sub>j])" 
                  and "strict_sorted (t\<^sub>j # map fst (avl_inorder r))"
              by auto
            then have "\<forall>(t\<^sub>k,A\<^sub>k) \<in> set (avl_inorder l). t\<^sub>k < t\<^sub>j" 
                  and "\<forall>(t\<^sub>k,A\<^sub>k) \<in> set (avl_inorder r). t\<^sub>j < t\<^sub>k"
              using strict_sorted_appl[OF \<open>strict_sorted (map fst (avl_inorder l) @ [t\<^sub>j])\<close>] 
                    strict_sorted_consg[OF \<open>strict_sorted (t\<^sub>j # map fst (avl_inorder r))\<close>]
              by auto

            have "t\<^sub>i < t\<^sub>j \<or> t\<^sub>i = t\<^sub>j \<or> t\<^sub>j < t\<^sub>i"
              by auto
            then show ?thesis
            proof (elim disjE)
              assume "t\<^sub>i < t\<^sub>j"
              then have "\<forall>(t\<^sub>k,A\<^sub>k) \<in> set ((t\<^sub>j,A\<^sub>j) # avl_inorder r). t\<^sub>i < t\<^sub>k"
                using \<open>\<forall>(t\<^sub>k,A\<^sub>k) \<in> set (avl_inorder r). t\<^sub>j < t\<^sub>k\<close> by auto
              then show ?thesis
                using \<open>\<langle>l,a,r\<rangle> = \<langle>l,((t\<^sub>j,A\<^sub>j),ht),r\<rangle>\<close> \<open>t\<^sub>i < t\<^sub>j\<close> \<open>strict_sorted (map fst (avl_inorder l))\<close> 
                      Node.IH inorder_avl_balL insort_happ_consR
                by (auto simp: avl_inorder_def)  
            next
              assume "t\<^sub>i = t\<^sub>j"
              have "avl_inorder (insert_happ_to_tree (t\<^sub>i,A\<^sub>i) \<langle>l,a,r\<rangle>) = avl_inorder (avl_node l (t\<^sub>j,A\<^sub>i @ A\<^sub>j) r)"
                using \<open>\<langle>l,a,r\<rangle> = \<langle>l,((t\<^sub>j,A\<^sub>j),ht),r\<rangle>\<close> \<open>t\<^sub>i = t\<^sub>j\<close> by auto
              also have "... = avl_inorder l @ (t\<^sub>j,A\<^sub>i @ A\<^sub>j) # avl_inorder r"
                unfolding \<open>\<langle>l,a,r\<rangle> = \<langle>l,((t\<^sub>j,A\<^sub>j),ht),r\<rangle>\<close> \<open>t\<^sub>i = t\<^sub>j\<close> avl_node_def by (auto simp: avl_inorder_def)   

              also have "... = insort_happ (t\<^sub>i,A\<^sub>i) (avl_inorder l @ [(t\<^sub>j,A\<^sub>j)]) @ avl_inorder r"
                using \<open>t\<^sub>i = t\<^sub>j\<close> insort_happ_consL[OF \<open>\<forall>(t\<^sub>k,A\<^sub>k) \<in> set (avl_inorder l). t\<^sub>k < t\<^sub>j\<close>, where hs\<^sub>2="[(t\<^sub>j,A\<^sub>j)]"] 
                by auto
              also have "... = insort_happ (t\<^sub>i,A\<^sub>i) (avl_inorder \<langle>l,a,r\<rangle>)"
                using \<open>t\<^sub>i = t\<^sub>j\<close> \<open>\<langle>l,a,r\<rangle> = \<langle>l,((t\<^sub>j,A\<^sub>j),ht),r\<rangle>\<close> 
                      insort_happ_consR[OF \<open>\<forall>(t\<^sub>k,A\<^sub>k) \<in> set (avl_inorder r). t\<^sub>j < t\<^sub>k\<close>] 
                by (auto simp: avl_inorder_def)
              finally show ?thesis
                by auto  
            next
              assume "t\<^sub>j < t\<^sub>i"
              then have "\<forall>(t\<^sub>k,A\<^sub>k) \<in> set (avl_inorder l @ [(t\<^sub>j,A\<^sub>j)]). t\<^sub>k < t\<^sub>i"
                using \<open>\<forall>(t\<^sub>k,A\<^sub>k) \<in> set (avl_inorder l). t\<^sub>k < t\<^sub>j\<close> by auto
              then show ?thesis
                using \<open>\<langle>l,a,r\<rangle> = \<langle>l,((t\<^sub>j,A\<^sub>j),ht),r\<rangle>\<close> \<open>t\<^sub>j < t\<^sub>i\<close> \<open>strict_sorted (map fst (avl_inorder r))\<close> 
                      Node.IH inorder_avl_balR 
                      insort_happ_consL[OF \<open>\<forall>(t\<^sub>k,A\<^sub>k) \<in> set (avl_inorder l @ [(t\<^sub>j,A\<^sub>j)]). t\<^sub>k < t\<^sub>i\<close>] 
                by (auto simp: avl_inorder_def)
            qed
          qed
     qed
  qed

  lemma insert_timed_ground_acts_to_tree_equiv:
    assumes "strict_sorted (map fst (avl_inorder htree))"
    shows "insort_timed_ground_acts as (avl_inorder htree) 
            = avl_inorder (insert_timed_ground_acts_to_tree as htree)"
    using assms
  proof (induction as arbitrary: htree)
    case Nil
    then show ?case by auto
  next
    case (Cons a' as)
    then show ?case 
      using insert_happ_to_tree_equiv[OF insert_timed_ground_acts_to_tree_strict_sorted[OF Cons.prems]]
      by (cases a') auto
  qed

  lemma simplify_planE_avl'_strict_sorted:
    assumes "simplify_planE_avl' STG mp_objT mp_Fevl htps \<pi>s = Inr htree" 
    shows "strict_sorted (map fst (avl_inorder htree))"
    using assms
  proof (induction \<pi>s arbitrary: htree)
    case Nil
    then show ?case 
      by (auto simp: avl_inorder_def)
  next
    case (Cons \<pi> \<pi>s)
    then obtain htree' where "simplify_planE_avl' STG mp_objT mp_Fevl htps \<pi>s = Inr htree'"
      by (auto simp: return_iff)
    then show ?case 
      using Cons.prems Cons.IH insert_timed_ground_acts_to_tree_strict_sorted by auto
  qed

  lemma simplify_planE_avl'_equiv: 
    assumes "simplify_planE STG mp_objT mp_Fevl htps \<pi>s = Inr hs" 
        and "simplify_planE_avl' STG mp_objT mp_Fevl htps \<pi>s = Inr htree" 
    shows "hs = avl_inorder htree"
    using assms unfolding avl_inorder_def
  proof (induction \<pi>s arbitrary: hs htree)
    case Nil
    then show ?case by auto
  next
    case (Cons \<pi> \<pi>s)
    then obtain hs' htree' where "simplify_planE STG mp_objT mp_Fevl htps \<pi>s = Inr hs'"
                             and "simplify_planE_avl' STG mp_objT mp_Fevl htps \<pi>s = Inr htree'"
      by (auto simp: return_iff)
    then have "hs' = map fst (inorder htree')"
      using Cons.prems Cons.IH by auto
    then show ?case 
      using Cons.prems 
            insert_timed_ground_acts_to_tree_equiv[OF simplify_planE_avl'_strict_sorted]
            \<open>simplify_planE STG mp_objT mp_Fevl htps \<pi>s = Inr hs'\<close>
            \<open>simplify_planE_avl' STG mp_objT mp_Fevl htps \<pi>s = Inr htree'\<close>
      by (auto simp: avl_inorder_def)
  qed 

  lemma simplify_planE_avl_equiv_Inr: 
    shows "(\<exists>hs. simplify_planE STG mp_objT mp_Fevl htps \<pi>s = Inr hs) 
        \<longleftrightarrow> (\<exists>htree. simplify_planE_avl' STG mp_objT mp_Fevl htps \<pi>s = Inr htree)"
    by (induction \<pi>s) (auto simp: return_iff)

  (* justification for avl-optimization *)
  lemma simplify_planE_avl_equiv: 
    shows "simplify_planE STG mp_objT mp_Fevl htps \<pi>s = Inr hs 
         \<longleftrightarrow> simplify_planE_avl STG mp_objT mp_Fevl htps \<pi>s = Inr hs"
    using simplify_planE_avl'_equiv simplify_planE_avl_equiv_Inr by fastforce

  (* concise lemma for paper *)
  lemma (in wf_ast_problem)
    assumes "wf_domain"
        and "simplify_planE_avl STG mp_objT mp_Fevl (htps_exec \<pi>s) \<pi>s = Inr hs "
    shows "ind_happ_seq \<pi>s hs" and "wf_plan \<pi>s"
    using assms simplify_planE_avl_equiv simplify_planE_return_iff 
          htps_exec_sorted htps_exec_distinct simplify_plan_correct
    by (auto simp: strict_sorted_iff)

  text \<open>Lift @{const valid_happ_seq_from} into an Error Monad, and use efficient 
  happening execution @{const en_exE}\<close> 
  fun valid_happ_seq_fromE :: "nat \<Rightarrow> world_model \<Rightarrow> happening list \<Rightarrow> _+unit" where
    "valid_happ_seq_fromE si s [] = 
      check (holds s (goal P)) (ERRS ''Postcondition does not hold'')"
  | "valid_happ_seq_fromE si s (h#hs) = do {
      s \<leftarrow> en_exE h s <+? (\<lambda>e _. shows ''at step '' o shows si o shows '': '' o e ());
      valid_happ_seq_fromE (si+1) s hs
    }"

  (*fun valid_happ_seq_fromE_avl' :: "nat \<Rightarrow> world_model \<Rightarrow> (happening \<times> nat) tree \<Rightarrow> _+world_model" where
    "valid_happ_seq_fromE_avl' si s \<langle>\<rangle> = 
      Error_Monad.return s"
  | "valid_happ_seq_fromE_avl' si s \<langle>l,((t,as),h),r\<rangle> = do {
      s \<leftarrow> valid_happ_seq_fromE_avl' (si+1) s l;
      s \<leftarrow> en_exE (t,as) s <+? (\<lambda>e _. shows ''at step '' o shows si o shows '': '' o e ());
      valid_happ_seq_fromE_avl' (si+1) s r
    }"*)

  (*fun valid_happ_seq_fromE_avl :: "nat \<Rightarrow> world_model \<Rightarrow> (happening \<times> nat) tree \<Rightarrow> _+unit" where
    "valid_happ_seq_fromE_avl si s htree = do {
      s \<leftarrow> valid_happ_seq_fromE_avl' (si+1) s htree;
      check (holds s (goal P)) (ERRS ''Postcondition does not hold'')}"*)

  text \<open>For the refinement, we need to show that the world models only
    contain atoms, i.e., containing only atoms is an invariant under execution
    of well-formed happenings.\<close>
  lemma (in wf_ast_problem) wf_happ_only_add_atoms:
    assumes "wm_basic s" 
        and "\<forall>a \<in> set as. wf_ground_action a"
    shows "wm_basic (apply_happ_exec (t,as) s)"
    using wf_problem wf_domain
    unfolding wf_problem_def wf_domain_def
    using assms 
          apply_happ_exec_refine 
          wf_fmla_atom_alt 
          wf_ground_action_wf_fmla_atom
    by (auto simp: wm_basic_def) fastforce

  lemma (in wf_ast_problem) wf_happ_only_add_atoms':
    assumes "wf_world_model s" 
        and "\<forall>a \<in> set as. wf_ground_action a"
    shows "wf_world_model (apply_happ_exec (t,as) s)"
    using wf_problem wf_domain
    unfolding wf_problem_def wf_domain_def
    using assms 
          apply_happ_exec_refine 
          wf_fmla_atom_alt 
          wf_ground_action_wf_fmla_atom
    by (auto simp: wf_world_model_def)

  text \<open>Justification for refinement of @{const valid_happ_seq_from}.\<close>
  lemma (in wf_ast_problem) valid_happ_seq_fromE_return_iff[return_iff]: 
    assumes "wm_basic s" 
        and "\<forall>(t,as) \<in> set hs. \<forall>a \<in> set as. wf_ground_action a"
    shows "valid_happ_seq_from s hs \<longleftrightarrow> valid_happ_seq_fromE k s hs = Inr ()"
    using assms 
          holds_for_wf_fmlas 
          wf_happ_only_add_atoms 
          apply_happ_exec_refine  
    by (induction hs arbitrary: s k) (auto simp: return_iff en_exE_return_iff)

  text \<open>Now we can define a refinement for @{const valid_plan_from2}.\<close>
  fun valid_plan_from2_exec :: "world_model \<Rightarrow> plan \<Rightarrow> bool" where
    "valid_plan_from2_exec s \<pi>s \<longleftrightarrow> 
      (wf_plan \<pi>s \<and> valid_happ_seq_from s (simplify_plan (htps_exec \<pi>s) \<pi>s))"

  text \<open>With @{thm wf_ast_problem.ind_happ_seq_unique_final_state'} we can prove, that 
  if there exists a valid induced happening sequence, then simplify plan is also valid.\<close>
  lemma (in wf_ast_problem) simplify_plan_valid_exists1:
    fixes \<pi>s
    defines "htps \<equiv> htps_exec \<pi>s"
    assumes "wf_plan \<pi>s"
        and "\<exists>hs. ind_happ_seq \<pi>s hs \<and> valid_happ_seq M hs M' \<and> M' \<^sup>c\<TTurnstile>\<^sub>= (goal P)"
    shows "valid_happ_seq M (simplify_plan htps \<pi>s) M' \<and> M' \<^sup>c\<TTurnstile>\<^sub>= (goal P)"
    using assms simplify_plan_correct ind_happ_seq_unique_final_state' by blast

  text \<open>Other way round is easy, since @{const simplify_plan} is an induced 
  happening sequence.\<close>
  lemma (in wf_ast_problem) simplify_plan_valid_exists2: 
    fixes \<pi>s
    defines "htps \<equiv> htps_exec \<pi>s"
    assumes "wf_plan \<pi>s" 
        and "valid_happ_seq M (simplify_plan htps \<pi>s) M' \<and> M' \<^sup>c\<TTurnstile>\<^sub>= (goal P)"
    shows "\<exists>hs. ind_happ_seq \<pi>s hs \<and> valid_happ_seq M hs M' \<and> M' \<^sup>c\<TTurnstile>\<^sub>= (goal P)"
    using assms simplify_plan_correct by blast

  text \<open>Justification for the refinement of @{const valid_plan_from2}.\<close>
  lemma (in wf_ast_problem) valid_plan_from2_exec_refine: 
    "valid_plan_from2 s \<pi>s \<longleftrightarrow> valid_plan_from2_exec s \<pi>s"
    using simplify_plan_valid_exists1 
          simplify_plan_valid_exists2
          valid_happ_seq_from_refine[OF inst_wf_plan_wf_happ_seq]
          simplify_plan_correct
    unfolding valid_plan_from2_def plan_happ_path_def
    by (meson valid_plan_from2_exec.simps)

  text \<open>Now we can also lift @{const valid_plan_from2_exec} into an Error Monad, 
  using @{const simplify_planE} and @{const valid_happ_seq_fromE}\<close> 
  fun valid_plan_from2E :: "_ \<Rightarrow> (object, type) mapping \<Rightarrow> (object, rat) mapping \<Rightarrow> world_model \<Rightarrow> plan \<Rightarrow> _+unit" where
    "valid_plan_from2E stg mp mp_fe s \<pi>s = do {
      hs \<leftarrow> simplify_planE_avl stg mp mp_fe (htps_exec \<pi>s) \<pi>s;  
      valid_happ_seq_fromE 1 s hs
    }"

  (* directly traverse tree instead of extracting the the happening sequence with inorder *)
  (*fun valid_plan_fromE :: "_ \<Rightarrow> (object, type) mapping \<Rightarrow> (object, rat) mapping \<Rightarrow> world_model \<Rightarrow> plan \<Rightarrow> _+unit" where
    "valid_plan_fromE stg mp mp_fe s \<pi>s = do {
      htree \<leftarrow> simplify_planE_avl' stg mp mp_fe (htps_exec \<pi>s) \<pi>s;  
      valid_happ_seq_fromE_avl 1 s htree
    }"*)

  lemma (in wf_ast_problem) valid_plan_fromE_wf_plan:
    assumes "valid_plan_from2E STG mp_objT mp_Fevl s \<pi>s = Inr ()" 
    shows "wf_plan \<pi>s"
  proof -
    have "strict_sorted (htps_exec \<pi>s)"
      using htps_exec_distinct htps_exec_sorted by (simp add: strict_sorted_iff)
    then show ?thesis
      using assms wf_problem simplify_planE_return_iff simplify_planE_avl_equiv
      by (auto simp: return_iff wf_problem_def)
  qed

  text \<open>Refinement lemma for our plan checking algorithm\<close>
  lemma (in wf_ast_problem) valid_plan_from2E_return_iff:
    assumes "wf_world_model s"
    shows "valid_plan_from2E STG mp_objT mp_Fevl s \<pi>s = Inr () \<longleftrightarrow> valid_plan_from2 s \<pi>s"
  proof -
    have "wf_domain"
      using wf_problem unfolding wf_problem_def by simp
    have "wm_basic s"
      using \<open>wf_world_model s\<close> wf_fmla_atom_alt wf_func_assign_is_eqAtom 
      unfolding wf_world_model_def wm_basic_def by auto
    have "strict_sorted (htps_exec \<pi>s)"
      using htps_exec_distinct htps_exec_sorted by (simp add: strict_sorted_iff)
    show ?thesis
      using \<open>wf_domain\<close> \<open>strict_sorted (htps_exec \<pi>s)\<close> valid_plan_from2_exec_refine
            valid_happ_seq_fromE_return_iff[OF \<open>wm_basic s\<close> simplify_plan_wf_ground_action] 
            simplify_planE_return_iff[OF \<open>wf_domain\<close> \<open>strict_sorted (htps_exec \<pi>s)\<close>]
            simplify_planE_avl_equiv
      apply (simp add: valid_plan_fromE_wf_plan) 
      apply (auto simp: return_iff)
      apply metis+
      done
  qed

  (* concise lemma for paper *)
  lemma (in wf_ast_problem)
    assumes "wf_world_model s"
    shows "valid_plan_from2E STG mp_objT mp_Fevl s \<pi>s = Inr () \<longleftrightarrow> valid_plan_from2 s \<pi>s"
    using assms by (rule valid_plan_from2E_return_iff)

  lemmas valid_plan_from2E_return_iff'[return_iff]
    = wf_ast_problem.valid_plan_from2E_return_iff[of P, OF wf_ast_problem.intro]

  (* Attempt to improve performance by first sorting the plan. *)

  (* slightly modified implementation of Merge-Sort from 
    (https://isabelle.in.tum.de/library/HOL/HOL-Data_Structures/Sorting.html) *)
  (*fun merge :: "('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "merge cmp [] ys = ys" |
    "merge cmp xs [] = xs" |
    "merge cmp (x#xs) (y#ys) = (
      if cmp x > cmp y then 
        x # merge cmp xs (y#ys) 
      else 
        y # merge cmp (x#xs) ys)"

  fun msort :: "('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "msort cmp xs = (let n = length xs in
    if n \<le> 1 then xs
    else merge cmp (msort cmp (take (n div 2) xs)) (msort cmp (drop (n div 2) xs)))"

  lemma set_msort: "set (msort cmp xs) = set xs"
    sorry (* TODO: proof *)

  fun valid_plan_fromE_sort :: "_ \<Rightarrow> (object, type) mapping \<Rightarrow> (object, rat) mapping \<Rightarrow> nat \<Rightarrow> world_model \<Rightarrow> plan \<Rightarrow> _+unit" where
    "valid_plan_fromE_sort stg mp mp_fe si s \<pi>s = do {
      hs \<leftarrow> simplify_planE stg mp mp_fe (htps_exec \<pi>s) (msort (\<lambda>(t\<^sub>a,a). t\<^sub>a) \<pi>s); 
      valid_happ_seq_fromE stg mp si s hs
    }"

  text \<open>Justification for sorting optimization.\<close>
  lemma (in wf_ast_problem) valid_plan_fromE_sort_iff:
    assumes "wf_world_model s"
    shows "valid_plan_fromE STG mp_objT mp_Fevl k s \<pi>s = Inr () \<longleftrightarrow> 
            valid_plan_fromE_sort STG mp_objT mp_Fevl k s \<pi>s = Inr ()"
    proof -
    have "wf_domain"
      using wf_problem unfolding wf_problem_def by simp
    have "wm_basic s"
      using \<open>wf_world_model s\<close> wf_fmla_atom_alt wf_func_assign_is_eqAtom 
      unfolding wf_world_model_def wm_basic_def by auto
    have "strict_sorted (htps_exec \<pi>s)"
      using htps_exec_distinct htps_exec_sorted by (simp add: strict_sorted_iff)
    show ?thesis
      using simplify_planE_eq_plan_order[OF \<open>wf_domain\<close> \<open>strict_sorted (htps_exec \<pi>s)\<close> msort_set]
      by (auto simp: return_iff)
  qed

  lemma (in wf_ast_problem) valid_plan_fromE_sort_wf_plan:
    assumes "wf_world_model s" and "valid_plan_fromE_sort STG mp_objT mp_Fevl k s \<pi>s = Inr ()" 
    shows "wf_plan \<pi>s"
  proof -
    have "strict_sorted (htps_exec \<pi>s)"
      using htps_exec_distinct htps_exec_sorted by (simp add: strict_sorted_iff)
    then have "wf_plan (msort (\<lambda>(t\<^sub>a,a). t\<^sub>a) \<pi>s)"
      using assms wf_problem simplify_planE_return_iff
      by (auto simp: return_iff wf_problem_def)
    then show ?thesis
      unfolding wf_plan_def using set_msort by fastforce
  qed

  lemma (in wf_ast_problem) valid_plan_fromE_sort_iff:
    assumes "wf_world_model s"
    shows "valid_plan_fromE_sort STG mp_objT mp_Fevl k s \<pi>s = Inr () \<longleftrightarrow> valid_plan_from s \<pi>s"
    sorry

  lemmas valid_plan_fromE_sort_return_iff'[return_iff]
    = wf_ast_problem.valid_plan_fromE_sort_iff[of P, OF wf_ast_problem.intro]*)

end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>

subsection \<open>Executable Plan Checker\<close>
text \<open>We obtain the main plan checker by combining the well-formedness check
  and executability check. \<close>


definition "check_all_list P l msg msgf \<equiv>
  forallM (\<lambda>x. check (P x) (\<lambda>_::unit. shows msg o shows '': '' o msgf x) ) l <+? snd"

lemma check_all_list_return_iff[return_iff]: "check_all_list P l msg msgf = Inr () \<longleftrightarrow> (\<forall>x\<in>set l. P x)"
  unfolding check_all_list_def by (induction l) (auto)

definition "check_wf_types D \<equiv> do {
  check_all_list (\<lambda>(_,t). t=(STR ''object'') \<or> t\<in>fst`set (types D)) (types D) ''Undeclared supertype'' (shows o snd)
}"

lemma check_wf_types_return_iff[return_iff]: "check_wf_types D = Inr () \<longleftrightarrow> ast_domain.wf_types D"
  unfolding ast_domain.wf_types_def check_wf_types_def by (force simp: return_iff)

definition "check_wf_domain D stg conT \<equiv> do {
  check_wf_types D;
  check (distinct (map (predicate_decl.pred) (predicates D))) (ERRS ''Duplicate predicate declaration'');
  check_all_list (ast_domain.wf_predicate_decl D) (predicates D) ''Malformed predicate declaration'' (shows o predicate.name o predicate_decl.pred);
  check (distinct (map (function_decl.func) (functions D))) (ERRS ''Duplicate function declaration'');
  check_all_list (ast_domain.wf_function_decl D) (functions D) ''Malformed function declaration'' (shows o func.name o function_decl.func);
  check (distinct (map fst (consts D))) (ERRS ''Duplicate constant declaration'');
  check (\<forall>(n,T)\<in>set (consts D). ast_domain.wf_type D T) (ERRS ''Malformed type'');
  check (distinct (map ast_action_schema.name (actions D))  ) (ERRS ''Duplicate action name'');
  check_all_list (ast_domain.wf_action_schema' D stg conT) (actions D) ''Malformed action'' (shows o ast_action_schema.name)
}"

lemma check_wf_domain_return_iff[return_iff]:
  "check_wf_domain D stg conT = Inr () \<longleftrightarrow> ast_domain.wf_domain' D stg conT"
proof -
  interpret ast_domain D .
  show ?thesis
    unfolding check_wf_domain_def wf_domain'_def by (auto simp: return_iff)
qed

definition "prepend_err_msg msg e \<equiv> \<lambda>_::unit. shows msg o shows '': '' o e ()"

definition "check_wf_problem P stg conT mp \<equiv> do {
  let D = ast_problem.domain P;
  check_wf_domain D stg conT <+? prepend_err_msg ''Domain not well-formed'';
  check (distinct (map fst (objects P) @ map fst (consts D))) (ERRS ''Duplicate object declaration'');
  check ((\<forall>(n,T)\<in>set (objects P). ast_domain.wf_type D T)) (ERRS ''Malformed type'');
  check (distinct (init P)) (ERRS ''Duplicate fact in initial state'');
  check (\<forall>f\<in>set (init P). ast_problem.wf_fmla_atom2' P mp stg f \<or> ast_problem.wf_func_assign' P mp stg f) (ERRS ''Malformed formula in initial state'');
  check (ast_domain.wf_fmla' D (Mapping.lookup mp) stg (goal P)) (ERRS ''Malformed goal formula'')
}"

lemma check_wf_problem_return_iff[return_iff]:
  "check_wf_problem P stg conT mp = Inr () \<longleftrightarrow> ast_problem.wf_problem' P stg conT mp"
proof -
  interpret ast_problem P .
  show ?thesis
    unfolding check_wf_problem_def wf_problem'_def by (auto simp: return_iff)
qed

definition "check_plan P \<pi>s \<equiv> do {
  let stg = ast_domain.STG (ast_problem.domain P);
  let conT = ast_domain.mp_constT (ast_problem.domain P);
  let mp = ast_problem.mp_objT P;
  let mp_fe = ast_problem.mp_Fevl P;
  check_wf_problem P stg conT mp;
  ast_problem.valid_plan_from2E P stg mp mp_fe (ast_problem.I P) \<pi>s
} <+? (\<lambda>e. String.implode (e () ''''))"

text \<open>Correctness theorem of the plan checker: It returns @{term "Inr ()"}
  if and only if the problem is well-formed and the plan is valid.
\<close>
theorem check_plan_return_iff[return_iff]: 
  "check_plan P \<pi>s = Inr () \<longleftrightarrow> ast_problem.wf_problem P \<and> ast_problem.valid_plan2 P \<pi>s"
proof -
  interpret ast_problem P .
  show ?thesis
    unfolding check_plan_def ast_problem.valid_plan2_def
    using valid_plan_from2E_return_iff' wf_ast_problem_def wf_ast_problem.wf_I
    by (fastforce simp: wf_problem'_correct return_iff)
qed

find_theorems ast_problem.valid_plan_from2

subsection \<open>Code Setup\<close>

text \<open>In this section, we set up the code generator to generate verified
  code for our plan checker.\<close>

subsubsection \<open>Code Equations\<close>
text \<open>We first register the code equations for the functions of the checker.
  Note that we not necessarily register the original code equations, but also
  optimized ones.
\<close>

lemmas wf_domain_code =
  ast_domain.sig_def
  ast_domain.wf_types_def
  ast_domain.wf_type.simps
  ast_domain.wf_predicate_decl.simps
  ast_domain.STG_def
  ast_domain.is_of_type'_def
  ast_domain.wf_atom'.simps
  ast_domain.wf_pred_atom'.simps
  ast_domain.wf_fmla'.simps
  ast_domain.wf_fmla_atom1'.simps
  ast_domain.wf_duration_consts'_def
  ast_domain.wf_effect'.simps
  ast_domain.wf_action_schema'.simps
  ast_domain.wf_domain'_def
  ast_domain.subst_term.simps
  ast_domain.mp_constT_def
  (* my new function *)
  ast_domain.wf_function_decl.simps
  ast_domain.func_sig_def
  ast_domain.wf_func_args'.simps
  ast_domain.wf_duration_const'.simps
  ast_domain.acts_non_intrf_def
  (*ast_domain.apply_happ.simps*)

declare wf_domain_code[code]

lemmas wf_problem_code =
  ast_problem.durations_match'_def
  ast_problem.wf_problem'_def
  ast_problem.wf_fact'_def
  ast_problem.is_obj_of_type_alt
  ast_problem.wf_fact_def
  ast_problem.wf_plan_action.simps
  ast_domain.subtype_edge.simps

declare wf_problem_code[code]

lemmas check_code =
  ast_problem.valid_plan2_def
  ast_problem.valid_plan_from2E.simps
  ast_problem.res_inst.simps
  ast_domain.resolve_action_schema_def
  ast_domain.resolve_action_schemaE_def
  ast_problem.I_def
  ast_domain.instantiate_action_schema.simps
  ast_problem.holds_def
  ast_problem.mp_objT_def
  ast_problem.is_obj_of_type_impl_def
  ast_problem.wf_fmla_atom2'_def
  valuation_def
  (* my new functions *)
  ast_problem.valid_happ_seq_fromE.simps 
  ast_problem.htps_exec.simps
  ast_problem.insort_htp.simps
  ast_problem.simplify_planE.simps
  ast_problem.simplify_actionE.simps
  ast_problem.insort_happ.simps
  ast_domain.inst_snap_action.simps
  ast_domain.filter_time_spec_def
  ast_domain.conjunct_effects_def
  (*ast_problem.acts_non_intrf_exec_def*)
  ast_problem.apply_happ_exec.simps
  ast_problem.en_exE_def
  ast_problem.insort_mult_happs.simps
  ast_problem.duration_matches'.simps
  ast_problem.wf_func_assign'.simps
  (*ast_problem.consec_htps_in_interval_exec.simps*)
  ast_problem.mp_Fevl_def
  ast_problem.place_inv_snap_acts.simps
  (*ast_problem.place_inv_snap_acts_acc.simps*)
  ast_problem.insort_timed_ground_acts.simps
  ast_problem.insert_happ_to_tree.simps
  ast_problem.insert_timed_ground_acts_to_tree.simps
  ast_problem.avl_inorder_def
  ast_problem.simplify_planE_avl.simps
  ast_problem.simplify_planE_avl'.simps
  ast_problem.avl_height.simps
  ast_problem.avl_node_def
  ast_problem.avl_balR_def
  ast_problem.avl_balL_def
  (*ast_problem.merge.simps
  ast_problem.msort.simps
  ast_problem.valid_plan_fromE_sort.simps*)

declare check_code[code]

subsubsection \<open>Setup for Containers Framework\<close>

derive (linorder) compare rat

derive (eq) ceq predicate func atom object formula 
derive ccompare predicate func atom object formula
derive (no) cenum atom object formula
derive (rbt) set_impl func atom object formula

derive (rbt) mapping_impl object

derive linorder predicate func object atom "object atom formula"

subsubsection \<open>More Efficient Distinctness Check for Linorders\<close>
(* TODO: Can probably be optimized even more. *)
fun no_stutter :: "'a list \<Rightarrow> bool" where
  "no_stutter [] = True"
| "no_stutter [_] = True"
| "no_stutter (a#b#l) = (a\<noteq>b \<and> no_stutter (b#l))"

lemma sorted_no_stutter_eq_distinct: "sorted l \<Longrightarrow> no_stutter l \<longleftrightarrow> distinct l"
  apply (induction l rule: no_stutter.induct)
  apply (auto simp: )
  done

definition distinct_ds :: "'a::linorder list \<Rightarrow> bool"
  where "distinct_ds l \<equiv> no_stutter (quicksort l)"

lemma [code_unfold]: "distinct = distinct_ds"
  apply (intro ext)
  unfolding distinct_ds_def
  apply (auto simp: sorted_no_stutter_eq_distinct)
  done

subsubsection \<open>Parsing Rational Numbers\<close>

type_synonym digit = nat

text\<open>Well-formedness conditions for a digit and a sequence of digits.\<close>
definition "wf_digit d \<longleftrightarrow> d < 10" 
text\<open>A sequence of digits is well-formed iff it is normalized and only contains well-formed digits.\<close>
definition "wf_digits ds \<longleftrightarrow> (\<forall>d \<in> set ds. wf_digit d)"

text\<open>Functions to trim leading and trailing zeros.\<close>

fun trim_ld_zs :: "digit list \<Rightarrow> digit list" where
  "trim_ld_zs [] = []"
| "trim_ld_zs (d#ds) = 
  (if d = 0 then trim_ld_zs ds else d#ds)"

lemma tlz_hd_neq_z: "trim_ld_zs ds = ds' \<Longrightarrow> hd ds' \<noteq> 0 \<or> ds' = []"
  by (induction ds) auto

lemma trim_ld_zs_idem: "trim_ld_zs (trim_ld_zs ds) = trim_ld_zs ds"
  by (induction ds) auto

lemma trim_ld_zs_wf: "wf_digits ds \<Longrightarrow> wf_digits (trim_ld_zs ds)"
  unfolding wf_digits_def by (induction ds) auto

lemma trim_ld_zs_app: "trim_ld_zs (ds1 @ ds2) = (trim_ld_zs ds1) @ ds2 \<or> (\<forall>d \<in> set ds1. d = 0)"
  by (induction ds1) auto

fun trim_tr_zs' :: "digit list \<Rightarrow> digit list \<Rightarrow> digit list" where
  "trim_tr_zs' [] zs = []"
| "trim_tr_zs' (d#ds) zs = 
  (if d = 0 then trim_tr_zs' ds (0#zs)
  else zs @ d # (trim_tr_zs' ds []))"

fun trim_tr_zs :: "digit list \<Rightarrow> digit list" where
  "trim_tr_zs ds = trim_tr_zs' ds []"

lemma ttz_last_neq_z_aux: 
  assumes "trim_tr_zs' ds zs = ds'" 
  shows "last ds' \<noteq> 0 \<or> ds' = []"
  using assms
proof (induction ds arbitrary: ds' zs)
  case Nil
  then show ?case by auto
next
  case (Cons d ds)
  then show ?case
    by (cases "d = 0") force+
qed

lemma ttz_last_neq_z: "trim_tr_zs ds = ds' \<Longrightarrow> last ds' \<noteq> 0 \<or> ds' = []"
  using ttz_last_neq_z_aux by (auto simp: Let_def split: if_splits)

lemma trim_tr_zs'_wf: "wf_digits ds \<and> wf_digits zs \<Longrightarrow> wf_digits (trim_tr_zs' ds zs)"
  unfolding wf_digits_def by (induction ds zs rule: trim_tr_zs'.induct) auto

lemma trim_tr_zs_wf: "wf_digits ds \<Longrightarrow> wf_digits (trim_tr_zs ds)"
  using trim_tr_zs'_wf[where zs="[]"] by (auto simp: wf_digits_def)

text\<open>Functions to convert between integers and a sequence of digits.\<close>

fun int_of_digits :: "digit list \<Rightarrow> int \<Rightarrow> int" where
  "int_of_digits [] acc = acc"
| "int_of_digits (d#ds) acc = int_of_digits ds (acc * 10 + d)"

fun digits_of_int :: "int \<Rightarrow> digit list" where
  "digits_of_int i = 
    (if i \<le> 0 then []
    else if i < 10 then [nat i]
    else digits_of_int (i div 10) @ [nat (i mod 10)])"

value "digits_of_int (int_of_digits [1,2,3,4] 0)"
value "int_of_digits (digits_of_int 1234) 0"

value "digits_of_int (int_of_digits [1] 123)"

lemma digits_of_int_int_of_digits_aux:
  assumes "acc > 0" and "\<forall>d \<in> set ds. wf_digit d"
  shows "digits_of_int (int_of_digits ds acc) = digits_of_int acc @ ds"
  using assms
  by (induction ds acc arbitrary: acc rule: int_of_digits.induct) (auto simp: wf_digit_def)

text\<open>Proof for correctness of function @{const int_of_digits} and @{const digits_of_int}.\<close>
lemma digits_of_int_int_of_digits:
  assumes "wf_digits ds"
  shows "digits_of_int (int_of_digits ds 0) = trim_ld_zs ds"
  using assms digits_of_int_int_of_digits_aux
proof (induction ds)
  case Nil
  then show ?case by auto
next
  case (Cons d ds)
  then show ?case
    by (cases "d = 0") (auto simp: wf_digits_def wf_digit_def)
qed

text\<open>Function to convert from a sequences of digits to a rational number.\<close>
primrec rat_of_digits_pair :: "digit list \<times> digit list \<Rightarrow> rat" where
  "rat_of_digits_pair (ds\<^sub>1,ds\<^sub>2) = (
    let ds\<^sub>1' = trim_ld_zs ds\<^sub>1; ds\<^sub>2' = trim_tr_zs ds\<^sub>2 in
      Rat.Fract (int_of_digits (ds\<^sub>1' @ ds\<^sub>2') 0) (10 ^ length ds\<^sub>2')
  )"

text\<open>For proofs about the function @{const rat_of_digits_pair} see \texttt{Rat\_Parsing.thy}.\<close>

subsubsection \<open>Code Generation\<close>

(* TODO/FIXME: Code_Char was removed from Isabelle-2018! 
  Check for performance regression of generated code!
*)
export_code
  check_plan
  nat_of_integer integer_of_nat int_of_integer integer_of_int Inl Inr Rat.Fract Rat.of_int rat_of_digits_pair
  predAtm eqAtm predicate Pred Func Either Var Obj PredDecl FuncDecl BigAnd BigOr
  formula.Not formula.Bot Effect No_Const Time_Const Func_Const LEQ EQ GEQ
  Simple_Action_Schema Durative_Action_Schema At_Start At_End Over_All
  map_atom Domain Problem Simple_Plan_Action Durative_Plan_Action
  term.CONST term.VAR (* I want to export the entire type, but I can only export the constructor because term is already an isabelle keyword. *)
  String.explode String.implode
  in SML
  module_name TEMPORAL_PDDL_Checker_Exported
  file "code/TEMPORAL_PDDL_Checker_Exported.sml"
    

(* export_code ast_domain.apply_effect_exec in SML module_name ast_domain *)
(* Usage example from within Isabelle *)
(*
ML_val \<open>
  let
    val prefix="/home/lammich/devel/isabelle/planning/papers/pddl_validator/experiments/results/"

    fun check name =
      (name,@{code parse_check_dpp_impl}
        (file_to_string (prefix ^ name ^ ".dom.pddl"))
        (file_to_string (prefix ^ name ^ ".prob.pddl"))
        (file_to_string (prefix ^ name ^ ".plan")))

  in
    (*check "IPC5_rovers_p03"*)
    check "Test2_rover_untyped_pfile07"
  end
\<close>
*)

end \<comment> \<open>Theory\<close>
