section \<open>Temporal PDDL Semantics\<close>
theory TEMPORAL_PDDL_Semantics
imports
  "Propositional_Proof_Systems.Formulas"
  "Propositional_Proof_Systems.Sema"
  "Propositional_Proof_Systems.Consistency"
  "Automatic_Refinement.Misc"
  "Automatic_Refinement.Refine_Util"
  "HOL.Rat"
  Error_Monad_Add
  (*"HOL.Real"*) (* TODO: maybe change sematics time to reals *)
begin
no_notation insert ("_ \<triangleright> _" [56,55] 55)

subsection \<open>Utility Functions\<close>

abbreviation strict_sorted::"'a::{linorder} list \<Rightarrow> bool" where "strict_sorted \<equiv> sorted_wrt (<)"

definition "index_by f l \<equiv> map_of (map (\<lambda>x. (f x,x)) l)"

lemma index_by_eq_Some_eq[simp]:
  assumes "distinct (map f l)"
  shows "index_by f l n = Some x \<longleftrightarrow> (x\<in>set l \<and> f x = n)"
  unfolding index_by_def
  using assms
  by (auto simp: o_def)

lemma index_by_eq_SomeD:
  shows "index_by f l n = Some x \<Longrightarrow> (x\<in>set l \<and> f x = n)"
  unfolding index_by_def
  by (auto dest: map_of_SomeD)


lemma lookup_zip_idx_eq:
  assumes "length params = length args"
  assumes "i<length args"
  assumes "distinct params"
  assumes "k = params ! i"
  shows "map_of (zip params args) k = Some (args ! i)"
  using assms
  by (auto simp: in_set_conv_nth)

lemma rtrancl_image_idem[simp]: "R\<^sup>* `` R\<^sup>* `` s = R\<^sup>* `` s"
  by (metis relcomp_Image rtrancl_idemp_self_comp)


subsection \<open>Abstract Syntax\<close>

subsubsection \<open>Generic Entities\<close>
text \<open>Defines the time number type\<close>

type_synonym time = rat

type_synonym name = String.literal

datatype predicate = Pred (name: name)

datatype func = Func (name: name)

text \<open>Some of the AST entities are defined over a polymorphic \<open>'val\<close> type,
  which gets either instantiated by variables (for domains)
  or objects (for problems).
\<close>

text \<open>An atom is either a predicate with arguments, or an equality statement.\<close>
datatype 'ent atom = predAtm (predicate: predicate) (arguments: "'ent list")
                   | eqAtm (lhs: 'ent) (rhs: 'ent)


text \<open>A type is a list of primitive type names.
  To model a primitive type, we use a singleton list.\<close>
datatype type = Either (primitives: "name list")


text \<open>An effect contains a list of values to be added, and a list of values
  to be removed.\<close>
datatype 'ent ast_effect = Effect (adds: "('ent atom formula) list")
                                  (dels: "('ent atom formula) list")

text \<open>Variables are identified by their names.\<close>
datatype variable = Var (varname: name)

text \<open>Objects and constants are identified by their names\<close>
datatype object = Obj (name: name) | FuncEnt (func: func) (arguments: "object list") | TimeEnt time

datatype "term" = VAR variable | CONST object

hide_const (open) VAR CONST \<comment> \<open>Refer to constructors by qualified names only\<close>


subsubsection \<open>Domains\<close>

text \<open>A time specifier specifies the time point of conditions and effects in a durative action\<close>
datatype temporal_annotation = At_Start | Over_All | At_End

datatype duration_op = EQ | LEQ | GEQ

datatype 'ent duration_constraint = 
  No_Const 
| Time_Const (d_op: duration_op) time 
| Func_Const (d_op: duration_op) (func: func) (arguments: "'ent list")

text \<open>An action schema has a name, a typed parameter list, a precondition,
  and an effect. In case of a durative action schema there is additionally a 
  duration constraint, and the conditions and effects are timed with a time specifier\<close>
datatype ast_action_schema =
  Simple_Action_Schema
    (name: name)
    (parameters: "(variable \<times> type) list")
    (precondition: "term atom formula")
    (effect: "term ast_effect")
| Durative_Action_Schema
    (name: name)
    (parameters: "(variable \<times> type) list")                             
    (duration_constraint: "term duration_constraint list")
    (condition: "(temporal_annotation \<times> (term atom formula)) list")
    (durative_effect: "(temporal_annotation \<times> (term ast_effect)) list") 

text \<open>A predicate declaration contains the predicate's name and its
  argument types.\<close>
datatype predicate_decl = PredDecl (pred: predicate) (argTs: "type list")

datatype function_decl = FuncDecl (func: func) (argTs: "type list")

text \<open>A domain contains the declarations of primitive types, predicates,
  and action schemas.\<close>
datatype ast_domain = Domain
  (types: "(name \<times> name) list") \<comment> \<open> \<open>(type, supertype)\<close> declarations. \<close>
  (predicates: "predicate_decl list")
  ("functions": "function_decl list")
  ("consts": "(object \<times> type) list")
  (actions: "ast_action_schema list")

subsubsection \<open>Problems\<close>

text \<open>A fact is a predicate applied to objects.\<close>
type_synonym fact = "predicate \<times> object list"

text \<open>A problem consists of a domain, a list of objects,
  a description of the initial state, and a description of the goal state. \<close>
datatype ast_problem = Problem
  (domain: ast_domain)
  (objects: "(object \<times> type) list")
  (init: "object atom formula list")
  (goal: "object atom formula")

subsubsection \<open>Plans\<close>

datatype plan_action = 
  Simple_Plan_Action (name: name) (arguments: "object list")
| Durative_Plan_Action (name: name) (arguments: "object list") (duration: time)

type_synonym plan = "(time \<times> plan_action) list"

subsubsection \<open>Ground Actions\<close>
text \<open>The following datatype represents an action scheme that has been
  instantiated by replacing the arguments with concrete objects,
  also called ground action.\<close>
datatype ground_action = Ground_Action
  (ga_name: name)
  (timing: temporal_annotation)
  (precondition: "(object atom) formula")
  (effect: "object ast_effect")

text \<open>A happening represents a collection of grounded actions that are all
   executed simultaneously at a specified time point.\<close>
type_synonym happening = "time \<times> (ground_action list)"

subsection \<open>Closed-World Assumption, Equality, and Negation\<close>
  text \<open>Discriminator for atomic predicate formulas.\<close>
  fun is_predAtom where
    "is_predAtom (Atom (predAtm _ _)) = True" | "is_predAtom _ = False"

  fun is_eqAtom where
    "is_eqAtom (Atom (eqAtm _ _)) = True" | "is_eqAtom _ = False"

  text \<open>The world model is a set of (atomic) formulas\<close>
  type_synonym world_model = "object atom formula set"
  
  text \<open>It is basic, if it only contains atoms\<close>
  definition "wm_basic M \<equiv> \<forall>a\<in>M. is_predAtom a"

  text \<open>A valuation extracted from the atoms of the world model\<close>
  definition valuation :: "world_model \<Rightarrow> object atom valuation"
    where "valuation M \<equiv> \<lambda>predAtm p xs \<Rightarrow> Atom (predAtm p xs) \<in> M | eqAtm a b \<Rightarrow> a=b"

  text \<open>Augment a world model by adding negated versions of all atoms
    not contained in it, as well as interpretations of equality.\<close>
  definition close_world :: "world_model \<Rightarrow> world_model" where
    "close_world M =
      M \<union> {\<^bold>\<not>(Atom (predAtm p as)) | p as. Atom (predAtm p as) \<notin> M}
      \<union> {Atom (eqAtm a a) | a. True} \<union> {\<^bold>\<not>(Atom (eqAtm a b)) | a b. a\<noteq>b}"

  definition "close_neg M \<equiv> M \<union> {\<^bold>\<not>(Atom a) | a. Atom a \<notin> M}"
  lemma "wm_basic M \<Longrightarrow> close_world M = close_neg (M \<union> {Atom (eqAtm a a) | a. True})"
    unfolding close_world_def close_neg_def wm_basic_def
    apply clarsimp
    apply (auto 0 3)
    by (metis atom.exhaust)

  abbreviation cw_entailment (infix "\<^sup>c\<TTurnstile>\<^sub>=" 53) where
    "M \<^sup>c\<TTurnstile>\<^sub>= \<phi> \<equiv> close_world M \<TTurnstile> \<phi>"

  lemma
    close_world_extensive: "M \<subseteq> close_world M" and
    close_world_idem[simp]: "close_world (close_world M) = close_world M"
    by (auto simp: close_world_def)

  lemma in_close_world_conv:
    "\<phi> \<in> close_world M \<longleftrightarrow> (
        \<phi>\<in>M
      \<or> (\<exists>p as. \<phi>=\<^bold>\<not>(Atom (predAtm p as)) \<and> Atom (predAtm p as) \<notin> M)
      \<or> (\<exists>a. \<phi>=Atom (eqAtm a a))
      \<or> (\<exists>a b. \<phi>=\<^bold>\<not>(Atom (eqAtm a b)) \<and> a\<noteq>b)
    )"
    by (auto simp: close_world_def)

  lemma valuation_aux_1:
    fixes M :: world_model and \<phi> :: "object atom formula"
    defines "C \<equiv> close_world M"
    assumes A: "\<forall>\<phi>\<in>C. \<A> \<Turnstile> \<phi>"
    shows "\<A> = valuation M"
    using A unfolding C_def
    apply (auto simp: in_close_world_conv valuation_def Ball_def intro!: ext split: atom.split)
    apply (metis formula_semantics.simps(1) formula_semantics.simps(3))
    apply (metis formula_semantics.simps(1) formula_semantics.simps(3))
    apply (metis atom.collapse(2) formula_semantics.simps(1) is_predAtm_def)
    done

  lemma valuation_aux_2:
    assumes "wm_basic M"
    shows "(\<forall>G\<in>close_world M. valuation M \<Turnstile> G)"
    using assms unfolding wm_basic_def
    by (force simp: in_close_world_conv valuation_def elim: is_predAtom.elims is_eqAtom.elims)

  lemma val_imp_close_world: "valuation M \<Turnstile> \<phi> \<Longrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= \<phi>"
    unfolding entailment_def
    using valuation_aux_1
    by blast

  lemma close_world_imp_val:
    "wm_basic M \<Longrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= \<phi> \<Longrightarrow> valuation M \<Turnstile> \<phi>"
    unfolding entailment_def using valuation_aux_2 by blast

  text \<open>Main theorem of this section:
    If a world model \<open>M\<close> contains only atoms, its induced valuation
    satisfies a formula \<open>\<phi>\<close> if and only if the closure of \<open>M\<close> entails \<open>\<phi>\<close>.

    Note that there are no syntactic restrictions on \<open>\<phi>\<close>,
    in particular, \<open>\<phi>\<close> may contain negation.
  \<close>
  theorem valuation_iff_close_world:
    assumes "wm_basic M"
    shows "valuation M \<Turnstile> \<phi> \<longleftrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= \<phi>"
    using assms val_imp_close_world close_world_imp_val by blast


subsubsection \<open>Proper Generalization\<close>
text \<open>Adding negation and equality is a proper generalization of the
  case without negation and equality\<close>

fun is_STRIPS_fmla :: "'ent atom formula \<Rightarrow> bool" where
  "is_STRIPS_fmla (Atom (predAtm _ _)) \<longleftrightarrow> True"
| "is_STRIPS_fmla (\<bottom>) \<longleftrightarrow> True"
| "is_STRIPS_fmla (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) \<longleftrightarrow> is_STRIPS_fmla \<phi>\<^sub>1 \<and> is_STRIPS_fmla \<phi>\<^sub>2"
| "is_STRIPS_fmla (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<longleftrightarrow> is_STRIPS_fmla \<phi>\<^sub>1 \<and> is_STRIPS_fmla \<phi>\<^sub>2"
| "is_STRIPS_fmla (\<^bold>\<not>\<bottom>) \<longleftrightarrow> True"
| "is_STRIPS_fmla _ \<longleftrightarrow> False"

lemma aux1: "\<lbrakk>wm_basic M; is_STRIPS_fmla \<phi>; valuation M \<Turnstile> \<phi>; \<forall>G\<in>M. \<A> \<Turnstile> G\<rbrakk> \<Longrightarrow> \<A> \<Turnstile> \<phi>"
  apply(induction \<phi> rule: is_STRIPS_fmla.induct)
  by (auto simp: valuation_def)

lemma aux2: "\<lbrakk>wm_basic M; is_STRIPS_fmla \<phi>; \<forall>\<A>. (\<forall>G\<in>M. \<A> \<Turnstile> G) \<longrightarrow> \<A> \<Turnstile> \<phi>\<rbrakk> \<Longrightarrow> valuation M \<Turnstile> \<phi>"
  apply(induction \<phi> rule: is_STRIPS_fmla.induct)
  apply simp_all
  apply (metis in_close_world_conv valuation_aux_2)
  using in_close_world_conv valuation_aux_2 apply blast
  using in_close_world_conv valuation_aux_2 by auto


lemma valuation_iff_STRIPS:
  assumes "wm_basic M"
  assumes "is_STRIPS_fmla \<phi>"
  shows "valuation M \<Turnstile> \<phi> \<longleftrightarrow> M \<TTurnstile> \<phi>"
proof -
  have aux1: "\<And>\<A>. \<lbrakk>valuation M \<Turnstile> \<phi>; \<forall>G\<in>M. \<A> \<Turnstile> G\<rbrakk> \<Longrightarrow> \<A> \<Turnstile> \<phi>"
    using assms apply(induction \<phi> rule: is_STRIPS_fmla.induct)
    by (auto simp: valuation_def)
  have aux2: "\<lbrakk>\<forall>\<A>. (\<forall>G\<in>M. \<A> \<Turnstile> G) \<longrightarrow> \<A> \<Turnstile> \<phi>\<rbrakk> \<Longrightarrow> valuation M \<Turnstile> \<phi>"
    using assms
    apply(induction \<phi> rule: is_STRIPS_fmla.induct)
    apply simp_all
    apply (metis in_close_world_conv valuation_aux_2)
    using in_close_world_conv valuation_aux_2 apply blast
    using in_close_world_conv valuation_aux_2 by auto
  show ?thesis
    by (auto simp: entailment_def intro: aux1 aux2)
qed

text \<open>Our extension to negation and equality is a proper generalization of the
  standard STRIPS semantics for formula without negation and equality\<close>
theorem proper_STRIPS_generalization:
  "\<lbrakk>wm_basic M; is_STRIPS_fmla \<phi>\<rbrakk> \<Longrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= \<phi> \<longleftrightarrow> M \<TTurnstile> \<phi>"
  by (simp add: valuation_iff_close_world[symmetric] valuation_iff_STRIPS)

subsection \<open>Happening Execution Semantics\<close>

text \<open>For this section, we fix a domain \<open>D\<close>, using Isabelle's
  locale mechanism.\<close>
locale ast_domain =
  fixes D :: ast_domain
begin

  text \<open>Check if two ground actions are interfering. This definition is taken from [FL03]\<close>
  definition acts_non_intrf :: "ground_action \<Rightarrow> ground_action \<Rightarrow> bool" where
    "acts_non_intrf a b \<longleftrightarrow> (
      let 
        add\<^sub>a = set(adds(effect a)); del\<^sub>a = set(dels(effect a)); pre\<^sub>a = Atom ` atoms (precondition a);
        add\<^sub>b = set(adds(effect b)); del\<^sub>b = set(dels(effect b)); pre\<^sub>b = Atom ` atoms (precondition b) 
      in
      pre\<^sub>a \<inter> (add\<^sub>b \<union> del\<^sub>b) = {} \<and>
      pre\<^sub>b \<inter> (add\<^sub>a \<union> del\<^sub>a) = {} \<and>
      add\<^sub>a \<inter> del\<^sub>b = {} \<and>
      add\<^sub>b \<inter> del\<^sub>a = {})"

  lemma acts_non_intrf_symmetric: 
    "\<forall>a b. acts_non_intrf a b \<longleftrightarrow> acts_non_intrf b a"
    unfolding acts_non_intrf_def by (auto simp: Let_def)

  text \<open>It seems to be agreed upon that, in case of a contradictory effect,
    addition overrides deletion. We model this behaviour by first executing
    the deletions, and then the additions.\<close>
  fun apply_happ :: "happening \<Rightarrow> world_model \<Rightarrow> world_model" where
    "apply_happ (t\<^sub>i, A\<^sub>i) M = 
      (M - \<Union> (set (map (set o dels o effect) A\<^sub>i))) \<union> \<Union> (set (map (set o adds o effect) A\<^sub>i))"

  text \<open>Predicate to model that the given list happenings is
    executable, and transforms an initial world model \<open>M\<close> into a final
    model \<open>M'\<close>.

    Note that this definition over the list structure is more convenient in HOL
    than to explicitly define an indexed sequence \<open>M\<^sub>0\<dots>M\<^sub>N\<close> of intermediate world
    models, as done in [Lif87].
  \<close>
  fun valid_happ_seq :: "world_model \<Rightarrow> happening list \<Rightarrow> world_model \<Rightarrow> bool" where
    "valid_happ_seq M [] M' \<longleftrightarrow> (M = M')"
  | "valid_happ_seq M ((t\<^sub>i,A\<^sub>i)#hs) M' \<longleftrightarrow> 
      (\<forall>a\<in> set A\<^sub>i. M \<^sup>c\<TTurnstile>\<^sub>= precondition a)
      \<and> (pairwise acts_non_intrf (set A\<^sub>i))
      \<and> valid_happ_seq (apply_happ (t\<^sub>i,A\<^sub>i) M) hs M'"

  lemma valid_happ_seq_M\<^sub>j_is_M\<^sub>i:
    assumes "\<forall>h \<in> set hs. apply_happ h M\<^sub>i = M\<^sub>i" 
        and "valid_happ_seq M\<^sub>i hs M\<^sub>j"
    shows "M\<^sub>i = M\<^sub>j"
  using assms by (induction M\<^sub>i hs M\<^sub>j rule: valid_happ_seq.induct) auto

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>



subsection \<open>Well-Formedness of PDDL\<close>

(* Well-formedness *)

(*
  Compute signature: predicate/arity
  Check that all atoms (schemas and facts) satisfy signature

  for action:
    Check that used parameters \<subseteq> declared parameters

  for init/goal: Check that facts only use declared objects
*)


fun ty_term where
  "ty_term varT objT (term.VAR v) = varT v"
| "ty_term varT objT (term.CONST c) = objT c"


lemma ty_term_mono: "varT \<subseteq>\<^sub>m varT' \<Longrightarrow> objT \<subseteq>\<^sub>m objT' \<Longrightarrow>
  ty_term varT objT \<subseteq>\<^sub>m ty_term varT' objT'"
  apply (rule map_leI)
  subgoal for x v
    apply (cases x)
    apply (auto dest: map_leD)
    done
  done


context ast_domain begin

  text \<open>The signature is a partial function that maps the predicates
    of the domain to lists of argument types.\<close>
  definition sig :: "predicate \<rightharpoonup> type list" where
    "sig \<equiv> map_of (map (\<lambda>PredDecl p n \<Rightarrow> (p,n)) (predicates D))"

  definition func_sig :: "func \<rightharpoonup> type list" where
    "func_sig \<equiv> map_of (map (\<lambda>FuncDecl f n \<Rightarrow> (f,n)) (functions D))"

  text \<open>We use a flat subtype hierarchy, where every type is a subtype
    of object, and there are no other subtype relations.

    Note that we do not need to restrict this relation to declared types,
    as we will explicitly ensure that all types used in the problem are
    declared.
    \<close>

  fun subtype_edge where
    "subtype_edge (ty,superty) = (superty,ty)"

  definition "subtype_rel \<equiv> set (map subtype_edge (types D))"

  definition of_type :: "type \<Rightarrow> type \<Rightarrow> bool" where
    "of_type oT T \<equiv> set (primitives oT) \<subseteq> subtype_rel\<^sup>* `` set (primitives T)"
  text \<open>This checks that every primitive on the LHS is contained in or a
    subtype of a primitive on the RHS\<close>


  text \<open>For the next few definitions, we fix a partial function that maps
    a polymorphic entity type @{typ "'e"} to types. An entity can be
    instantiated by variables or objects later.\<close>
  context
    fixes ty_ent :: "'ent \<rightharpoonup> type"  \<comment> \<open>Entity's type, None if invalid\<close>
  begin

    text \<open>Checks whether an entity has a given type\<close>
    definition is_of_type :: "'ent \<Rightarrow> type \<Rightarrow> bool" where
      "is_of_type v T \<longleftrightarrow> (
        case ty_ent v of
          Some vT \<Rightarrow> of_type vT T
        | None \<Rightarrow> False)"

    fun wf_pred_atom :: "predicate \<times> 'ent list \<Rightarrow> bool" where
      "wf_pred_atom (p,vs) \<longleftrightarrow> (
        case sig p of
          None \<Rightarrow> False
        | Some Ts \<Rightarrow> list_all2 is_of_type vs Ts)"

    fun wf_func_args :: "func \<times> 'ent list \<Rightarrow> bool" where
      "wf_func_args (f,vs) \<longleftrightarrow> (
        case func_sig f of
          None \<Rightarrow> False
        | Some Ts \<Rightarrow> list_all2 is_of_type vs Ts)"

    text \<open>Predicate-atoms are well-formed if their arguments match the
      signature, equalities are well-formed if the arguments are valid
      objects (have a type).

      TODO: We could check that types may actually overlap
    \<close>
    fun wf_atom :: "'ent atom \<Rightarrow> bool" where
      "wf_atom (predAtm p vs) \<longleftrightarrow> wf_pred_atom (p,vs)"
    | "wf_atom (eqAtm a b) \<longleftrightarrow> ty_ent a \<noteq> None \<and> ty_ent b \<noteq> None"

    text \<open>A formula is well-formed if it consists of valid atoms,
      and does not contain negations, except for the encoding \<open>\<^bold>\<not>\<bottom>\<close> of true.
    \<close>
    fun wf_fmla :: "('ent atom) formula \<Rightarrow> bool" where
      "wf_fmla (Atom a) \<longleftrightarrow> wf_atom a"
    | "wf_fmla (\<bottom>) \<longleftrightarrow> True"
    | "wf_fmla (\<phi>1 \<^bold>\<and> \<phi>2) \<longleftrightarrow> (wf_fmla \<phi>1 \<and> wf_fmla \<phi>2)"
    | "wf_fmla (\<phi>1 \<^bold>\<or> \<phi>2) \<longleftrightarrow> (wf_fmla \<phi>1 \<and> wf_fmla \<phi>2)"
    | "wf_fmla (\<^bold>\<not>\<phi>) \<longleftrightarrow> wf_fmla \<phi>"
    | "wf_fmla (\<phi>1 \<^bold>\<rightarrow> \<phi>2) \<longleftrightarrow> (wf_fmla \<phi>1 \<and> wf_fmla \<phi>2)"

    lemma "wf_fmla \<phi> = (\<forall>a\<in>atoms \<phi>. wf_atom a)"
      by (induction \<phi>) auto

    (*lemma wf_fmla_add_simps[simp]: "wf_fmla (\<^bold>\<not>\<phi>) \<longleftrightarrow> \<phi>=\<bottom>"
      by (cases \<phi>) auto*)

    text \<open>Special case for a well-formed atomic predicate formula\<close>
    fun wf_fmla_atom where
      "wf_fmla_atom (Atom (predAtm a vs)) \<longleftrightarrow> wf_pred_atom (a,vs)"
    | "wf_fmla_atom _ \<longleftrightarrow> False"

    lemma wf_fmla_atom_alt: "wf_fmla_atom \<phi> \<longleftrightarrow> is_predAtom \<phi> \<and> wf_fmla \<phi>"
      by (cases \<phi> rule: wf_fmla_atom.cases) auto

    text \<open>An effect is well-formed if the added and removed formulas
      are atomic\<close>
    fun wf_effect where
      "wf_effect (Effect a d) \<longleftrightarrow> (\<forall>ae\<in>set a. wf_fmla_atom ae) \<and> (\<forall>de\<in>set d. wf_fmla_atom de)"

    fun wf_duration_const :: "'ent duration_constraint \<Rightarrow> bool" where
      "wf_duration_const No_Const \<longleftrightarrow> True"
    | "wf_duration_const (Time_Const op d) \<longleftrightarrow> d \<ge> 0"
    | "wf_duration_const (Func_Const op f vs) \<longleftrightarrow> 
        (case func_sig f of
            None \<Rightarrow> False
          | Some Ts \<Rightarrow> list_all2 is_of_type vs Ts)"

    definition "wf_duration_consts = list_all wf_duration_const" 
  end \<comment> \<open>Context fixing \<open>ty_ent\<close>\<close>


  definition constT :: "object \<rightharpoonup> type" where
    "constT \<equiv> map_of (consts D)"

  text \<open>An action schema is well-formed if the parameter names are distinct,
    and the precondition and effect is well-formed wrt.\ the parameters.
  \<close>
  fun wf_action_schema :: "ast_action_schema \<Rightarrow> bool" where
    "wf_action_schema (Simple_Action_Schema n params pre eff) \<longleftrightarrow> (
      let tyt = ty_term (map_of params) constT in
        distinct (map fst params)
      \<and> wf_fmla tyt pre
      \<and> wf_effect tyt eff)"
  | "wf_action_schema (Durative_Action_Schema n params d cond eff) \<longleftrightarrow> (
      let tyt = ty_term (map_of params) constT in
        distinct (map fst params)
      \<and> (\<forall>(t,c) \<in> set cond. wf_fmla tyt c)
      \<and> (\<forall>(t,e) \<in> set eff. wf_effect tyt e \<and> t \<noteq> Over_All)
      \<and> wf_duration_consts tyt d)"

  text \<open>A type is well-formed if it consists only of declared primitive types,
     and the type object.\<close>
  fun wf_type where
    "wf_type (Either Ts) \<longleftrightarrow> set Ts \<subseteq> insert (STR ''object'') (fst`set (types D))"

  text \<open>A predicate is well-formed if its argument types are well-formed.\<close>
  fun wf_predicate_decl where
    "wf_predicate_decl (PredDecl p Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. wf_type T)"

  text \<open>A function is well-formed if its argument types are well-formed.\<close>
  fun wf_function_decl where
    "wf_function_decl (FuncDecl f Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. wf_type T)"

  text \<open>The types declaration is well-formed, if all supertypes are declared types (or object)\<close>
  definition "wf_types \<equiv> snd`set (types D) \<subseteq> insert (STR ''object'') (fst`set (types D))"

  text \<open>A domain is well-formed if
    \<^item> there are no duplicate declared predicate names,
    \<^item> all declared predicates are well-formed,
    \<^item> there are no duplicate declared function names,
    \<^item> all declared functions are well-formed,
    \<^item> there are no duplicate action names,
    \<^item> and all declared actions are well-formed
    \<close>
  definition wf_domain :: "bool" where
    "wf_domain \<equiv>
      wf_types
    \<and> distinct (map (predicate_decl.pred) (predicates D))
    \<and> (\<forall>p\<in>set (predicates D). wf_predicate_decl p)
    \<and> distinct (map (function_decl.func) (functions D))
    \<and> (\<forall>f\<in>set (functions D). wf_function_decl f)
    \<and> distinct (map fst (consts D))
    \<and> (\<forall>(n,T)\<in>set (consts D). wf_type T)
    \<and> distinct (map ast_action_schema.name (actions D))
    \<and> (\<forall>a\<in>set (actions D). wf_action_schema a)
    "

end \<comment> \<open>locale \<open>ast_domain\<close>\<close>

text \<open>We fix a problem, and also include the definitions for the domain
  of this problem.\<close>
locale ast_problem = ast_domain "domain P"
  for P :: ast_problem
begin
  text \<open>We refer to the problem domain as \<open>D\<close>\<close>
  abbreviation "D \<equiv> ast_problem.domain P"

  definition objT :: "object \<rightharpoonup> type" where
    "objT \<equiv> map_of (objects P) ++ constT"

  lemma objT_alt: "objT = map_of (consts D @ objects P)"
    unfolding objT_def constT_def
    apply (clarsimp)
    done

  definition wf_fact :: "fact \<Rightarrow> bool" where
    "wf_fact = wf_pred_atom objT"

  fun wf_func_assign :: "object atom formula \<Rightarrow> bool" where 
    "wf_func_assign (Atom (eqAtm (FuncEnt f args) (TimeEnt d))) \<longleftrightarrow> wf_func_args objT (f,args)"
  | "wf_func_assign _ \<longleftrightarrow> False"

  lemma wf_func_assign_is_eqAtom: "wf_func_assign f \<Longrightarrow> is_eqAtom f"
    apply (cases f)
    apply auto
    apply (metis is_eqAtom.simps(1) wf_func_assign.elims(2))
    done

  text \<open>This definition is needed for well-formedness of the initial model,
    and forward-references to the concept of world model.
  \<close>
  definition wf_world_model where
    "wf_world_model M = (\<forall>f\<in>M. wf_fmla_atom objT f)" (* \<or> wf_func_assign f *)

  (*Note: current semantics assigns each object a unique type *)
  definition wf_problem where
    "wf_problem \<equiv>
      wf_domain
    \<and> distinct (map fst (objects P) @ map fst (consts D))
    \<and> (\<forall>(n,T)\<in>set (objects P). wf_type T)
    \<and> distinct (init P)
    \<and> (\<forall>f\<in>set (init P). wf_fmla_atom objT f \<or> wf_func_assign f)
    \<and> wf_fmla objT (goal P)" (* \<and> wf_world_model (set (init P)) *)

  fun wf_effect_inst :: "object ast_effect \<Rightarrow> bool" where
    "wf_effect_inst (Effect (a) (d)) \<longleftrightarrow> (\<forall>a\<in>set a \<union> set d. wf_fmla_atom objT a)"

  lemma wf_effect_inst_alt: "wf_effect_inst eff = wf_effect objT eff"
    by (cases eff) auto

end \<comment> \<open>locale \<open>ast_problem\<close>\<close>

text \<open>Locale to express a well-formed domain\<close>
locale wf_ast_domain = ast_domain +
  assumes wf_domain: wf_domain

text \<open>Locale to express a well-formed problem\<close>
locale wf_ast_problem = ast_problem P for P +
  assumes wf_problem: wf_problem
begin
  sublocale wf_ast_domain "domain P"
    apply unfold_locales
    using wf_problem
    unfolding wf_problem_def by simp

end \<comment> \<open>locale \<open>wf_ast_problem\<close>\<close>

subsection \<open>PDDL Semantics\<close>

(* Semantics *)

context ast_domain begin

  definition resolve_action_schema :: "name \<rightharpoonup> ast_action_schema" where
    "resolve_action_schema n = index_by ast_action_schema.name (actions D) n"

  fun subst_term where
    "subst_term psubst (term.VAR x) = psubst x"
  | "subst_term psubst (term.CONST c) = c"

  

  text \<open>To instantiate an action schema, we first compute a substitution from
    parameters to objects, and then apply this substitution to the
    precondition and effect. The substitution is applied via the \<open>map_xxx\<close>
    functions generated by the datatype package.
    \<close>
  fun instantiate_action_schema :: "ast_action_schema \<Rightarrow> object list \<Rightarrow> temporal_annotation \<Rightarrow> ground_action" where
    "instantiate_action_schema (Simple_Action_Schema n params pre eff) args ta = 
      (let
        tsubst = subst_term (the o (map_of (zip (map fst params) args)));
        pre_inst = (map_formula o map_atom) tsubst pre;
        eff_inst = (map_ast_effect) tsubst eff
      in
        Ground_Action n ta pre_inst eff_inst
      )"

  text \<open>Filter a given timed-list by a time specifier. 
  \texttt{(at start ...)}, \texttt{(at end ...)}, or \texttt{(over all ...)} conditions/effects\<close>
  definition filter_time_spec :: "temporal_annotation \<Rightarrow> (temporal_annotation \<times> 'a) list \<Rightarrow> 'a list" where
    "filter_time_spec t l = map snd (filter (((=) t) o fst) l)"

  lemma filter_time_spec_correct: "\<forall>x \<in> set (filter_time_spec t xs). (t,x) \<in> set xs"
    unfolding filter_time_spec_def
    by (induction xs arbitrary: t) auto

  text \<open>auxiliary-function to conjunct multiple effects into one single effect. 
  Needed to construct effect after filtering by a time specifier\<close>
  definition conjunct_effects :: "('a ast_effect) list \<Rightarrow> 'a ast_effect" ("\<And>\<^sub>e\<^sub>f\<^sub>f _" [40] 40) where
    "conjunct_effects l = Effect ((concat o (map adds)) l) ((concat o (map dels)) l)"

  text \<open>instantiate a given Durative Action Schema; 
  Note: if an action schema is well formed then the effect for the snap action for the 
  temporal annotation \texttt{(over all ...)} will be an empty effect (\texttt{Effect [] []})\<close>
  fun inst_snap_action :: "ast_action_schema \<Rightarrow> object list \<Rightarrow> temporal_annotation \<Rightarrow> ground_action" where
    "inst_snap_action (Durative_Action_Schema n params d cond eff) args ta = 
      (let 
        tsubst = subst_term (the o (map_of (zip (map fst params) args)));
        pre\<^sub>i = (map_formula o map_atom) tsubst (BigAnd (filter_time_spec ta cond));
        eff\<^sub>i = (map_ast_effect) tsubst (\<And>\<^sub>e\<^sub>f\<^sub>f (filter_time_spec ta eff)) 
      in 
        Ground_Action n ta pre\<^sub>i eff\<^sub>i
      )"

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

context wf_ast_domain begin
  text \<open>Resolving an action yields a well-founded action schema.\<close>
  (* TODO: This must be implicitly proved when showing that plan execution
    preserves wf. Try to remove this redundancy!*)
  lemma resolve_action_wf:
    assumes "resolve_action_schema n = Some a"
    shows "wf_action_schema a"
  proof -
    from wf_domain have
      X1: "distinct (map ast_action_schema.name (actions D))"
      and X2: "\<forall>a\<in>set (actions D). wf_action_schema a"
      unfolding wf_domain_def by auto

    show ?thesis
      using assms unfolding resolve_action_schema_def
      by (auto simp add: index_by_eq_Some_eq[OF X1] X2)
  qed

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

context ast_problem begin

  text \<open>Initial model\<close>
  definition I :: "world_model" where
    "I \<equiv> set (filter is_predAtom (init P))"


  text \<open>Resolve a plan action and instantiate the referenced action schema.\<close>
  fun res_inst :: "plan_action \<Rightarrow> temporal_annotation \<Rightarrow> ground_action option" where
    "res_inst (Simple_Plan_Action n args) ta =
      Some (instantiate_action_schema (the (resolve_action_schema n)) args ta)"
  | "res_inst (Durative_Plan_Action _ _ _) _ = None"

  (* resolve and instantiate a given Durative Plan Action *)
  fun res_inst_snap_action :: "plan_action \<Rightarrow> temporal_annotation \<rightharpoonup> ground_action" where
    "res_inst_snap_action (Durative_Plan_Action n args d) ta = 
      Some (inst_snap_action (the (resolve_action_schema n)) args ta)"
  | "res_inst_snap_action (Simple_Plan_Action _ _) _ = None"

  text \<open>Check whether object has specified type\<close>
  definition "is_obj_of_type n T \<equiv> case objT n of
    None \<Rightarrow> False
  | Some oT \<Rightarrow> of_type oT T"

  text \<open>We can also use the generic \<open>is_of_type\<close> function.\<close>
  lemma is_obj_of_type_alt: "is_obj_of_type = is_of_type objT"
    apply (intro ext)
    unfolding is_obj_of_type_def is_of_type_def by auto


  text \<open>HOL encoding of matching an action's formal parameters against an
    argument list.
    The parameters of the action are encoded as a list of \<open>name\<times>type\<close> pairs,
    such that we map it to a list of types first. Then, the list
    relator @{const list_all2} checks that arguments and types have the same
    length, and each matching pair of argument and type
    satisfies the predicate @{const is_obj_of_type}.
  \<close>
  definition "action_params_match a args
    \<equiv> list_all2 is_obj_of_type args (map snd (parameters a))"

  text \<open>All functions are required to be constant and defined in the initial state. 
  Therefore all duration constraints must be satisfied by the initial state.\<close>
  definition func_eval :: "object \<rightharpoonup> rat" where
    "func_eval \<equiv> map_of (fold (\<lambda>a fev. case a of Atom (eqAtm f (TimeEnt t)) \<Rightarrow> (f,t)#fev | _ \<Rightarrow> fev) (init P) [])"

  fun duration_matches :: "time \<Rightarrow> term duration_constraint \<Rightarrow> (variable \<times> type) list \<Rightarrow> object list \<Rightarrow> bool" where
    "duration_matches d No_Const params args \<longleftrightarrow> d \<ge> 0"
  | "duration_matches d (Time_Const op d') params args \<longleftrightarrow> 
      (case op of
        LEQ \<Rightarrow> d \<le> d'
      | EQ \<Rightarrow> d = d'
      | GEQ \<Rightarrow> d \<ge> d')"
  | "duration_matches d (Func_Const op f vs) params args \<longleftrightarrow>
      (let tsubst = subst_term (the o (map_of (zip (map fst params) args))) in
       case func_eval (FuncEnt f (map tsubst vs)) of 
          None \<Rightarrow> False 
        | Some d' \<Rightarrow> (case op of
            LEQ \<Rightarrow> d \<le> d'
          | EQ \<Rightarrow> d = d'
          | GEQ \<Rightarrow> d \<ge> d'))"

  definition "durations_match d xs params args = list_all (\<lambda>x. duration_matches d x params args) xs"

  text \<open>At this point, we can define well-formedness of a plan action:
    The action must refer to a declared action schema, the arguments must
    be compatible with the formal parameters' types.
  \<close>
 (* Objects are valid and match parameter types *)
  fun wf_plan_action :: "plan_action \<Rightarrow> bool" where
    "wf_plan_action (Simple_Plan_Action n args) = (
      case resolve_action_schema n of
        None \<Rightarrow> False
      | Some (Simple_Action_Schema n params pre eff) \<Rightarrow> 
          action_params_match (Simple_Action_Schema n params pre eff) args
      | Some (Durative_Action_Schema n params d cond eff) \<Rightarrow> False)"
    | "wf_plan_action (Durative_Plan_Action n args d) = (
      case resolve_action_schema n of
        None \<Rightarrow> False
      | Some (Simple_Action_Schema n params pre eff) \<Rightarrow> False
      | Some (Durative_Action_Schema n params dconst cond eff) \<Rightarrow> 
          action_params_match (Durative_Action_Schema n params dconst cond eff) args
          \<and> durations_match d dconst params args \<and> d \<ge> 0)"
  (* TODO: 'd \<ge> 0' is a hacky way to make sure all durations are non-negative; correct way 
  would be to check Function Assignments for durations constraints, maybe in wf_func_assign *)

  text \<open>A plan is wellformed if all plan actions are wellformed and all starting 
  time points are greater-equal 0.\<close>
  definition wf_plan :: "plan \<Rightarrow> bool" where
    "wf_plan \<pi>s \<longleftrightarrow> (\<forall>(t,\<pi>) \<in> set \<pi>s. wf_plan_action \<pi> \<and> t \<ge> 0)"

  definition is_act_simple :: "plan_action \<Rightarrow> bool" where
    "is_act_simple \<pi> \<longleftrightarrow> (case \<pi> of (Simple_Plan_Action _ _) \<Rightarrow> True | _ \<Rightarrow> False)"

  definition simple_acts :: "plan \<Rightarrow> (time \<times> plan_action) set" where 
    "simple_acts \<pi>s = set (filter (is_act_simple o snd) \<pi>s)"

  lemma simple_acts_subset: "simple_acts \<pi>s \<subseteq> set \<pi>s"
    unfolding simple_acts_def by auto

  definition durative_acts :: "plan \<Rightarrow> (time \<times> plan_action) set" where 
    "durative_acts \<pi>s = set (filter ((HOL.Not) o is_act_simple o snd) \<pi>s)"

  lemma dur_acts_subset: "durative_acts \<pi>s \<subseteq> set \<pi>s"
    unfolding durative_acts_def by auto

  lemma is_act_simple_alt: "is_act_simple = is_Simple_Plan_Action"
    unfolding is_act_simple_def
    apply (rule ext)
    by (auto split: plan_action.splits)
  
  text \<open>Definition of a happening time point. Happening time point specify time points at, 
  which the current state can change. Therefore every start and end of any plan action is 
  a happening time point.\<close>
  definition is_htp :: "plan \<Rightarrow> time \<Rightarrow> bool" where
    "is_htp \<pi>s t\<^sub>i \<longleftrightarrow> (\<exists>\<pi>. (t\<^sub>i,\<pi>) \<in> set \<pi>s) \<or> (\<exists>(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s. t\<^sub>i = t\<^sub>\<pi> + (duration \<pi>))"

  text\<open>Predicate for sequence of happening time points.\<close>
  definition htps_seq :: "plan \<Rightarrow> time list \<Rightarrow> bool" where
    "htps_seq \<pi>s htps \<longleftrightarrow> strict_sorted htps \<and> (\<forall>t. t \<in> set htps \<longleftrightarrow> is_htp \<pi>s t)"

  text \<open>Predicate for consecutive happening time points: There is no happening 
  time point in between.\<close>
  definition consec_htps :: "plan \<Rightarrow> time \<Rightarrow> time \<Rightarrow> bool" where
    "consec_htps \<pi>s t\<^sub>i t\<^sub>j 
      \<longleftrightarrow> (t\<^sub>i < t\<^sub>j \<and> is_htp \<pi>s t\<^sub>i \<and> is_htp \<pi>s t\<^sub>j \<and> (\<forall>t. is_htp \<pi>s t \<longrightarrow> t \<le> t\<^sub>i \<or> t\<^sub>j \<le> t))"

  (*
  abbreviation res_inst_snap_act_start_abbrev ("\<lfloor>_\<rfloor>\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t" 53) where
    "\<lfloor>\<pi>\<rfloor>\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t \<equiv> res_inst_snap_action \<pi> At_Start"

  abbreviation res_inst_snap_act_end_abbrev ("\<lfloor>_\<rfloor>\<^sub>e\<^sub>n\<^sub>d" 53) where
    "\<lfloor>\<pi>\<rfloor>\<^sub>e\<^sub>n\<^sub>d \<equiv> res_inst_snap_action \<pi> At_End"

  abbreviation res_inst_snap_act_inv_abbrev ("\<lfloor>_\<rfloor>\<^sub>i\<^sub>n\<^sub>v" 53) where
    "\<lfloor>\<pi>\<rfloor>\<^sub>i\<^sub>n\<^sub>v \<equiv> res_inst_snap_action \<pi> Over_All"*)

  text \<open>Predicate to check is a grounded action is a instantiation of a plan action 
  for an induced happening sequence.\<close>
  fun inst_of_plan_action :: "plan \<Rightarrow> time \<times> plan_action \<Rightarrow> time \<times> ground_action \<Rightarrow> bool" where
    "inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a) \<longleftrightarrow> (
      (res_inst \<pi> At_Start = Some a \<and> t\<^sub>\<pi> = t\<^sub>a)
      \<or> (res_inst_snap_action \<pi> At_Start = Some a \<and> t\<^sub>\<pi> = t\<^sub>a)
      \<or> (res_inst_snap_action \<pi> At_End = Some a \<and> t\<^sub>\<pi> + (duration \<pi>) = t\<^sub>a)
      \<or> (res_inst_snap_action \<pi> Over_All = Some a \<and> 
          (\<exists>t\<^sub>i t\<^sub>j. consec_htps \<pi>s t\<^sub>i t\<^sub>j \<and> t\<^sub>\<pi> \<le> t\<^sub>i \<and> t\<^sub>j \<le> t\<^sub>\<pi> + (duration \<pi>) \<and> t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j)))"

  (* experimented with shorter notations *)
  (*fun inst_of_plan_action :: "plan \<Rightarrow> time \<times> plan_action \<Rightarrow> time \<times> ground_action \<Rightarrow> bool" where
    "inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a) \<longleftrightarrow> (
      (res_inst \<pi> = Some a \<and> t\<^sub>\<pi> = t\<^sub>a)
      \<or> (\<lfloor>\<pi>\<rfloor>\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t = Some a \<and> t\<^sub>\<pi> = t\<^sub>a)
      \<or> (\<lfloor>\<pi>\<rfloor>\<^sub>e\<^sub>n\<^sub>d = Some a \<and> t\<^sub>\<pi> + (duration \<pi>) = t\<^sub>a)
      \<or> (\<lfloor>\<pi>\<rfloor>\<^sub>i\<^sub>n\<^sub>v = Some a \<and> (\<exists>t\<^sub>i t\<^sub>j. consec_htps \<pi>s t\<^sub>i t\<^sub>j \<and> t\<^sub>\<pi> \<le> t\<^sub>i \<and> t\<^sub>j \<le> t\<^sub>\<pi> + (duration \<pi>) \<and> t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j)))"*)

  abbreviation happ_member (infix "\<in>\<^sub>h" 53) where
    "ta \<in>\<^sub>h hs \<equiv> (case ta of (t,a) \<Rightarrow> (\<exists>as. (t,as) \<in> set hs \<and> a \<in> set as))"

  text \<open>Definition of an induced happening sequence. 
    \<^item> for every simple action $(t,\pi)$ there is an instantiation at time point $t$
    \<^item> for every durative action $(t,\pi)$
      \<^item> there is a ground action at time point $t$, 
          which contains all conditions and effect of $\pi$ with time specifier \texttt{(at start ...)}
      \<^item> there is a ground action at time point $t + (\texttt{duration}\ \pi)$, 
          which contains all conditions and effect of $\pi$ with time specifier \texttt{(at end ...)}
      \<^item> in between every consecutive happening-time-points $t_i$ $t_j$ during the execution of $\pi$
        there is a ground action at some time point $t'$ (in between $t_i$ \& $t_j$), 
          which contains all conditions of $\pi$ with time specifier \texttt{(over all ...)}, the effect of is empty
    \<^item> additionally an induced happening sequence is strictly sorted 
      and contains no other actions besides the ones specified above.
  \<close>
  definition ind_happ_seq :: "plan \<Rightarrow> happening list \<Rightarrow> bool" where
    "ind_happ_seq \<pi>s hs \<longleftrightarrow> (
      strict_sorted (map fst hs)
      \<and> (\<forall>(t\<^sub>\<pi>,\<pi>) \<in> simple_acts \<pi>s. 
          let 
            \<pi>\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t = the (res_inst \<pi> At_Start)
          in
          \<exists>A. (t\<^sub>\<pi>,A) \<in> set hs \<and> \<pi>\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t \<in> set A) 
      \<and> (\<forall>(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s. 
          let \<pi>\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t = the (res_inst_snap_action \<pi> At_Start);
              \<pi>\<^sub>e\<^sub>n\<^sub>d = the (res_inst_snap_action \<pi> At_End);
              \<pi>\<^sub>i\<^sub>n\<^sub>v = the (res_inst_snap_action \<pi> Over_All) in
          (\<exists>A. (t\<^sub>\<pi>,A) \<in> set hs \<and> \<pi>\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t \<in> set A) \<and> 
          (\<exists>A. (t\<^sub>\<pi> + (duration \<pi>),A) \<in> set hs \<and> \<pi>\<^sub>e\<^sub>n\<^sub>d \<in> set A) \<and> 
          (\<forall>t\<^sub>i t\<^sub>j. (consec_htps \<pi>s t\<^sub>i t\<^sub>j \<and> t\<^sub>\<pi> \<le> t\<^sub>i \<and> t\<^sub>j \<le> t\<^sub>\<pi> + (duration \<pi>)) 
            \<longrightarrow> (\<exists>(t',A) \<in> set hs. t\<^sub>i < t' \<and> t' < t\<^sub>j \<and> \<pi>\<^sub>i\<^sub>n\<^sub>v \<in> set A)))
      \<and> (\<forall>(t\<^sub>i,A\<^sub>i) \<in> set hs. A\<^sub>i \<noteq> [] \<and>
          (\<forall>a \<in> set A\<^sub>i. \<exists>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s. inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>i,a))))"

lemma ind_happ_seq_props:
  assumes "ind_happ_seq \<pi>s hs"
  shows "strict_sorted (map fst hs)"
        "(t\<^sub>\<pi>,\<pi>) \<in> simple_acts \<pi>s \<Longrightarrow> \<exists>A. (t\<^sub>\<pi>,A) \<in> set hs \<and> the (res_inst \<pi> At_Start) \<in> set A"
        "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s \<Longrightarrow> \<exists>A. (t\<^sub>\<pi>,A) \<in> set hs \<and> the (res_inst_snap_action \<pi> At_Start) \<in> set A"
        "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s \<Longrightarrow> \<exists>A. (t\<^sub>\<pi> + (duration \<pi>),A) \<in> set hs \<and> the (res_inst_snap_action \<pi> At_End) \<in> set A"
        "\<lbrakk>(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s; consec_htps \<pi>s t\<^sub>i t\<^sub>j ; t\<^sub>\<pi> \<le> t\<^sub>i ; t\<^sub>j \<le> t\<^sub>\<pi> + (duration \<pi>)\<rbrakk>
          \<Longrightarrow> \<exists>(t',A) \<in> set hs. t\<^sub>i < t' \<and> t' < t\<^sub>j \<and> the (res_inst_snap_action \<pi> Over_All) \<in> set A"
        "(t\<^sub>i,A\<^sub>i) \<in> set hs \<Longrightarrow> A\<^sub>i \<noteq> []"
        "\<lbrakk>(t\<^sub>i,A\<^sub>i) \<in> set hs ; a \<in> set A\<^sub>i\<rbrakk> \<Longrightarrow> \<exists>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s. inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>i,a)"
  using assms
  by(auto simp: ind_happ_seq_def)

  text \<open>A sequence of plan actions form a path, if they are well-formed and
    their instantiations form a path.\<close>
  definition plan_happ_path :: "world_model \<Rightarrow> plan \<Rightarrow> world_model \<Rightarrow> bool" where
    "plan_happ_path M \<pi>s M' \<longleftrightarrow> (\<exists>hs. ind_happ_seq \<pi>s hs \<and> valid_happ_seq M hs M')"

  text \<open>A plan is valid wrt.\ a given initial model, if it forms a path to a
    goal model \<close>
  definition valid_plan_from2 :: "world_model \<Rightarrow> plan \<Rightarrow> bool" where
    "valid_plan_from2 M \<pi>s \<longleftrightarrow> (wf_plan \<pi>s \<and> (\<exists>M'. plan_happ_path M \<pi>s M' \<and> M' \<^sup>c\<TTurnstile>\<^sub>= (goal P)))"

  text \<open>Finally, a plan is valid if it is valid wrt.\ the initial world
    model @{const I}\<close>
  definition valid_plan2 :: "plan \<Rightarrow> bool"
    where "valid_plan2 \<equiv> valid_plan_from2 I"
                                  
  text \<open>Concise definition used in paper:\<close>
  lemma "valid_plan2 \<pi>s \<equiv> wf_plan \<pi>s \<and> (\<exists>M'. plan_happ_path I \<pi>s M' \<and> M' \<^sup>c\<TTurnstile>\<^sub>= (goal P))"
    unfolding valid_plan2_def valid_plan_from2_def by auto

end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>


subsection \<open>Preservation of Well-Formedness\<close>

subsubsection \<open>Well-Formed Action Instances\<close>
text \<open>The goal of this section is to establish that well-formedness of
  world models is preserved by execution of well-formed plan actions.
\<close>

context ast_problem begin

  text \<open>As plan actions are executed by first instantiating them, and then
    executing the action instance, it is natural to define a well-formedness
    concept for action instances.\<close>

  fun wf_ground_action :: "ground_action \<Rightarrow> bool" where
    "wf_ground_action (Ground_Action _ _ pre eff) \<longleftrightarrow> (wf_fmla objT pre \<and> wf_effect objT eff)"

  text \<open>We first prove that instantiating a well-formed action schema will yield
    a well-formed action instance.

    We begin with some auxiliary lemmas before the actual theorem.
  \<close>

  lemma (in ast_domain) of_type_refl[simp, intro!]: "of_type T T"
    unfolding of_type_def by auto

  lemma (in ast_domain) of_type_trans[trans]:
    "of_type T1 T2 \<Longrightarrow> of_type T2 T3 \<Longrightarrow> of_type T1 T3"
    unfolding of_type_def
    by clarsimp (meson in_mono rtrancl_image_unfold_right rtrancl_reachable_induct) 

  lemma is_of_type_map_ofE:
    assumes "is_of_type (map_of params) x T"
    obtains i xT where "i<length params" "params!i = (x,xT)" "of_type xT T"
    using assms
    unfolding is_of_type_def
    by (auto split: option.splits dest!: map_of_SomeD simp: in_set_conv_nth)

  lemma wf_atom_mono:
    assumes SS: "tys \<subseteq>\<^sub>m tys'"
    assumes WF: "wf_atom tys a"
    shows "wf_atom tys' a"
  proof -
    have "list_all2 (is_of_type tys') xs Ts" if "list_all2 (is_of_type tys) xs Ts" for xs Ts
      using that
      apply induction
      by (auto simp: is_of_type_def split: option.splits dest: map_leD[OF SS])
    with WF show ?thesis
      by (cases a) (auto split: option.splits dest: map_leD[OF SS])
  qed

  lemma wf_fmla_atom_mono:
    assumes SS: "tys \<subseteq>\<^sub>m tys'"
    assumes WF: "wf_fmla_atom tys a"
    shows "wf_fmla_atom tys' a"
  proof -
    have "list_all2 (is_of_type tys') xs Ts" if "list_all2 (is_of_type tys) xs Ts" for xs Ts
      using that
      apply induction
      by (auto simp: is_of_type_def split: option.splits dest: map_leD[OF SS])
    with WF show ?thesis
      by (cases a rule: wf_fmla_atom.cases) (auto split: option.splits dest: map_leD[OF SS])
  qed


  lemma constT_ss_objT: "constT \<subseteq>\<^sub>m objT"
    unfolding constT_def objT_def
    apply rule
    by (auto simp: map_add_def split: option.split)

  lemma wf_atom_constT_imp_objT: "wf_atom (ty_term Q constT) a \<Longrightarrow> wf_atom (ty_term Q objT) a"
    apply (erule wf_atom_mono[rotated])
    apply (rule ty_term_mono)
    by (simp_all add: constT_ss_objT)

  lemma wf_fmla_atom_constT_imp_objT: "wf_fmla_atom (ty_term Q constT) a \<Longrightarrow> wf_fmla_atom (ty_term Q objT) a"
    apply (erule wf_fmla_atom_mono[rotated])
    apply (rule ty_term_mono)
    by (simp_all add: constT_ss_objT)

  context
    fixes Q and f :: "variable \<Rightarrow> object"
    assumes INST: "is_of_type Q x T \<Longrightarrow> is_of_type objT (f x) T"
  begin

    lemma is_of_type_var_conv: "is_of_type (ty_term Q objT) (term.VAR x) T  \<longleftrightarrow> is_of_type Q x T"
      unfolding is_of_type_def by (auto)

    lemma is_of_type_const_conv: "is_of_type (ty_term Q objT) (term.CONST x) T  \<longleftrightarrow> is_of_type objT x T"
      unfolding is_of_type_def
      by (auto split: option.split)

    lemma INST': "is_of_type (ty_term Q objT) x T \<Longrightarrow> is_of_type objT (subst_term f x) T"
      apply (cases x) using INST apply (auto simp: is_of_type_var_conv is_of_type_const_conv)
      done


    lemma wf_inst_eq_aux: "Q x = Some T \<Longrightarrow> objT (f x) \<noteq> None"
      using INST[of x T] unfolding is_of_type_def
      by (auto split: option.splits)

    lemma wf_inst_eq_aux': "ty_term Q objT x = Some T \<Longrightarrow> objT (subst_term f x) \<noteq> None"
      by (cases x) (auto simp: wf_inst_eq_aux)


    lemma wf_inst_atom:
      assumes "wf_atom (ty_term Q constT) a"
      shows "wf_atom objT (map_atom (subst_term f) a)"
    proof -
      have X1: "list_all2 (is_of_type objT) (map (subst_term f) xs) Ts" if
        "list_all2 (is_of_type (ty_term Q objT)) xs Ts" for xs Ts
        using that
        apply induction
        using INST'
        by auto
      then show ?thesis
        using assms[THEN wf_atom_constT_imp_objT] wf_inst_eq_aux'
        by (cases a; auto split: option.splits)

    qed

    lemma wf_inst_formula_atom:
      assumes "wf_fmla_atom (ty_term Q constT) a"
      shows "wf_fmla_atom objT ((map_formula o map_atom o subst_term) f a)"
      using assms[THEN wf_fmla_atom_constT_imp_objT] wf_inst_atom
      apply (cases a rule: wf_fmla_atom.cases; auto split: option.splits)
      by (simp add: INST' list.rel_map(1) list_all2_mono)

    lemma wf_inst_effect:
      assumes "wf_effect (ty_term Q constT) \<phi>"
      shows "wf_effect objT ((map_ast_effect o subst_term) f \<phi>)"
      using assms
      proof (induction \<phi>)
        case (Effect x1a x2a)
        then show ?case using wf_inst_formula_atom by auto
      qed

    lemma wf_inst_formula:
      assumes "wf_fmla (ty_term Q constT) \<phi>"
      shows "wf_fmla objT ((map_formula o map_atom o subst_term) f \<phi>)"
      using assms
      by (induction \<phi>) (auto simp: wf_inst_atom dest: wf_inst_eq_aux)

    lemma wf_BigAnd_aux: "\<forall>x \<in> set xs. wf_fmla tyt x \<Longrightarrow> wf_fmla tyt (BigAnd xs)"
      by (induction xs) auto

    lemma wf_BigAnd_filter_time_spec:
      fixes n params d cond eff
      defines "a \<equiv> Durative_Action_Schema n params d cond eff"  
      assumes "wf_action_schema a"
      shows "wf_fmla (ty_term (map_of params) constT) (BigAnd (filter_time_spec ta cond))"
      using assms filter_time_spec_correct wf_BigAnd_aux
      by (fastforce simp: Let_def)

    lemma wf_conjunct_effects_aux: "\<forall>x \<in> set xs. wf_effect tyt x \<Longrightarrow> wf_effect tyt (\<And>\<^sub>e\<^sub>f\<^sub>f xs)"
      unfolding conjunct_effects_def
      apply (induction xs) 
      apply auto
      apply (metis ast_effect.collapse wf_effect.simps)+
      done (* TODO: clean up *)

    lemma wf_conj_eff_filter_time_spec:
      fixes n params d cond eff
      defines "a \<equiv> Durative_Action_Schema n params d cond eff"  
      assumes "wf_action_schema a"
      shows "wf_effect (ty_term (map_of params) constT) (\<And>\<^sub>e\<^sub>f\<^sub>f (filter_time_spec ta eff))"
      using assms filter_time_spec_correct wf_conjunct_effects_aux
      by (fastforce simp: Let_def)

end

  text \<open>Next two theorems show that, instantiating a well-formed action schema 
  with compatible arguments will yield a well-formed action instance.\<close>
  theorem wf_inst_action_schema:
    fixes n params pre eff
    defines "a \<equiv> Simple_Action_Schema n params pre eff"  
    assumes "action_params_match a args"
    assumes "wf_action_schema a"
    shows "wf_ground_action (instantiate_action_schema a args ta)"
  proof -
    have INST:
      "is_of_type objT ((the \<circ> map_of (zip (map fst params) args)) x) T"
      if "is_of_type (map_of params) x T" for x T
      using that
      apply (rule is_of_type_map_ofE)
      using assms
      apply (clarsimp simp: Let_def)
      subgoal for i xT
        unfolding action_params_match_def
        apply (subst lookup_zip_idx_eq[where i=i];
          (clarsimp simp: list_all2_lengthD)?)
        apply (frule list_all2_nthD2[where p=i]; simp?)
        apply (auto
                simp: is_obj_of_type_alt is_of_type_def
                intro: of_type_trans
                split: option.splits)
        done
      done
    then show ?thesis
      using assms wf_inst_formula wf_inst_effect
      by (fastforce split: term.splits simp: Let_def comp_apply[abs_def])
  qed

  theorem wf_inst_durative_action_schema:
    fixes n params d cond eff
    defines "a \<equiv> Durative_Action_Schema n params d cond eff"  
    assumes "action_params_match a args"
    assumes "wf_action_schema a"
    shows "wf_ground_action (inst_snap_action a args ta)"
  proof -
    have INST:
      "is_of_type objT ((the \<circ> map_of (zip (map fst params) args)) x) T"
      if "is_of_type (map_of params) x T" for x T
      using that
      apply (rule is_of_type_map_ofE)
      using assms
      apply (clarsimp simp: Let_def)
      subgoal for i xT
        unfolding action_params_match_def
        apply (subst lookup_zip_idx_eq[where i=i];
          (clarsimp simp: list_all2_lengthD)?)
        apply (frule list_all2_nthD2[where p=i]; simp?)
        apply (auto
                simp: is_obj_of_type_alt is_of_type_def
                intro: of_type_trans
                split: option.splits)
        done
      done
    then show ?thesis
      using assms
        wf_inst_formula[OF _ wf_BigAnd_filter_time_spec, 
          where f1="\<lambda>x. the (map_of (zip (map fst params) args) x)" 
              and params1="params" and Q1="(map_of params)"]
        wf_inst_effect[OF _ wf_conj_eff_filter_time_spec, 
        where f1="\<lambda>x. the (map_of (zip (map fst params) args) x)" 
              and params1="params" and Q1="(map_of params)"]
      apply (auto split: term.splits simp: Let_def comp_apply[abs_def])
      done (* TODO: clean up proof! *)
  qed

  lemma wf_over_all_empty_eff:
    assumes "wf_plan_action \<pi> " 
        and "wf_action_schema a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a"
        and "Some a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a = resolve_action_schema (name \<pi>)"
        and "Some a = res_inst_snap_action \<pi> Over_All"
      shows "effect a = Effect [] []"
    using assms
  proof (cases a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a)
    case (Simple_Action_Schema n params pre eff)
    then show ?thesis
      using assms
      by (cases \<pi>) (auto split: option.splits)
  next
    case (Durative_Action_Schema n params d cond eff)
    then have "\<forall>(t,e) \<in> set eff. t \<noteq> Over_All"
      using \<open>wf_action_schema a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a\<close> by (auto simp: Let_def)
    then have "(\<And>\<^sub>e\<^sub>f\<^sub>f (filter_time_spec Over_All eff)) = Effect [] []"
      unfolding filter_time_spec_def conjunct_effects_def by auto
    then show ?thesis 
      using assms Durative_Action_Schema
      by (cases \<pi>) (auto split: option.splits) 
  qed
  
end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>



subsubsection \<open>Preservation\<close>

context ast_problem begin

  fun happ_precond :: "happening \<Rightarrow> world_model \<Rightarrow> bool" where
    "happ_precond (t,A) M \<longleftrightarrow> (\<forall>a \<in> set A. M \<^sup>c\<TTurnstile>\<^sub>= precondition a)"

  fun happ_non_intrf :: "happening \<Rightarrow> bool" where
    "happ_non_intrf (t,A) \<longleftrightarrow> (\<forall>a \<in> set A. \<forall>b \<in> set A. a \<noteq> b \<longrightarrow> acts_non_intrf a b)"

  text \<open>Shorthand for enabled happening: all preconditions satisfied, no interfering actions, 
    \& all ground actions are wellformed .\<close>
  fun happ_enabled :: "happening \<Rightarrow> world_model \<Rightarrow> bool" where 
    "happ_enabled (t,A) M \<longleftrightarrow> (happ_precond (t,A) M \<and> happ_non_intrf (t,A) \<and> (\<forall>a \<in> set A. wf_ground_action a))"
 
  text \<open>Shorthand for wellformed-ness of a happening sequence: all ground actions wellformed .\<close>
  fun wf_happ_seq :: "happening list \<Rightarrow> bool" where
    "wf_happ_seq hs \<longleftrightarrow> (\<forall>(t,A) \<in> set hs. (\<forall>a \<in> set A. wf_ground_action a))"

end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>

context wf_ast_problem begin
  text \<open>The initial world model is well-formed\<close>
  lemma wf_I: "wf_world_model I"
    using wf_problem
    unfolding I_def wf_world_model_def wf_problem_def
    apply(safe) 
    subgoal for f 
      apply (induction f) 
      apply auto
      by (metis is_predAtom.elims(2) wf_func_assign.simps(2))
    done

  (* get rid of this ugly lemma *)
  lemma wf_ground_action_wf_fmla_atom: 
    "wf_ground_action a \<Longrightarrow> \<forall>x \<in> set ((adds o effect) a). wf_fmla_atom objT x"
    using wf_effect_inst_alt[symmetric] wf_effect.elims(2)
    by (cases a) force

  text \<open>The Application of a happening preserves well-formedness\<close>
  theorem wf_apply_happ:
    assumes "happ_enabled (t,as) s" 
        and "wf_world_model s"
    shows "wf_world_model (apply_happ (t,as) s)"
    using assms wf_ground_action_wf_fmla_atom by (auto simp: wf_world_model_def)

  theorem wf_apply_happ_compact_notation:
    "happ_enabled (t,as) s \<Longrightarrow> wf_world_model s \<Longrightarrow> wf_world_model (apply_happ (t,as) s)"
    by (rule wf_apply_happ)

  corollary wf_valid_happ_seq:                                       
    assumes "wf_world_model M" 
        and "wf_happ_seq hs"
        and "valid_happ_seq M hs M'"
    shows "wf_world_model M'"
    using assms wf_apply_happ by (induction hs arbitrary: M) (auto split: prod.splits simp: pairwise_def)

  text \<open>In a wellformed plan the action parameters match for every plan action\<close>
  lemma wf_plan_action_params_match: 
    assumes "wf_plan \<pi>s" 
        and "(t,a) \<in> set \<pi>s" 
        and "a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a = the (resolve_action_schema (name a))"
    shows "action_params_match a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a (arguments a)"
    using assms by (cases a) (auto simp: wf_plan_def split: ast_action_schema.splits option.splits)

  lemma simple_plan_action_schema_type1:
    assumes "wf_plan_action (Simple_Plan_Action n args)"
    shows "\<exists>params pre eff. resolve_action_schema n = Some (Simple_Action_Schema n params pre eff)"
  proof (cases "resolve_action_schema n")
    case None
    then show ?thesis 
      using assms by auto
  next
    case (Some a)
    from wf_domain have [simp]: "distinct (map ast_action_schema.name (actions D))"
      unfolding wf_domain_def by auto
    then show ?thesis 
      using assms \<open>resolve_action_schema n = Some a\<close> resolve_action_schema_def
      by (cases a) fastforce+
  qed

  lemma durative_plan_action_schema_type1:
    assumes "wf_plan_action (Durative_Plan_Action n args t')"
    shows "\<exists>params d cond eff. resolve_action_schema n 
            = Some (Durative_Action_Schema n params d cond eff)"
  proof (cases "resolve_action_schema n")
    case None
    then show ?thesis 
      using assms by auto
  next
    case (Some a)
    from wf_domain have [simp]: "distinct (map ast_action_schema.name (actions D))"
      unfolding wf_domain_def by auto
    then show ?thesis 
      using assms \<open>resolve_action_schema n = Some a\<close> resolve_action_schema_def
      by (cases a) fastforce+
  qed

  text \<open>Instantiating a wellformed plan action always produces a wellformed ground action\<close>
  lemma wf_inst_of_plan_action:
    assumes "wf_plan \<pi>s" 
        and "(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s" 
        and "inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>i,a)"
    shows "wf_ground_action a"
    using assms
  proof -
    have wf_\<pi>: "wf_plan_action \<pi>"
      using assms wf_plan_def by blast
    obtain ta where "res_inst \<pi> ta = Some a \<or> res_inst_snap_action \<pi> ta = Some a"
      using assms by auto
    then show ?thesis
    proof (elim disjE)
      assume case_smpl_act: "res_inst \<pi> ta = Some a"
      then show ?thesis 
        proof (cases \<pi>)
          case (Simple_Plan_Action n args)
          then obtain params pre eff where 
                a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a_def: "resolve_action_schema n = Some (Simple_Action_Schema n params pre eff)"
            using wf_\<pi> simple_plan_action_schema_type1 Simple_Plan_Action by blast
          with wf_domain have "wf_action_schema (Simple_Action_Schema n params pre eff)"
            unfolding wf_domain_def using resolve_action_schema_def by force
          then show ?thesis
            using assms wf_\<pi> case_smpl_act a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a_def Simple_Plan_Action wf_inst_action_schema 
            by force 
        next
          case (Durative_Plan_Action n args d)
          then show ?thesis using case_smpl_act by auto
        qed
    next
      assume case_snp_act: "res_inst_snap_action \<pi> ta = Some a"
      then show ?thesis 
        proof (cases \<pi>)
          case (Simple_Plan_Action n args)
          then show ?thesis using case_snp_act by auto
        next
          case (Durative_Plan_Action n args d)
          then obtain params dcond cond eff where 
            a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a_def: "resolve_action_schema n = Some (Durative_Action_Schema n params dcond cond eff)"
            using wf_\<pi> durative_plan_action_schema_type1 by blast
          with wf_domain have "wf_action_schema (Durative_Action_Schema n params dcond cond eff)"
            unfolding wf_domain_def using resolve_action_schema_def by force                                           
          then show ?thesis
            using assms wf_\<pi> case_snp_act a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a_def Durative_Plan_Action wf_inst_durative_action_schema
            by force 
        qed
      qed
  qed

  text \<open>Every ground action in an induced happening sequence for a wellformed plan 
  is wellformed.\<close>
  lemma happ_seq_wf_ground_action: 
    assumes "wf_plan \<pi>s" 
        and "ind_happ_seq \<pi>s hs" 
        and "(t\<^sub>i,A\<^sub>i) \<in> set hs" 
        and "a \<in> set A\<^sub>i"
    shows "wf_ground_action a"
    unfolding ind_happ_seq_def
  proof -
    have "\<exists>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s. inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>i,a)"
      using assms ind_happ_seq_def by blast
    then obtain t\<^sub>\<pi> \<pi> where "(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s" and "inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>i,a)" by blast
    then show ?thesis 
      using assms wf_inst_of_plan_action
      by blast
  qed

  text \<open>An induced happening sequence for a wellformed plan is always a wellformed 
  happening sequence.\<close>
  lemma inst_wf_plan_wf_happ_seq: 
    assumes "wf_plan \<pi>s" 
        and "ind_happ_seq \<pi>s hs"
    shows "wf_happ_seq hs"
    unfolding Let_def simple_acts_def durative_acts_def is_act_simple_def
    using assms happ_seq_wf_ground_action by auto

  text \<open>Execution of a plan preserves well-formedness\<close>
  corollary wf_plan_happ_path:
    assumes "wf_world_model M" and "wf_plan \<pi>s" and "plan_happ_path M \<pi>s M'"
    shows "wf_world_model M'"
    using assms inst_wf_plan_wf_happ_seq wf_valid_happ_seq
    unfolding plan_happ_path_def by (induction \<pi>s arbitrary: M) blast+

end \<comment> \<open>Context of \<open>wf_ast_problem\<close>\<close>

  (* auxilirary functions *)
  text \<open>Auxiliary function that are used to divide happening sequences.\<close>
  definition "leq \<equiv> \<lambda>t\<^sub>i. \<lambda>(t\<^sub>a,as). t\<^sub>a \<le> t\<^sub>i"
  (*TODO: call this lt*)
  definition "le \<equiv> \<lambda>t\<^sub>i. \<lambda>(t\<^sub>a,as). t\<^sub>a < t\<^sub>i"

lemma strict_sorted_app_iff: "strict_sorted a \<and> strict_sorted b \<and> (\<forall>x \<in> set a. \<forall>y \<in> set b. x < y)
          \<longleftrightarrow> strict_sorted (a @ b)"
  by (induction a arbitrary: b) auto

lemma empty_filter_conv: "[] = filter P xs \<longleftrightarrow> (\<forall>x\<in>set xs. \<not> P x)"
  by(auto dest: sym simp add: filter_empty_conv)



subsubsection \<open>Completeness of Semantics\<close>


context wf_ast_problem
begin

fun consume2 where
"consume2 [] [] = 0"
|  "consume2 (x#xs) (y#ys) = 0 + consume2 xs ys"

lemma empty_happ:
 "(\<And>a. a \<in> set A \<Longrightarrow> effect a = Effect [] []) \<Longrightarrow> apply_happ (t, A) M = M"
  by (induction A) auto

lemma valid_happ_seq_append_1:
  "\<lbrakk>\<And>t A a.\<lbrakk>(t, A) \<in> set hs1; a \<in> set A\<rbrakk> \<Longrightarrow> effect a = Effect [] [];
        valid_happ_seq M hs2 M';
        (\<And>t A a. \<lbrakk> (t, A) \<in> set hs1; a\<in> set A\<rbrakk> \<Longrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= precondition a);
        (\<And>t A a. (t, A) \<in> set hs1 \<Longrightarrow> pairwise acts_non_intrf (set A)) \<rbrakk> \<Longrightarrow>
        valid_happ_seq M (hs1 @ hs2) M'"
  by (induction hs1 arbitrary: M) (fastforce simp del: apply_happ.simps simp add: empty_happ)+

lemma valid_happ_seq_append_2:
  "\<lbrakk> valid_happ_seq M (hs1 @ hs2) M'; \<And>t A a.\<lbrakk>(t, A) \<in> set hs1; a \<in> set A\<rbrakk> \<Longrightarrow> effect a = Effect [] []\<rbrakk> \<Longrightarrow>
        valid_happ_seq M hs2 M'"
  by (induction hs1 arbitrary: M) (fastforce simp del: apply_happ.simps simp add: empty_happ)+

lemma valid_happ_seq_append_2':
  "\<lbrakk> valid_happ_seq M (hs1 @ hs2) M'; \<And>t A a.\<lbrakk>(t, A) \<in> set hs2; a \<in> set A\<rbrakk> \<Longrightarrow> effect a = Effect [] []\<rbrakk> \<Longrightarrow>
        valid_happ_seq M hs1 M'"
  apply (induction hs1 arbitrary: hs2 M M') 
  apply (auto simp del: apply_happ.simps simp add: empty_happ)
  by (metis empty_happ old.prod.exhaust valid_happ_seq_M\<^sub>j_is_M\<^sub>i)+

lemma valid_happ_seq_append_3:
  "\<lbrakk>(t, A) \<in> set hs1; a\<in> set A; valid_happ_seq M (hs1 @ hs2) M';
    \<And>t A a.\<lbrakk>(t, A) \<in> set hs1; a \<in> set A\<rbrakk> \<Longrightarrow> effect a = Effect [] []\<rbrakk>
    \<Longrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= precondition a"
  by (induction hs1 arbitrary: M) (fastforce simp del: apply_happ.simps simp add: empty_happ)+

lemma valid_happ_seq_append_4:
  "\<lbrakk>valid_happ_seq M (hs1 @ hs2) M'; \<And>t A a.\<lbrakk>(t, A) \<in> set hs1; a \<in> set A\<rbrakk> \<Longrightarrow> effect a = Effect [] []\<rbrakk> \<Longrightarrow>
    (\<And>t A a. (t, A) \<in> set hs1 \<Longrightarrow> pairwise acts_non_intrf (set A))"
  by (induction hs1 arbitrary: M) (fastforce simp del: apply_happ.simps simp add: empty_happ)+

lemma valid_happ_seq_empty_eff:
  "\<lbrakk>\<And>t A a.\<lbrakk>(t, A) \<in> set hs; a \<in> set A\<rbrakk> \<Longrightarrow> effect a = Effect [] [];
        (\<And>t A a. \<lbrakk> (t, A) \<in> set hs; a\<in> set A\<rbrakk> \<Longrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= precondition a);
        (\<And>t A a. (t, A) \<in> set hs \<Longrightarrow> pairwise acts_non_intrf (set A)) \<rbrakk> \<Longrightarrow>
        valid_happ_seq M hs M"  
  by (induction hs) (fastforce simp del: apply_happ.simps simp add: empty_happ)+

lemma valid_happ_seq_append_5:
  "\<lbrakk>\<And>t A a.\<lbrakk>(t, A) \<in> set hs2; a \<in> set A\<rbrakk> \<Longrightarrow> effect a = Effect [] [];
        valid_happ_seq M hs1 M';
        (\<And>t A a. \<lbrakk> (t, A) \<in> set hs2; a\<in> set A\<rbrakk> \<Longrightarrow> M' \<^sup>c\<TTurnstile>\<^sub>= precondition a);
        (\<And>t A a. (t, A) \<in> set hs2 \<Longrightarrow> pairwise acts_non_intrf (set A)) \<rbrakk> \<Longrightarrow>
        valid_happ_seq M (hs1 @ hs2) M'"  
  by (induction hs1 arbitrary: M)
     (auto simp del: apply_happ.simps simp add: empty_happ intro!: valid_happ_seq_empty_eff)

lemma strict_sorted_cons: "\<lbrakk>strict_sorted (map f (x # xs)); x' \<in> set xs\<rbrakk> \<Longrightarrow> f x \<noteq> f x'"
  by (induction xs) auto

lemma strict_sorted_order:
      "\<lbrakk>(\<And>x. x \<in> s \<Longrightarrow> \<exists>y \<in> set (x1 # xs1 @ x2 # xs2). f y = x); strict_sorted (map f (x1 # xs1 @ x2 # xs2));
        (\<And>y. y \<in> set xs1 \<Longrightarrow> f y \<notin> s); x \<in> s; x < f x2\<rbrakk> \<Longrightarrow> x = f x1"
  by (fastforce simp: image_def strict_sorted_app_iff[symmetric])

lemma in_suff:
  "\<lbrakk>\<And>x. x \<in> set xs1 \<Longrightarrow> x \<noteq> x2; x2 \<in> set (xs1 @ xs2)\<rbrakk> \<Longrightarrow> x2 \<in> set xs2"
  by auto

lemma strict_sorted_order_in_suff:
  "\<lbrakk>strict_sorted (xs1 @ xs2); x1 \<in> set xs1; x2 \<in> set xs2\<rbrakk> \<Longrightarrow> x1 < x2"
  by (induction xs1) (auto simp: image_def strict_sorted_app_iff[symmetric])

lemma empty_eff_non_intrf:
  "\<lbrakk>\<And>a. a \<in> A \<Longrightarrow> effect a = Effect [] []\<rbrakk> \<Longrightarrow> pairwise acts_non_intrf A"
  by (auto simp: pairwise_def acts_non_intrf_def)

lemma filter_eq_consD: "x # l' = filter Q l \<Longrightarrow> x\<in>set l \<and> Q x"
  by (induction l) (auto split: if_splits)

lemma valid_hap_seq_construct:
  assumes "\<And>t. t \<in> htps \<Longrightarrow> \<exists>A. (t, A) \<in> set hs"
    and "\<And>t. t \<in> htps \<Longrightarrow> \<exists>A. (t, A) \<in> set hs'"
    and "strict_sorted (map fst hs)"
    and "strict_sorted (map fst hs')"
    and "\<And>t A A'. \<lbrakk>t \<in> htps; (t, A) \<in> set hs; (t, A') \<in> set hs'\<rbrakk> \<Longrightarrow> set A = set A'"
    and "\<And>t A A' a. \<lbrakk>t \<notin> htps; (t, A) \<in> set hs; a \<in> set A\<rbrakk> \<Longrightarrow> effect a = Effect [] []"
    and "\<And>t A A' a. \<lbrakk>t \<notin> htps; (t, A) \<in> set hs'; a \<in> set A\<rbrakk> \<Longrightarrow> effect a = Effect [] []"
    and "\<And>t A t\<^sub>1 t\<^sub>2 a.
            \<lbrakk>t \<notin> htps; t\<^sub>1 \<in> htps; t\<^sub>2 \<in> htps; t \<in> {t\<^sub>1<..< t\<^sub>2}; (t, A) \<in> set hs; a \<in> set A\<rbrakk> \<Longrightarrow> 
              \<exists>t'\<in>{t\<^sub>1<..< t\<^sub>2}.\<exists>A'. (t',A') \<in> set hs' \<and> a \<in> set A'"
    and "\<And>t A t\<^sub>1 t\<^sub>2 a.
            \<lbrakk>t \<notin> htps; t\<^sub>1 \<in> htps; t\<^sub>2 \<in> htps; t \<in> {t\<^sub>1<..< t\<^sub>2}; (t, A) \<in> set hs'; a \<in> set A\<rbrakk> \<Longrightarrow> 
              \<exists>t'\<in>{t\<^sub>1<..< t\<^sub>2}.\<exists>A'. (t',A') \<in> set hs \<and> a \<in> set A'"
    and "valid_happ_seq M hs M'"
    and "hs \<noteq> [] \<Longrightarrow> (fst (hd hs)) \<in> htps"
    and "hs' \<noteq> [] \<Longrightarrow> (fst (hd hs')) \<in> htps"
    and "hs \<noteq> [] \<Longrightarrow> (fst (last hs)) \<in> htps"
    and "hs' \<noteq> [] \<Longrightarrow> (fst (last hs')) \<in> htps"
  shows "valid_happ_seq M hs' M'"
  using assms
proof(induction "filter (\<lambda>h. fst h \<in> htps) hs" "filter (\<lambda>h. fst h \<in> htps) hs'"
    arbitrary: M hs hs' htps rule: consume2.induct)
  case (2 h xs h' ys hs hs' htps M)
  then obtain hs1 hs2 hs1' hs2'
    where "hs = hs1 @ h # hs2" "(\<forall>h\<in>set hs1. fst h \<notin> htps)"
      "fst h \<in> htps" "xs = filter (\<lambda>h. fst h \<in> htps) hs2"

      "hs' = hs1' @ h' # hs2'" "(\<forall>h\<in>set hs1'. fst h \<notin> htps)"
      "fst h' \<in> htps" "ys = filter (\<lambda>h. fst h \<in> htps) hs2'"
    by (auto simp: Cons_eq_filter_iff)
  hence [simp]: "hs1 = []" "hs1' = []"
    using \<open>hs' \<noteq> [] \<Longrightarrow> fst (hd hs') \<in> htps\<close> \<open>hs \<noteq> [] \<Longrightarrow> fst (hd hs) \<in> htps\<close>
     apply -
    by (rule list.exhaust, auto)+

  note [simp] = \<open>hs = hs1 @ h # hs2\<close> \<open>hs' = hs1' @ h' # hs2'\<close>

  obtain t t' A A' where *[simp]: "h = (t, A)" "h' = (t',A')"
    by (cases h, cases h', auto)
  hence in_htp: "t\<in>htps" "t'\<in>htps"
    using \<open>fst h \<in> htps\<close> \<open>fst h' \<in> htps\<close>
    by auto
  moreover have "\<And>t. t \<in> htps \<Longrightarrow> \<exists>A. (t, A) \<in> set (h # hs2)"
                "\<And>t. t \<in> htps \<Longrightarrow> \<exists>A. (t, A) \<in> set (h' # hs2')"
    using 2(4,5) \<open>(\<forall>h\<in>set hs1. fst h \<notin> htps)\<close> \<open>(\<forall>h\<in>set hs1'. fst h \<notin> htps)\<close>
    by fastforce+
  moreover have "strict_sorted (map fst (h#hs2))" "strict_sorted (map fst (h'#hs2'))"
    using 2(6,7) 
    by (auto simp: strict_sorted_app_iff[symmetric])
  ultimately have [simp]: "t = t'"
    by force
  hence A_eq: "set A = set A'"
    using 2(8) in_htp
    by auto
  moreover have "valid_happ_seq M (h # hs2) M'"
    using 2(9) \<open>valid_happ_seq M hs M'\<close> \<open>(\<forall>h\<in>set hs1. fst h \<notin> htps)\<close>
    by (force simp: intro!: valid_happ_seq_append_2[where ?hs1.0 = hs1])+
  ultimately have "valid_happ_seq M [h] (apply_happ (t, A') M)"
    using \<open>h = (t,A)\<close> A_eq
    by auto
  hence "valid_happ_seq M [h'] (apply_happ (t, A') M)"
    using \<open>h = (t,A)\<close> A_eq
    by auto

  show ?case
  proof(cases "xs")
    case Nil
    hence "set (map fst hs2) \<inter> htps = {}"
      using \<open>xs = filter (\<lambda>h. fst h \<in> htps) hs2\<close>
      by (auto simp add: filter_empty_conv)
    hence "M' = (apply_happ (t, A') M)"
      using \<open>valid_happ_seq M hs M'\<close> \<open>valid_happ_seq M [h] (apply_happ (t, A') M)\<close>
             \<open>hs \<noteq> [] \<Longrightarrow> fst (last hs) \<in> htps\<close>
      by (auto split: if_splits)
    moreover from \<open>set (map fst hs2) \<inter> htps = {}\<close> have "set (map fst hs2') \<inter> htps = {}"
      using \<open>\<And>t. t \<in> htps \<Longrightarrow> \<exists>A. (t, A) \<in> set (h # hs2)\<close> \<open>fst h' \<in> htps\<close>
        strict_sorted_cons[OF \<open>strict_sorted (map fst (h'#hs2'))\<close>]
      by (simp add: disjoint_iff_not_equal) (metis fst_conv)
    ultimately show ?thesis
      using \<open>hs' \<noteq> [] \<Longrightarrow> fst (last hs') \<in> htps\<close> \<open>valid_happ_seq M [h'] (apply_happ (t, A') M)\<close>
      by (auto split: if_splits)
  next
    case (Cons h2 xs')
    then obtain hs3 hs4
      where "hs2 = hs3 @ h2 # hs4" "(\<forall>h\<in>set hs3. fst h \<notin> htps)"
        "fst h2 \<in> htps" "xs' = filter (\<lambda>h. fst h \<in> htps) hs4"
      using \<open>xs = filter (\<lambda>h. fst h \<in> htps) hs2\<close>
      by (auto simp: filter_eq_Cons_iff)
    moreover hence "fst h2 \<noteq> fst h"
      using \<open>strict_sorted (map fst (h # hs2))\<close>
      by auto
    hence "fst h2 \<noteq> fst h'"
      using \<open>t = t'\<close>
      by auto
    ultimately obtain A2' where "(fst h2, A2') \<in> set hs2'"
      using \<open>\<And>t. t \<in> htps \<Longrightarrow> \<exists>A. (t, A) \<in> set (h' # hs2')\<close>
      by (cases h2, cases h', auto simp add: disjoint_iff_not_equal)
    then obtain hs3' hs4' where [simp]: "hs2' = hs3' @ (fst h2, A2') # hs4'"
      by (auto dest: split_list_first)

    note[simp] = \<open>hs2 = hs3 @ h2 # hs4\<close> strict_sorted_app_iff[symmetric]

    have fst_h3'_n_htp: "fst h3' \<notin> htps" if "h3'\<in>set hs3'" for h3'
    proof(rule ccontr, safe)
      assume "fst h3' \<in> htps"
      hence "fst h3' < fst h2"
        using that \<open>strict_sorted (map fst hs')\<close>
        by auto
      moreover have "x \<in> htps \<Longrightarrow> \<exists>y\<in>set (h # hs3 @ h2 # hs4). fst y = x" for x
        using \<open>\<And>t. t \<in> htps \<Longrightarrow> \<exists>A. (t, A) \<in> set (h # hs2)\<close>
        by force
      ultimately have "fst h3' = fst h"
        using \<open>fst h3' \<in> htps\<close> \<open>\<forall>h\<in>set hs3. fst h \<notin> htps\<close> \<open>strict_sorted (map fst hs)\<close>
        by (auto simp: simp del: *
                 intro!: strict_sorted_order[where s = htps and ?xs1.0 = "hs3" and ?x2.0 = "h2" and ?xs2.0 = "hs4"])+
      thus False
        using that \<open>strict_sorted (map fst hs')\<close>
        by auto
    qed

    define hs_IH where "hs_IH \<equiv> h2 # hs4"
    define hs'_IH where "hs'_IH \<equiv> (fst h2, A2') # hs4'"
    define htps_IH where "htps_IH \<equiv> htps - {t}"
    define M_IH where "M_IH \<equiv> (apply_happ (t, A') M)"
    have [dest]:"\<And>h'. h' \<in> set (hs_IH) \<Longrightarrow> t \<noteq> fst h'"
      using \<open>strict_sorted (map fst hs)\<close>
      by (auto simp: hs_IH_def)
    have "\<And>h'. h' \<in> set (hs'_IH) \<Longrightarrow> t' \<noteq> fst h'"
      using \<open>strict_sorted (map fst hs')\<close>
      by (auto simp: hs'_IH_def)

    have "xs = filter (\<lambda>h. fst h \<in> htps_IH) (hs_IH)" (is "?xs = ?fil_xs (\<lambda>h. fst h \<in> htps_IH)")
    proof-
      have "?fil_xs (\<lambda>h. fst h \<in> htps_IH) = ?fil_xs (\<lambda>h. fst h \<in> htps)"
        by (fastforce intro!: filter_cong simp: htps_IH_def)
      also have "... = filter (\<lambda>h. fst h \<in> htps) hs2"
        using Cons \<open>(\<forall>h\<in>set hs3. fst h \<notin> htps)\<close>
        by (auto simp: hs_IH_def)
      finally show ?thesis
        using Cons
        by (simp add: \<open>xs = filter (\<lambda>h. fst h \<in> htps) hs2\<close>)
    qed
    moreover have "ys = filter (\<lambda>h. fst h \<in> htps_IH) (hs'_IH)" (is "?ys = ?fil_ys (\<lambda>h. fst h \<in> htps_IH)")
    proof-
      have "?fil_ys (\<lambda>h. fst h \<in> htps - {t'}) = ?fil_ys (\<lambda>h. fst h \<in> htps)"
        using \<open>\<And>h'. h' \<in> set (hs'_IH) \<Longrightarrow> t' \<noteq> fst h'\<close>
        by (force intro!: filter_cong)
      also have "... = filter (\<lambda>h. fst h \<in> htps) hs2'"
        using Cons fst_h3'_n_htp
        by (auto simp: hs'_IH_def)
      finally show ?thesis
        using Cons
        by (simp add: \<open>ys = filter (\<lambda>h. fst h \<in> htps) hs2'\<close> htps_IH_def)
    qed
    moreover have "\<And>t'. t' \<in> htps_IH \<Longrightarrow> \<exists>A. (t', A) \<in> set (hs_IH)"
      using \<open>(\<forall>h\<in>set hs3. fst h \<notin> htps)\<close>
        \<open>\<And>t. t \<in> htps \<Longrightarrow> \<exists>A. (t, A) \<in> set (h # hs2)\<close>
        \<open>\<And>h'. h' \<in> set (hs_IH) \<Longrightarrow> t \<noteq> fst h'\<close>
      by (fastforce simp: hs_IH_def htps_IH_def)
    moreover have "\<And>t''. t'' \<in> htps_IH \<Longrightarrow> \<exists>A. (t'', A) \<in> set (hs'_IH)"
      using fst_h3'_n_htp
        \<open>\<And>t. t \<in> htps \<Longrightarrow> \<exists>A. (t, A) \<in> set (h' # hs2')\<close>
      by (fastforce simp: hs'_IH_def htps_IH_def)
    moreover have "strict_sorted (map fst (hs_IH))"
      using \<open>strict_sorted (map fst hs)\<close>
      by (auto simp: hs_IH_def htps_IH_def)
    moreover have "strict_sorted (map fst (hs'_IH))"
      using \<open>strict_sorted (map fst hs')\<close>
      by (auto simp: hs'_IH_def htps_IH_def)
    moreover have
      "\<And> t'' A'' A'''. \<lbrakk>t'' \<in> htps_IH; (t'', A'') \<in> set (hs_IH); (t'', A''') \<in> set (hs'_IH)\<rbrakk> \<Longrightarrow> set A'' = set A'''"
      using 2(8)
      by (auto simp: htps_IH_def hs_IH_def hs'_IH_def)
    moreover have "\<And>t'' A'' a. \<lbrakk>t'' \<notin> htps_IH; (t'', A'') \<in> set (hs_IH); a \<in> set A''\<rbrakk> \<Longrightarrow> effect a = Effect [] []"
      using 2(9) \<open>fst h2 \<in> htps\<close> \<open>\<And>h'. h' \<in> set (hs_IH) \<Longrightarrow> t \<noteq> fst h'\<close>
      by (fastforce simp add: htps_IH_def hs_IH_def)
    moreover have "\<And>t'' A'' a. \<lbrakk>t'' \<notin> htps_IH; (t'', A'') \<in> set (hs'_IH); a \<in> set A''\<rbrakk> \<Longrightarrow> effect a = Effect [] []"
      using 2(10) \<open>fst h2 \<in> htps\<close> \<open>\<And>h'. h' \<in> set (hs'_IH) \<Longrightarrow> t' \<noteq> fst h'\<close>
      by (force simp add: htps_IH_def hs'_IH_def)
    moreover have "\<exists>t'\<in>{t\<^sub>1<..< t\<^sub>2}.\<exists>A'. (t',A') \<in> set hs'_IH \<and> a \<in> set A'"
      if "t'' \<notin> htps_IH" "t\<^sub>1 \<in> htps_IH" "t\<^sub>2 \<in> htps_IH" "t'' \<in> {t\<^sub>1<..< t\<^sub>2}" "(t'', A'') \<in> set hs_IH"
        "a \<in> set A''"
      for t'' A'' t\<^sub>1 t\<^sub>2 a
    proof-
      have "t'' \<notin> htps"
        using \<open>\<And>h'. h' \<in> set (hs_IH) \<Longrightarrow> t \<noteq> fst h'\<close> \<open>t'' \<notin> htps_IH\<close> \<open>(t'', A'') \<in> set hs_IH\<close>
        by (fastforce simp: htps_IH_def)
      hence "\<exists>t'\<in>{t\<^sub>1<..< t\<^sub>2}.\<exists>A'. (t',A') \<in> set hs' \<and> a \<in> set A'"
        using that
        by (auto simp del: \<open>hs' = hs1' @ h' # hs2'\<close> simp: htps_IH_def hs_IH_def intro!: 2(11))
      then obtain t''' A''' where "t''' \<in> {t\<^sub>1<..< t\<^sub>2}" "(t''',A''') \<in> set hs'" "a \<in> set A'''"
        by (auto simp del: \<open>hs' = hs1' @ h' # hs2'\<close>)
      hence "t\<^sub>1 < t'''"
        by auto
      moreover have "t' < t\<^sub>1"
        using \<open>t\<^sub>1 \<in> htps_IH\<close> \<open>\<And>t. t \<in> htps \<Longrightarrow> \<exists>A. (t, A) \<in> set (h # hs2)\<close> \<open>strict_sorted (map fst hs)\<close>
        by(fastforce simp: htps_IH_def)
      hence "t\<^sub>1 \<in> set (map fst hs'_IH)"
        using fst_h3'_n_htp \<open>t\<^sub>1 \<in> htps_IH\<close> \<open>\<And>t''. t'' \<in> htps_IH \<Longrightarrow> \<exists>A. (t'', A) \<in> set hs'_IH\<close>
        by (fastforce simp: image_def hs'_IH_def htps_IH_def)+
      hence "\<And>h3'. h3' \<in> set hs3' \<Longrightarrow> fst h3' < t\<^sub>1"
        using \<open>strict_sorted (map fst hs')\<close>
        by (auto simp: hs'_IH_def)
      ultimately have "t''' \<notin> set (map fst hs3')"
        by fastforce
      thus ?thesis 
        using \<open>(t''',A''') \<in> set hs'\<close> \<open>t' < t\<^sub>1\<close> \<open>t\<^sub>1 < t'''\<close> \<open>t''' \<in> {t\<^sub>1<..< t\<^sub>2}\<close> \<open>a \<in> set A'''\<close>
        by (auto simp: hs'_IH_def)+
    qed
      (*TODO: this is exactly symmetric to the last statement. Refactor them *)
    moreover have "\<exists>t'\<in>{t\<^sub>1<..< t\<^sub>2}.\<exists>A'. (t',A') \<in> set hs_IH \<and> a \<in> set A'"
      if "t'' \<notin> htps_IH" "t\<^sub>1 \<in> htps_IH" "t\<^sub>2 \<in> htps_IH" "t'' \<in> {t\<^sub>1<..< t\<^sub>2}" "(t'', A'') \<in> set hs'_IH"
        "a \<in> set A''"
      for t'' A'' t\<^sub>1 t\<^sub>2 a
    proof-
      have "t'' \<notin> htps"
        using \<open>\<And>h'. h' \<in> set (hs'_IH) \<Longrightarrow> t' \<noteq> fst h'\<close> \<open>t'' \<notin> htps_IH\<close> \<open>(t'', A'') \<in> set hs'_IH\<close>
        by (fastforce simp: htps_IH_def)        
      hence "\<exists>t'\<in>{t\<^sub>1<..< t\<^sub>2}.\<exists>A'. (t',A') \<in> set hs \<and> a \<in> set A'"
        using that
        by (auto simp del: \<open>hs = hs1 @ h # hs2\<close> simp: htps_IH_def hs'_IH_def intro!: 2(12))
      then obtain t''' A''' where "t''' \<in> {t\<^sub>1<..< t\<^sub>2}" "(t''',A''') \<in> set hs" "a \<in> set A'''"
        by (auto simp del: \<open>hs = hs1 @ h # hs2\<close>)
      hence "t\<^sub>1 < t'''"
        by auto
      moreover have "t' < t\<^sub>1"
        using \<open>t\<^sub>1 \<in> htps_IH\<close> \<open>\<And>t. t \<in> htps \<Longrightarrow> \<exists>A. (t, A) \<in> set (h # hs2)\<close> \<open>strict_sorted (map fst hs)\<close>
        by(fastforce simp: htps_IH_def)
      hence "t\<^sub>1 \<in> set (map fst hs_IH)"
        using fst_h3'_n_htp \<open>t\<^sub>1 \<in> htps_IH\<close> \<open>hs1 = []\<close> \<open>\<And>t''. t'' \<in> htps_IH \<Longrightarrow> \<exists>A. (t'', A) \<in> set hs_IH\<close>
        by(fastforce simp: image_def hs'_IH_def htps_IH_def)+
      hence "\<And>h3'. h3' \<in> set hs3 \<Longrightarrow> fst h3' < t\<^sub>1"
        using \<open>strict_sorted (map fst hs)\<close>
        by (auto simp: hs_IH_def)
      ultimately have "t''' \<notin> set (map fst hs3)"
        by fastforce
      thus ?thesis
        using \<open>(t''',A''') \<in> set hs\<close> \<open>t''' \<in> {t\<^sub>1<..< t\<^sub>2}\<close> \<open>a \<in> set A'''\<close> \<open>t' < t\<^sub>1\<close> \<open>t\<^sub>1 < t'''\<close>
        by (auto simp: hs_IH_def)
    qed
    moreover have "valid_happ_seq M_IH hs_IH M'"
      using \<open>valid_happ_seq M hs M'\<close> \<open>valid_happ_seq M [h] (apply_happ (t, A') M)\<close>
        \<open>(\<forall>h\<in>set hs3. fst h \<notin> htps)\<close>
      by (auto simp: M_IH_def hs_IH_def intro: 2(9) dest!: valid_happ_seq_append_2)
    moreover have "(fst (hd hs_IH)) \<in> htps_IH"
      using \<open>fst h2 \<in> htps\<close>
      by (auto simp: hs_IH_def htps_IH_def \<open>\<And>h'. h' \<in> set hs_IH \<Longrightarrow> t \<noteq> fst h'\<close> simp del: \<open>t = t'\<close>)
    moreover have "(fst (hd hs'_IH)) \<in> htps_IH"
      using \<open>fst h2 \<in> htps\<close> \<open>fst h2 \<noteq> fst h'\<close>
      by (auto simp: hs'_IH_def htps_IH_def)
    moreover have "(fst (last hs_IH)) \<in> htps_IH"
      using \<open>hs \<noteq> [] \<Longrightarrow> fst (last hs) \<in> htps\<close>
      by (auto simp: hs_IH_def htps_IH_def \<open>\<And>h'. h' \<in> set hs_IH \<Longrightarrow> t \<noteq> fst h'\<close> simp del: \<open>t = t'\<close>)
    moreover have "(fst (last hs'_IH)) \<in> htps_IH"
      using \<open>fst h2 \<in> htps\<close>  \<open>hs' \<noteq> [] \<Longrightarrow> fst (last hs') \<in> htps\<close> \<open>\<And>h'. h' \<in> set hs'_IH \<Longrightarrow> t' \<noteq> fst h'\<close>
      by (auto simp: htps_IH_def hs'_IH_def split: if_splits)+
    ultimately have "valid_happ_seq M_IH hs'_IH M'"
      by (rule 2)
    moreover have "(apply_happ (t, A') M) \<^sup>c\<TTurnstile>\<^sub>= precondition a"
      if "a \<in> set A''" "(t'',A'') \<in> set hs3'"
      for t'' A'' a
    proof-
      have "t'' \<notin> htps"
        using \<open>(t'',A'') \<in> set hs3'\<close> fst_h3'_n_htp
        by auto
      moreover have "t \<in> htps"
        using \<open>t \<in> htps\<close> .
      moreover have "fst h2 \<in> htps"
        using \<open>fst h2 \<in> htps\<close> .
      moreover have "t'' \<in> {t<..<fst h2}"
        using \<open>(t'',A'') \<in> set hs3'\<close> \<open>strict_sorted (map fst hs')\<close>
        by auto
      moreover have "(t'',A'') \<in> set hs'"
        using \<open>(t'',A'') \<in> set hs3'\<close> \<open>strict_sorted (map fst hs')\<close>
        by auto
      ultimately have "\<exists>t'\<in>{t<..<fst h2}. \<exists>A'. (t', A') \<in> set hs \<and> a \<in> set A'"
        using \<open>a \<in> set A''\<close> 
        by(rule 2)      
      then obtain t''' A''' where "t''' \<in> {t<..<fst h2}" "(t''',A''') \<in> set hs" "a \<in> set A'''"
        by (auto simp del: \<open>hs = hs1 @ h # hs2\<close>)
      hence "(t''',A''') \<in> set hs3"
        using \<open>strict_sorted (map fst hs)\<close>
        by auto
      moreover have "valid_happ_seq (apply_happ (t, A') M) (hs3 @ h2 # hs4) M'"
        using \<open>valid_happ_seq M hs M'\<close> \<open>valid_happ_seq M [h] (apply_happ (t, A') M)\<close>
        by auto
      ultimately show ?thesis
        using 2(9) \<open>(\<forall>h\<in>set hs3. fst h \<notin> htps)\<close> \<open>a \<in> set A'''\<close>
        by (force simp: intro!: valid_happ_seq_append_3)
    qed
    moreover have "\<And>t'' A''. (t'',A'') \<in> set hs3' \<Longrightarrow> pairwise acts_non_intrf (set A'')"
      using fst_h3'_n_htp 2(10)
      by (force simp: intro!: empty_eff_non_intrf)
    ultimately show ?thesis
      using \<open>valid_happ_seq M [h'] (apply_happ (t, A') M)\<close> fst_h3'_n_htp
      by (auto simp add: M_IH_def hs'_IH_def intro!: valid_happ_seq_append_1  2(10))
  qed
qed (fastforce simp: empty_filter_conv dest!: filter_eq_consD)+


lemma not_htp_empty_effect:
    assumes "wf_plan \<pi>s"
      and "\<not> is_htp \<pi>s t\<^sub>i"
      and "ind_happ_seq \<pi>s hs"
      and "(t\<^sub>i,A\<^sub>i) \<in> set hs"
      and "a \<in> set A\<^sub>i"
    shows "(effect a) = Effect [] []"
  proof -    
    have *: "(t\<^sub>i,\<pi>) \<notin> set \<pi>s"
            "\<And>t\<^sub>\<pi>. (t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s \<Longrightarrow> t\<^sub>i \<noteq> t\<^sub>\<pi> + (duration \<pi>)"
         for \<pi>
      using \<open>\<not>is_htp \<pi>s t\<^sub>i\<close>
      by (auto simp: is_htp_def)
    obtain t\<^sub>\<pi> \<pi> where "(t\<^sub>\<pi>, \<pi>)\<in>set \<pi>s" "inst_of_plan_action \<pi>s (t\<^sub>\<pi>, \<pi>) (t\<^sub>i, a)"
      using ind_happ_seq_props(7)[OF assms(3-5)]
      by blast
    have "wf_plan_action \<pi>"
      using \<open>wf_plan \<pi>s\<close> \<open>(t\<^sub>\<pi>, \<pi>) \<in> set \<pi>s\<close>
      by (auto simp: wf_plan_def)
    moreover then obtain a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a where
      "wf_action_schema a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a"
      "Some a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a = resolve_action_schema (plan_action.name \<pi>)"
      by (cases \<pi>) (auto split: option.splits dest: resolve_action_wf)
    moreover have "Some a = res_inst_snap_action \<pi> Over_All"
      using * \<open>(t\<^sub>\<pi>, \<pi>)\<in>set \<pi>s\<close> \<open>inst_of_plan_action \<pi>s (t\<^sub>\<pi>, \<pi>) (t\<^sub>i, a)\<close>
      by (cases \<pi>) (fastforce simp: durative_acts_def is_act_simple_def)+
    ultimately show ?thesis 
      by(rule wf_over_all_empty_eff)
  qed

lemma unique_happ:
  assumes "ind_happ_seq \<pi>s hs"
  shows "\<lbrakk>(t, A) \<in> set hs; (t, A') \<in> set hs\<rbrakk> \<Longrightarrow> A = A'"
  using ind_happ_seq_props(1)[OF assms]
  by (induction hs) auto

lemma inst_of_plan_actionE:
  "\<And>t\<^sub>\<pi> \<pi>. \<lbrakk>inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a);
           \<lbrakk>res_inst \<pi> At_Start = Some a; t\<^sub>\<pi> = t\<^sub>a\<rbrakk> \<Longrightarrow> Q;
           \<lbrakk>res_inst_snap_action \<pi> At_Start = Some a; t\<^sub>\<pi> = t\<^sub>a\<rbrakk> \<Longrightarrow> Q;
           \<lbrakk>res_inst_snap_action \<pi> At_End = Some a; t\<^sub>\<pi> + (duration \<pi>) = t\<^sub>a\<rbrakk> \<Longrightarrow> Q;
           \<And>t\<^sub>i t\<^sub>j. \<lbrakk>res_inst_snap_action \<pi> Over_All = Some a; consec_htps \<pi>s t\<^sub>i t\<^sub>j; t\<^sub>\<pi> \<le> t\<^sub>i; t\<^sub>j \<le> t\<^sub>\<pi> + (duration \<pi>); t\<^sub>i < t\<^sub>a; t\<^sub>a < t\<^sub>j\<rbrakk> \<Longrightarrow> Q\<rbrakk>
    \<Longrightarrow> Q"
  by auto
  
lemma ind_happ_seq_happ_at_htps:
    assumes "is_htp \<pi>s t"
      and "ind_happ_seq \<pi>s hs"
      and "ind_happ_seq \<pi>s hs'"
      and "(t,A) \<in> set hs"
      and "(t,A') \<in> set hs'"
      and "a \<in> set A"
    shows "a \<in> set A'"
  proof-
    obtain t\<^sub>\<pi> \<pi> ta where x: "(t\<^sub>\<pi>, \<pi>)\<in>set \<pi>s"
      "(res_inst \<pi> At_Start = Some a \<and> t\<^sub>\<pi> = t)
                       \<or> (res_inst_snap_action \<pi> At_Start = Some a \<and> t\<^sub>\<pi> = t)
                       \<or> (res_inst_snap_action \<pi> At_End = Some a \<and> t\<^sub>\<pi> + (duration \<pi>) = t)"
      using ind_happ_seq_props(7)[OF \<open>ind_happ_seq \<pi>s hs\<close> \<open>(t,A) \<in> set hs\<close> \<open>a \<in> set A\<close>]
        \<open>is_htp \<pi>s t\<close>
      by (auto simp: ast_problem.consec_htps_def)
    note r = ind_happ_seq_props(2-4)[OF \<open>ind_happ_seq \<pi>s hs'\<close>, of _ \<pi>, 
          THEN exE,
          simplified durative_acts_def simple_acts_def is_act_simple_def set_filter comp_def]
    obtain A'' where "(t,A'') \<in> set hs'" "a \<in> set A''"
      apply (insert x)
      apply (elim disjE conjE)
      by (force intro: r split: plan_action.splits)+
      
    moreover hence "A'' = A'"
      using  \<open>ind_happ_seq \<pi>s hs'\<close> \<open>(t, A') \<in> set hs'\<close>
      by(auto intro: unique_happ)
    ultimately show ?thesis
      by auto
  qed

  lemma ind_happ_seq_happ_at_htps':
    assumes "is_htp \<pi>s t"
      and "ind_happ_seq \<pi>s hs"
      and "ind_happ_seq \<pi>s hs'"
      and "(t,A) \<in> set hs"
      and "(t,A') \<in> set hs'"
    shows "set A = set A'"
    using assms ind_happ_seq_happ_at_htps
    by blast

lemma htp_in_ind_happ_seq:
  "\<lbrakk>is_htp \<pi>s t; ind_happ_seq \<pi>s hs\<rbrakk> \<Longrightarrow> \<exists>A. (t,A) \<in> set hs"
  by(fastforce simp: is_htp_def ind_happ_seq_def durative_acts_def simple_acts_def split: prod.splits)

lemma sorted_takeWhile: "strict_sorted xs \<Longrightarrow> x \<in> set (takeWhile ((\<lambda>x. x < c)) xs) = (x \<in> set xs \<and> (x < c))"
  by (induction xs arbitrary: c x) auto
  
lemma sorted_dropWhile: "strict_sorted xs \<Longrightarrow> x \<in> set (dropWhile ((\<lambda>x. x \<le> c)) xs) = (x \<in> set xs \<and> (c < x))"
  by (induction xs arbitrary: c x) auto

lemma map_fst_dropWhile: "map fst (dropWhile (leq t) hs) = (dropWhile ((\<lambda>x. x \<le> t)) (map fst hs))"
  by (induction hs) (auto simp: leq_def)

lemma map_fst_takeWhile: "map fst (takeWhile (le t) hs) = (takeWhile ((\<lambda>x. x < t)) (map fst hs))"
  by (induction hs) (auto simp: le_def)

lemma strict_sorted_fst_unique_snd:
  "\<lbrakk>strict_sorted (map fst hs); (t, A) \<in> set hs; (t, A') \<in> set hs\<rbrakk> \<Longrightarrow> A = A'"
  by (induction hs) auto

lemma strict_sorted_dropWhile:
  "strict_sorted xs \<Longrightarrow> strict_sorted (dropWhile Q xs)"
  by (induction xs) auto

lemma strict_sorted_takeWhile:
  "strict_sorted xs \<Longrightarrow> strict_sorted (takeWhile Q xs)"
  by (induction xs) (auto dest!: set_takeWhileD)

lemma strict_sorted_drop_leq_take_le':
    assumes "strict_sorted (map fst hs)"
    shows "(t\<^sub>a,A) \<in> set (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)) \<longleftrightarrow> 
              (t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j \<and> (t\<^sub>a,A) \<in> set hs)" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  hence "t\<^sub>a \<in> set (map fst (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)))"
    by auto
  hence "(t\<^sub>i < t\<^sub>a)" "t\<^sub>a < t\<^sub>j"
    using strict_sorted_takeWhile[OF \<open>strict_sorted (map fst hs)\<close>] \<open>strict_sorted (map fst hs)\<close>
    by(auto simp: sorted_takeWhile sorted_dropWhile map_fst_takeWhile map_fst_dropWhile)+
  thus ?r
    using \<open>?l\<close>
    by (auto dest: set_dropWhileD set_takeWhileD)
next 
  assume ?r
  hence "t\<^sub>a \<in> set (map fst hs)"
    by auto
  hence "t\<^sub>a \<in> set (map fst ((dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs))))"
    using strict_sorted_takeWhile[OF \<open>strict_sorted (map fst hs)\<close>] \<open>strict_sorted (map fst hs)\<close> \<open>?r\<close>
    by(auto simp: sorted_takeWhile sorted_dropWhile map_fst_takeWhile map_fst_dropWhile)
  then obtain A' where "(t\<^sub>a, A') \<in> set ((dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)))" "(t\<^sub>a, A') \<in> set hs"
    by (fastforce dest: set_dropWhileD set_takeWhileD)
  thus ?l
    using \<open>?r\<close> strict_sorted_fst_unique_snd \<open>strict_sorted (map fst hs)\<close>
    by force
qed

lemma ind_happ_seqs_same_acts_leq\<^sub>i_le\<^sub>j':
  assumes "is_htp \<pi>s t\<^sub>i"
        and "is_htp \<pi>s t\<^sub>j"
        and "ind_happ_seq \<pi>s hs\<^sub>1" 
        and "ind_happ_seq \<pi>s hs\<^sub>2"
        and "(t\<^sub>a,A) \<in> set (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs\<^sub>1))"
        and "a \<in> set A"
      shows "\<exists>t\<^sub>a' A'. (t\<^sub>a',A') \<in> set (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs\<^sub>2)) \<and> a \<in> set A'"
  proof -
    let ?hs\<^sub>1'="dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs\<^sub>1)"
    let ?hs\<^sub>2'="dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs\<^sub>2)"
    have "(t\<^sub>a,A) \<in> set hs\<^sub>1"
      using \<open>(t\<^sub>a,A) \<in> set ?hs\<^sub>1'\<close> by (meson set_dropWhileD set_takeWhileD) 
    have "strict_sorted (map fst hs\<^sub>1)" and "strict_sorted (map fst hs\<^sub>2)"
      using \<open>ind_happ_seq \<pi>s hs\<^sub>1\<close> \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close> unfolding ind_happ_seq_def by auto
    moreover have "t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j"
      using \<open>(t\<^sub>a,A) \<in> set ?hs\<^sub>1'\<close> \<open>strict_sorted (map fst hs\<^sub>1)\<close> \<open>(t\<^sub>a,A) \<in> set hs\<^sub>1\<close>
      by (fastforce simp: strict_sorted_drop_leq_take_le')
    moreover obtain t\<^sub>\<pi> \<pi> where "(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s" and "inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a)"
      using \<open>ind_happ_seq \<pi>s hs\<^sub>1\<close> \<open>(t\<^sub>a,A) \<in> set hs\<^sub>1\<close> \<open>a \<in> set A\<close>
      by (fastforce simp: ind_happ_seq_def)                              
    ultimately show ?thesis
    proof (elim inst_of_plan_actionE, goal_cases)
      case (4 t\<^sub>i' t\<^sub>j')
      let ?a\<^sub>i\<^sub>n\<^sub>v="the (res_inst_snap_action \<pi> Over_All)"
      have "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s"
        unfolding durative_acts_def is_act_simple_def
        using 4 \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> by (cases \<pi>) auto
      then have "\<exists>(t',as) \<in> set hs\<^sub>2. t\<^sub>i' < t' \<and> t' < t\<^sub>j' \<and> ?a\<^sub>i\<^sub>n\<^sub>v \<in> set as"
        using \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close> 
        using \<open>consec_htps \<pi>s t\<^sub>i' t\<^sub>j'\<close> 4 by (auto simp: ind_happ_seq_def)
      then obtain t\<^sub>a' A' where "(t\<^sub>a',A') \<in> set hs\<^sub>2" and "t\<^sub>i' < t\<^sub>a' \<and> t\<^sub>a' < t\<^sub>j'" and "?a\<^sub>i\<^sub>n\<^sub>v \<in> set A'"
        by auto
      then have "(t\<^sub>a',A') \<in> set hs\<^sub>2"
        using 4 by auto
      moreover have "t\<^sub>i < t\<^sub>a' \<and> t\<^sub>a' < t\<^sub>j"
        using assms \<open>consec_htps \<pi>s t\<^sub>i' t\<^sub>j'\<close> \<open>t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j\<close> \<open>t\<^sub>i' < t\<^sub>a\<close> \<open>t\<^sub>a < t\<^sub>j'\<close> 
              \<open>t\<^sub>i' < t\<^sub>a' \<and> t\<^sub>a' < t\<^sub>j'\<close>
        by (auto simp: consec_htps_def)
      ultimately show ?thesis
        using 4 \<open>?a\<^sub>i\<^sub>n\<^sub>v \<in> set A'\<close> \<open>strict_sorted (map fst hs\<^sub>2)\<close>
        by(fastforce simp: strict_sorted_drop_leq_take_le')
    qed (insert \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close>, cases \<pi>;
         fastforce simp: strict_sorted_drop_leq_take_le' ind_happ_seq_def simple_acts_def
                         durative_acts_def is_act_simple_def)+
  qed

lemma happs_same_between_htps:
  assumes "ind_happ_seq \<pi>s hs"
      and "ind_happ_seq \<pi>s hs'"
      and "is_htp \<pi>s t\<^sub>1" "is_htp \<pi>s t\<^sub>2"
      and "(t, A) \<in> set hs"
      and "\<not>is_htp \<pi>s t"
      and "t\<^sub>1 < t"
      and "t < t\<^sub>2"
      and "a \<in> set A"
  shows "\<exists>t'\<in>{t\<^sub>1<..<t\<^sub>2}. \<exists>A'. (t',A')\<in>set hs'\<and> a \<in> set A'"
proof-
  have "\<exists>t\<^sub>a' A'. (t\<^sub>a',A') \<in> set (dropWhile (leq t\<^sub>1) (takeWhile (le t\<^sub>2) hs')) \<and> a \<in> set A'"
    using ind_happ_seq_props(1)[OF \<open>ind_happ_seq \<pi>s hs\<close>] assms
    by (fastforce simp: strict_sorted_drop_leq_take_le' ind_happ_seqs_same_acts_leq\<^sub>i_le\<^sub>j')
  thus ?thesis
    using \<open>(t, A) \<in> set hs\<close> ind_happ_seq_props(1)[OF \<open>ind_happ_seq \<pi>s hs'\<close>]
    by (auto simp: strict_sorted_drop_leq_take_le')
qed

lemma consec_htps_props:
  assumes "consec_htps \<pi>s t\<^sub>i t\<^sub>j"
  shows "t\<^sub>i < t\<^sub>j"
        "is_htp \<pi>s t\<^sub>i"
        "is_htp \<pi>s t\<^sub>j"
        "is_htp \<pi>s t \<Longrightarrow> t \<le> t\<^sub>i \<or> t\<^sub>j \<le> t"
  using assms
  by (auto simp: consec_htps_def)

lemma ind_happ_seq_hd_htp:
  assumes "ind_happ_seq \<pi>s hs" "hs \<noteq> []"
  shows "is_htp \<pi>s (fst (hd hs))"
proof-
  obtain h hs' where hs[simp]: "hs = h#hs'"
    using \<open>hs \<noteq> []\<close>
    by (auto simp: neq_Nil_conv)
  then obtain t A where h[simp]: "h = (t, A)"
    by (elim prod.exhaust)
  then obtain a where "a \<in> set A"
    using ind_happ_seq_props(6)[OF \<open>ind_happ_seq \<pi>s hs\<close>]
    by auto
  then obtain t\<^sub>\<pi> \<pi> where "(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s" and "inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t,a)"
    using \<open>ind_happ_seq \<pi>s hs\<close> \<open>a \<in> set A\<close>
    by (fastforce simp: ind_happ_seq_def)
  then show ?thesis
    using ind_happ_seq_props(1)[OF \<open>ind_happ_seq \<pi>s hs\<close>]
    by(force simp: durative_acts_def is_act_simple_def is_htp_def
             dest!: consec_htps_props(2) htp_in_ind_happ_seq[OF _ \<open>ind_happ_seq \<pi>s hs\<close>]
             elim!: res_inst_snap_action.elims)
qed

lemma sorted_last: "\<lbrakk>strict_sorted xs; x \<in> set xs\<rbrakk> \<Longrightarrow> x \<le> last xs"
  by (induction xs) (auto simp: dest!: last_in_set)

lemma ind_happ_seq_last_htp:
  assumes "ind_happ_seq \<pi>s hs" "hs \<noteq> []"
  shows "is_htp \<pi>s (fst (last hs))"
proof-
  obtain h hs' where hs[simp]: "hs = hs' @ [h]"
    using \<open>hs \<noteq> []\<close>
    by (auto simp: neq_Nil_rev_conv)
  then obtain t A where h[simp]: "h = (t, A)"
    by (elim prod.exhaust)
  then obtain a where "a \<in> set A"
    using ind_happ_seq_props(6)[OF \<open>ind_happ_seq \<pi>s hs\<close>]
    by auto
  then obtain t\<^sub>\<pi> \<pi> where "(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s" and "inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t,a)"
    using \<open>ind_happ_seq \<pi>s hs\<close> \<open>a \<in> set A\<close>
    by (fastforce simp: ind_happ_seq_def)
  then show ?thesis
    using ind_happ_seq_props(1)[OF \<open>ind_happ_seq \<pi>s hs\<close>] sorted_last
    by (fastforce simp: durative_acts_def is_act_simple_def is_htp_def
        dest!: consec_htps_props(3) htp_in_ind_happ_seq[OF _ \<open>ind_happ_seq \<pi>s hs\<close>]
        elim!: res_inst_snap_action.elims)
qed

definition "htps' \<pi>s \<equiv> {t . is_htp \<pi>s t}"

lemma htps_props: "t \<in> htps' \<pi>s \<Longrightarrow> is_htp \<pi>s t"
  by(auto simp: htps'_def)

lemma ind_happ_seq_unique_final_state':
  assumes"ind_happ_seq \<pi>s hs" and "ind_happ_seq \<pi>s hs'"
  shows "\<lbrakk>wf_plan \<pi>s; valid_happ_seq M\<^sub>0 hs M\<^sub>n\<rbrakk> \<Longrightarrow> valid_happ_seq M\<^sub>0 hs' M\<^sub>n"
  using not_htp_empty_effect assms
  by (auto intro!: ind_happ_seq_last_htp htp_in_ind_happ_seq ind_happ_seq_hd_htp ind_happ_seq_props(1)
                   valid_hap_seq_construct[where htps = "htps' \<pi>s" and hs = "hs"]
           intro: happs_same_between_htps
           simp: htps'_def ind_happ_seq_happ_at_htps'[OF htps_props \<open>ind_happ_seq \<pi>s hs\<close> \<open>ind_happ_seq \<pi>s hs'\<close>])

end

end \<comment> \<open>Theory\<close>
