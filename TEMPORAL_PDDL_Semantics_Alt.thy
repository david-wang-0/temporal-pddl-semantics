section \<open>Connecting the Semantics to State-Transition Based Semantics\<close>
theory TEMPORAL_PDDL_Semantics_Alt
imports
  TEMPORAL_PDDL_Semantics
  TEMPORAL_PDDL_Checker (* only need for lemma @{const ind_happ_seq_exists} *)
begin

  text \<open>Auxiliary lemma with about @{const dropWhile}, @{const takeWhile} 
  with @{const le} and @{const leq}\<close>

  lemma strict_sorted_drop_le_take_leq_comm:
    assumes "t\<^sub>i \<le> t\<^sub>j" 
        and "strict_sorted (map fst hs)"
    shows "dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>j) hs) = takeWhile (leq t\<^sub>j) (dropWhile (le t\<^sub>i) hs)"
    using assms 
    by (induction hs) (auto simp: le_def leq_def)

  lemma strict_sorted_drop_leq_take_le_comm:
    assumes "t\<^sub>i < t\<^sub>j" 
        and "strict_sorted (map fst hs)"
    shows "dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs) = takeWhile (le t\<^sub>j) (dropWhile (leq t\<^sub>i) hs)"
    using assms 
    by (induction hs) (auto simp: le_def leq_def)

  lemma strict_sorted_drop_leq_take_leq_comm:
    assumes "t\<^sub>i \<le> t\<^sub>j" 
        and "strict_sorted (map fst hs)"
    shows "dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs) = takeWhile (leq t\<^sub>j) (dropWhile (leq t\<^sub>i) hs)"
    using assms by (induction hs) (auto simp: leq_def)

  lemma strict_sorted_drop_le_take_leq:
    assumes "strict_sorted (map fst hs)"
        and "(t\<^sub>a,A) \<in> set hs"
    shows "(t\<^sub>a,A) \<in> set (dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>j) hs)) \<longleftrightarrow> t\<^sub>i \<le> t\<^sub>a \<and> t\<^sub>a \<le> t\<^sub>j"
    unfolding leq_def le_def
    using assms
    apply (induction hs)
    apply (auto simp: leq_def le_def)
    apply (meson set_dropWhileD set_takeWhileD)
    apply auto[1]
    using set_takeWhileD apply fastforce
    apply (meson set_dropWhileD)+
    done (* TODO: proof *)
  
  lemma strict_sorted_drop_leq_take_leq:
    assumes "strict_sorted (map fst hs)"
        and "(t\<^sub>a,A) \<in> set hs"
    shows "(t\<^sub>a,A) \<in> set (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs)) \<longleftrightarrow> t\<^sub>i < t\<^sub>a \<and> t\<^sub>a \<le> t\<^sub>j"
    unfolding leq_def
    using assms
    apply (induction hs)
    apply auto
    apply (meson set_dropWhileD set_takeWhileD)
    apply auto[1]
    using set_takeWhileD apply fastforce
    apply (meson set_dropWhileD)+
    done (* TODO: proof *)

  lemma strict_sorted_drop_leq_take_le:
    assumes "strict_sorted (map fst hs)"
        and "(t\<^sub>a,A) \<in> set hs"
    shows "(t\<^sub>a,A) \<in> set (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)) \<longleftrightarrow> t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j"
    unfolding leq_def le_def
    using assms
    apply (induction hs)
    apply auto
    apply (meson set_dropWhileD set_takeWhileD)
    apply auto[1]
    using set_takeWhileD apply fastforce
    apply (meson set_dropWhileD)+
    done (* TODO: proof *)


  lemma split_list2_le:
    assumes "strict_sorted xs"
        and "x\<^sub>1 \<in> set xs"
        and "x\<^sub>2 \<in> set xs"
    shows "x\<^sub>1 < x\<^sub>2 \<longleftrightarrow> (\<exists>xs\<^sub>1 xs\<^sub>2 xs\<^sub>3. xs = xs\<^sub>1 @ x\<^sub>1 # xs\<^sub>2 @ x\<^sub>2 # xs\<^sub>3)"
  proof
    assume "x\<^sub>1 < x\<^sub>2"
    obtain xs\<^sub>2' xs\<^sub>3 where "xs = xs\<^sub>2' @ x\<^sub>2 # xs\<^sub>3"
      using \<open>x\<^sub>2 \<in> set xs\<close>
      by (meson split_list)
    then have "\<forall>x \<in> set xs\<^sub>3. x\<^sub>2 < x"
      using \<open>strict_sorted xs\<close> sorted_wrt_append[where xs="xs\<^sub>2'" and ys="x\<^sub>2 # xs\<^sub>3"]
      by (simp add: \<open>xs = xs\<^sub>2' @ x\<^sub>2 # xs\<^sub>3\<close>)
    then have "x\<^sub>1 \<in> set xs\<^sub>2'"
      using \<open>x\<^sub>1 < x\<^sub>2\<close> \<open>x\<^sub>1 \<in> set xs\<close> \<open>xs = xs\<^sub>2' @ x\<^sub>2 # xs\<^sub>3\<close> by auto
    then obtain xs\<^sub>1 xs\<^sub>2 where "xs\<^sub>2' = xs\<^sub>1 @ x\<^sub>1 # xs\<^sub>2"
      by (meson split_list)
    then show "\<exists>xs\<^sub>1 xs\<^sub>2 xs\<^sub>3. xs = xs\<^sub>1 @ x\<^sub>1 # xs\<^sub>2 @ x\<^sub>2 # xs\<^sub>3"
      using \<open>xs = xs\<^sub>2' @ x\<^sub>2 # xs\<^sub>3\<close> \<open>xs\<^sub>2' = xs\<^sub>1 @ x\<^sub>1 # xs\<^sub>2\<close> by auto
  next
    assume "\<exists>xs\<^sub>1 xs\<^sub>2 xs\<^sub>3. xs = xs\<^sub>1 @ x\<^sub>1 # xs\<^sub>2 @ x\<^sub>2 # xs\<^sub>3"
    then obtain xs\<^sub>1 xs\<^sub>2 xs\<^sub>3 where "xs = xs\<^sub>1 @ x\<^sub>1 # xs\<^sub>2 @ x\<^sub>2 # xs\<^sub>3"
      by auto
    then show "x\<^sub>1 < x\<^sub>2"
      using \<open>strict_sorted xs\<close>
            sorted_wrt_append[where xs="xs\<^sub>1 @ x\<^sub>1 # xs\<^sub>2" and ys="x\<^sub>2 # xs\<^sub>3"]
      by (simp add: \<open>xs = xs\<^sub>1 @ x\<^sub>1 # xs\<^sub>2 @ x\<^sub>2 # xs\<^sub>3\<close>)
  qed

  lemma drop_take_leq\<^sub>i_leq_leq\<^sub>j_aux:
    assumes "t\<^sub>k \<le> t\<^sub>j"
        and "strict_sorted (map fst hs)"
    shows "takeWhile (leq t\<^sub>k) hs @ takeWhile (leq t\<^sub>j) (dropWhile (leq t\<^sub>k) hs) = takeWhile (leq t\<^sub>j) hs"
    using assms by (induction hs) (auto simp: leq_def)

  lemma drop_take_leq\<^sub>i_leq_leq\<^sub>j_simp:
    assumes "t\<^sub>i \<le> t\<^sub>k" and "t\<^sub>k \<le> t\<^sub>j"
        and "strict_sorted (map fst hs)"
      shows "dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>k) hs) @ dropWhile (leq t\<^sub>k) (takeWhile (leq t\<^sub>j) hs) 
              = dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs)"
    using \<open>t\<^sub>i \<le> t\<^sub>k\<close> drop_take_leq\<^sub>i_leq_leq\<^sub>j_aux[OF \<open>t\<^sub>k \<le> t\<^sub>j\<close> \<open>strict_sorted (map fst hs)\<close>]
          strict_sorted_drop_leq_take_leq_comm[OF \<open>t\<^sub>k \<le> t\<^sub>j\<close> \<open>strict_sorted (map fst hs)\<close>]
    by (induction hs) (auto simp: leq_def)

subsection \<open>State-Transition Based Semantics\<close>

context ast_problem begin

  fun inst_cond :: "ast_action_schema \<Rightarrow> object list \<Rightarrow> temporal_annotation \<Rightarrow> (object atom) formula" where
    "inst_cond (Durative_Action_Schema n params d cond eff) args ts = 
      (let tsubst = subst_term (the o (map_of (zip (map fst params) args))) in 
          (map_formula o map_atom) tsubst (BigAnd (filter_time_spec ts cond)))"

  fun res_inst_inv :: "plan_action \<Rightarrow> (object atom) formula option" where 
    "res_inst_inv (Simple_Plan_Action n args) = None"
  | "res_inst_inv (Durative_Plan_Action n args d) = 
      Some (inst_cond (the (resolve_action_schema n)) args Over_All)"

  lemma res_inst_inv_refine:
    assumes "wf_plan_action \<pi>"
        and "Some a = res_inst_snap_action \<pi> Over_All"
    shows "Some (precondition a) = res_inst_inv \<pi>"
    using assms
    by (cases \<pi>) (auto simp: Let_def split: option.splits ast_action_schema.splits)

  text\<open>Set of all ground actions that, are executed at a given time point in the 
  induced happening sequence.\<close>
  definition acts_of_plan_at :: "time \<Rightarrow> plan \<Rightarrow> ground_action set" where
    "acts_of_plan_at t\<^sub>i \<pi>s = 
      {a\<^sub>\<pi>. \<exists>\<pi>. (t\<^sub>i,\<pi>) \<in> simple_acts \<pi>s \<and> Some a\<^sub>\<pi> = res_inst \<pi>} 
    \<union> {a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t. \<exists>\<pi>. (t\<^sub>i,\<pi>) \<in> durative_acts \<pi>s \<and> Some a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t = res_inst_snap_action \<pi> At_Start} 
    \<union> {a\<^sub>e\<^sub>n\<^sub>d. \<exists>t' \<pi>. (t',\<pi>) \<in> durative_acts \<pi>s \<and> t\<^sub>i = t' + duration \<pi> \<and> Some a\<^sub>e\<^sub>n\<^sub>d = res_inst_snap_action \<pi> At_End}" 
  (* TODO: maybe convert to multiset *)

  text\<open>Set of all invariant that have to hold in between consecutive happening time points \<open>t' < t\<close>.\<close> 
  definition invs_of_plan_at :: "time \<Rightarrow> plan \<Rightarrow> (object atom) formula set" where
    "invs_of_plan_at t\<^sub>i \<pi>s = 
      {inv. \<exists>t\<^sub>\<pi> \<pi>. (t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s \<and> t\<^sub>\<pi> < t\<^sub>i \<and> t\<^sub>i \<le> t\<^sub>\<pi> + (duration \<pi>) \<and> Some inv = res_inst_inv \<pi>}"
  (* TODO: maybe convert to multiset *)

  text\<open>Predicate for sequence of happening time points.\<close>
  (*definition htps_seq :: "plan \<Rightarrow> time list \<Rightarrow> bool" where
    "htps_seq \<pi>s htps \<longleftrightarrow> strict_sorted htps \<and> (\<forall>t. t \<in> set htps \<longleftrightarrow> is_htp \<pi>s t)"*)
  
  fun apply_eff :: "ground_action set \<Rightarrow> world_model \<Rightarrow> world_model" where
    "apply_eff A\<^sub>i M = (M - \<Union> (set ` dels ` effect ` A\<^sub>i)) \<union> \<Union> (set ` adds ` effect ` A\<^sub>i)"

  text\<open>Instead of explicitly defining an induced happening sequence. Here the 
  happening sequence is only implicitly constructed. Only happening time points are considered 
  for the valid execution, invariants are treated like preconditions of an entire happening.\<close> 
  fun valid_state_seq :: "world_model \<Rightarrow> time list \<Rightarrow> plan \<Rightarrow> world_model \<Rightarrow> bool" where
    "valid_state_seq M [] \<pi>s M' \<longleftrightarrow> (M = M')"
  | "valid_state_seq M (t\<^sub>i#ts) \<pi>s M' \<longleftrightarrow> 
    (let A\<^sub>i = acts_of_plan_at t\<^sub>i \<pi>s in
        (\<forall>i \<in> invs_of_plan_at t\<^sub>i \<pi>s. M \<^sup>c\<TTurnstile>\<^sub>= i)
      \<and> (\<forall>a \<in> A\<^sub>i. M \<^sup>c\<TTurnstile>\<^sub>= precondition a)
      \<and> (\<forall>a \<in> A\<^sub>i. \<forall>b \<in> A\<^sub>i. a \<noteq> b \<longrightarrow> acts_non_intrf a b)
      \<and> valid_state_seq (apply_eff A\<^sub>i M) ts \<pi>s M')"

  definition valid_plan_from :: "world_model \<Rightarrow> plan \<Rightarrow> bool" where
    "valid_plan_from M \<pi>s \<longleftrightarrow> (wf_plan \<pi>s \<and> (\<exists>htps M'. htps_seq \<pi>s htps \<and> valid_state_seq M htps \<pi>s M' \<and> M' \<^sup>c\<TTurnstile>\<^sub>= (goal P)))"

  definition valid_plan :: "plan \<Rightarrow> bool"
    where "valid_plan \<equiv> valid_plan_from I"

  text \<open>Concise definition used in paper:\<close> 
  lemma "valid_plan \<pi>s \<equiv> wf_plan \<pi>s \<and> (\<exists>htps M'. htps_seq \<pi>s htps \<and> valid_state_seq I htps \<pi>s M' \<and> M' \<^sup>c\<TTurnstile>\<^sub>= (goal P))"
    unfolding valid_plan_def valid_plan_from_def by auto

  subsection \<open>Connecting the State-Transition Based Semantics to Happening Sequence Based Semantics\<close>

  text\<open>Justification for Semantic refinement\<close>

  lemma "apply_happ (t,A) M = apply_eff (set A) M"
    by auto
    
  lemma valid_state_seq_app_iff:
    "valid_state_seq M\<^sub>i (ts\<^sub>1@ts\<^sub>2) \<pi>s M\<^sub>k 
      \<longleftrightarrow> (\<exists>M\<^sub>j. valid_state_seq M\<^sub>i ts\<^sub>1 \<pi>s M\<^sub>j \<and> valid_state_seq M\<^sub>j ts\<^sub>2 \<pi>s M\<^sub>k)"
    by (induction ts\<^sub>1 arbitrary: ts\<^sub>2 M\<^sub>i M\<^sub>k) (auto simp: Let_def)

  lemma valid_state_seq_state_unique:
    assumes "valid_state_seq M\<^sub>0 ts \<pi>s M\<^sub>i" and "valid_state_seq M\<^sub>0 ts \<pi>s M\<^sub>i'"
    shows "M\<^sub>i = M\<^sub>i'"
    using assms by (induction M\<^sub>0 ts \<pi>s M\<^sub>i rule: valid_state_seq.induct) (auto simp: Let_def)

  text\<open>@{const acts_of_plan_at} returns exactly the set of actions that would be executed 
  for a happening time point in the induced happening sequence\<close>
  lemma ind_happ_seq_htp_acts_of_plan_at:
    assumes "ind_happ_seq \<pi>s hs"
        and "is_htp \<pi>s t"
        and "(t,A) \<in> set hs"
    shows "set A = acts_of_plan_at t \<pi>s"
  proof
    show "set A \<subseteq> acts_of_plan_at t \<pi>s"
    proof
      fix a
      assume "a \<in> set A"
      then have "\<exists>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s. inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t,a)"
        using assms by (auto simp: ind_happ_seq_def)
      then obtain t\<^sub>\<pi> \<pi> where "(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s" and "inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t,a)"
        by auto
      let ?case1="res_inst \<pi> = Some a \<and> t\<^sub>\<pi> = t"
      let ?case2="res_inst_snap_action \<pi> At_Start = Some a \<and> t\<^sub>\<pi> = t"
      let ?case3="res_inst_snap_action \<pi> At_End = Some a \<and> t\<^sub>\<pi> + duration \<pi> = t"
      let ?case4="res_inst_snap_action \<pi> Over_All = Some a \<and> 
            (\<exists>t\<^sub>i t\<^sub>j. consec_htps \<pi>s t\<^sub>i t\<^sub>j \<and> t\<^sub>\<pi> \<le> t\<^sub>i \<and> t\<^sub>j \<le> t\<^sub>\<pi> + (duration \<pi>) \<and> t\<^sub>i < t \<and> t < t\<^sub>j)"
      have "?case1 \<or> ?case2 \<or> ?case3 \<or> ?case4"
        using \<open>inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t,a)\<close> by simp
      then show "a \<in> acts_of_plan_at t \<pi>s"
        proof (elim disjE)
          assume ?case1
          then show ?thesis
            unfolding acts_of_plan_at_def simple_acts_def is_act_simple_def
            using \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> by (cases \<pi>) auto
        next
          assume ?case2
          then show ?thesis
            unfolding acts_of_plan_at_def durative_acts_def is_act_simple_def
            using \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> by (cases \<pi>) auto
        next
          assume ?case3
          then show ?thesis
            unfolding acts_of_plan_at_def durative_acts_def is_act_simple_def
            using \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> by (cases \<pi>) fastforce+
        next
          assume ?case4
          then show ?thesis
            using assms by (auto simp: consec_htps_def)
        qed
      qed
  next
    show "set A \<supseteq> acts_of_plan_at t \<pi>s"
    proof
      fix a
      let ?case1="a \<in> {a\<^sub>\<pi>. \<exists>\<pi>. (t,\<pi>) \<in> simple_acts \<pi>s \<and> Some a\<^sub>\<pi> = res_inst \<pi>}"
      let ?case2="a \<in> {a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t. \<exists>\<pi>. (t,\<pi>) \<in> durative_acts \<pi>s \<and> Some a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t = res_inst_snap_action \<pi> At_Start}"
      let ?case3="a \<in> {a\<^sub>e\<^sub>n\<^sub>d. \<exists>t' \<pi>. (t',\<pi>) \<in> durative_acts \<pi>s \<and> t = t' + duration \<pi> \<and> Some a\<^sub>e\<^sub>n\<^sub>d = res_inst_snap_action \<pi> At_End}"
      assume "a \<in> acts_of_plan_at t \<pi>s"
      then have "?case1 \<or> ?case2 \<or> ?case3"
        unfolding acts_of_plan_at_def by simp
      then show "a \<in> set A"
        proof (elim disjE)
          assume ?case1
          then obtain \<pi> where "(t,\<pi>) \<in> simple_acts \<pi>s" and "the (res_inst \<pi>) = a"
            by auto (metis option.sel)
          then have "\<exists>as. (t, as) \<in> set hs \<and> a \<in> set as"
            using assms unfolding ind_happ_seq_def by auto
          then obtain A' where "(t, A') \<in> set hs" and "a \<in> set A'"
            by auto
          have "A = A'"
            using assms \<open>(t, A') \<in> set hs\<close> unfolding ind_happ_seq_def
            by (auto simp: strict_sorted_iff distinct_map_fstD)
          then show ?thesis
            using \<open>a \<in> set A'\<close> by auto
        next
          assume ?case2
          then obtain \<pi> where "(t,\<pi>) \<in> durative_acts \<pi>s" 
                          and "the (res_inst_snap_action \<pi> At_Start) = a"
            by auto (metis option.sel)
          then have "\<exists>as. (t, as) \<in> set hs \<and> a \<in> set as"
            using assms unfolding ind_happ_seq_def by auto
          then obtain A' where "(t, A') \<in> set hs" and "a \<in> set A'"
            by auto
          have "A = A'"
            using assms \<open>(t, A') \<in> set hs\<close> unfolding ind_happ_seq_def
            by (auto simp: strict_sorted_iff distinct_map_fstD)
          then show ?thesis
            using \<open>a \<in> set A'\<close> by auto
        next
          assume ?case3
          then obtain t' \<pi> where "(t',\<pi>) \<in> durative_acts \<pi>s" and "t = t' + duration \<pi>" 
                             and "the (res_inst_snap_action \<pi> At_End) = a"
            by auto (metis option.sel)
          then have "\<exists>as. (t, as) \<in> set hs \<and> a \<in> set as"
            using assms unfolding ind_happ_seq_def by auto
          then obtain A' where "(t, A') \<in> set hs" and "a \<in> set A'"
            by auto
          have "A = A'"
            using assms \<open>(t, A') \<in> set hs\<close> unfolding ind_happ_seq_def
            by (auto simp: strict_sorted_iff distinct_map_fstD)
          then show ?thesis
            using \<open>a \<in> set A'\<close> by auto
      qed
    qed
  qed
end

context wf_ast_problem
begin

  text\<open>The precondition of every invariant ground action in between two consecutive 
  happening time points is included in @{const invs_of_plan_at}.\<close>
  lemma ind_happ_seq_invs_of_plan_at:
    assumes "wf_plan \<pi>s"
        and "consec_htps \<pi>s t\<^sub>i t\<^sub>j"
        and "ind_happ_seq \<pi>s hs"
        and "(t,A) \<in> set (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs))"
        and "a \<in> set A"
    shows "(precondition a) \<in> invs_of_plan_at t\<^sub>j \<pi>s"
  proof -
    let ?hs'="dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)"
    have "strict_sorted (map fst hs)"
      using \<open>ind_happ_seq \<pi>s hs\<close> unfolding ind_happ_seq_def by auto
    have "(t,A) \<in> set hs"
      using assms by (meson set_dropWhileD set_takeWhileD)
    then have "\<exists>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s. inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t,a)"
      using assms by (auto simp: ind_happ_seq_def)
    then obtain t\<^sub>\<pi> \<pi> where "(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s" and "inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t,a)"
      by auto
    then have "is_htp \<pi>s t\<^sub>\<pi>"
      unfolding is_htp_def by auto
    have "\<not>is_htp \<pi>s t"

      thm sorted_take[OF sorted_drop]
      thm wf_ast_problem.strict_sorted_drop_leq_take_le'

      using assms strict_sorted_drop_leq_take_le'[OF \<open>strict_sorted (map fst hs)\<close>] 
      unfolding consec_htps_def by auto
    let ?case1="res_inst \<pi> = Some a \<and> t\<^sub>\<pi> = t"
    let ?case2="res_inst_snap_action \<pi> At_Start = Some a \<and> t\<^sub>\<pi> = t"
    let ?case3="res_inst_snap_action \<pi> At_End = Some a \<and> t\<^sub>\<pi> + duration \<pi> = t"
    let ?case4="res_inst_snap_action \<pi> Over_All = Some a \<and> 
            (\<exists>t\<^sub>i t\<^sub>j. consec_htps \<pi>s t\<^sub>i t\<^sub>j \<and> t\<^sub>\<pi> \<le> t\<^sub>i \<and> t\<^sub>j \<le> t\<^sub>\<pi> + (duration \<pi>) \<and> t\<^sub>i < t \<and> t < t\<^sub>j)"
    have "?case1 \<or> ?case2 \<or> ?case3 \<or> ?case4"
      using \<open>inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t,a)\<close> by simp
    then show ?thesis
      proof (elim disjE)
        assume ?case1
        then show ?thesis
          using assms \<open>\<not>is_htp \<pi>s t\<close> \<open>is_htp \<pi>s t\<^sub>\<pi>\<close> by auto
      next
        assume ?case2
        then show ?thesis
          using assms \<open>\<not>is_htp \<pi>s t\<close> \<open>is_htp \<pi>s t\<^sub>\<pi>\<close> by auto
      next
        assume ?case3
        then have "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s"
          unfolding durative_acts_def is_act_simple_def
          using \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> by (cases \<pi>) auto
        then have "is_htp \<pi>s (t\<^sub>\<pi> + duration \<pi>)"
          unfolding is_htp_def by auto
        then show ?thesis
          using \<open>?case3\<close> \<open>\<not>is_htp \<pi>s t\<close> by auto
      next
        assume ?case4
        obtain t\<^sub>i' t\<^sub>j' where "consec_htps \<pi>s t\<^sub>i' t\<^sub>j'" 
                      and "t\<^sub>\<pi> \<le> t\<^sub>i' \<and> t\<^sub>i' < t\<^sub>\<pi> + duration \<pi>" 
                      and "t\<^sub>i' < t \<and> t < t\<^sub>j'"
        using \<open>?case4\<close> by auto
        have "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s"
          unfolding durative_acts_def is_act_simple_def
          using \<open>?case4\<close> \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> by (cases \<pi>) auto
        then have "is_htp \<pi>s (t\<^sub>\<pi> + duration \<pi>)"
          unfolding is_htp_def by auto
        have "t\<^sub>i < t \<and> t < t\<^sub>j"
          using assms 
                strict_sorted_drop_leq_take_le'[OF \<open>strict_sorted (map fst hs)\<close>] 
          by simp
        then have "(t\<^sub>i \<le> t\<^sub>i' \<and> t\<^sub>i' \<le> t\<^sub>j) \<or> (t\<^sub>i' \<le> t\<^sub>i \<and> t\<^sub>i \<le> t\<^sub>j')"
          using \<open>t\<^sub>i' < t \<and> t < t\<^sub>j'\<close> by auto
        then have "t\<^sub>i' = t\<^sub>i" and "t\<^sub>j' = t\<^sub>j"
          using \<open>consec_htps \<pi>s t\<^sub>i t\<^sub>j\<close> \<open>consec_htps \<pi>s t\<^sub>i' t\<^sub>j'\<close> \<open>t\<^sub>i < t \<and> t < t\<^sub>j\<close> \<open>t\<^sub>i' < t \<and> t < t\<^sub>j'\<close> 
          unfolding consec_htps_def by auto (metis dual_order.strict_trans eq_iff leD)+
        then have "t\<^sub>\<pi> \<le> t\<^sub>i \<and> t\<^sub>i < t\<^sub>\<pi> + duration \<pi>"
          using \<open>t\<^sub>\<pi> \<le> t\<^sub>i' \<and> t\<^sub>i' < t\<^sub>\<pi> + duration \<pi>\<close> by simp
        then have "t\<^sub>\<pi> < t\<^sub>j \<and> t\<^sub>j \<le> t\<^sub>\<pi> + (duration \<pi>)"
          using assms \<open>is_htp \<pi>s (t\<^sub>\<pi> + duration \<pi>)\<close> unfolding consec_htps_def by auto
        
        have "Some (precondition a) = res_inst_inv \<pi>"
          using assms \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> \<open>?case4\<close> res_inst_inv_refine unfolding wf_plan_def by auto

        then show ?thesis 
          unfolding invs_of_plan_at_def
          using \<open>(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s\<close> 
                \<open>t\<^sub>\<pi> < t\<^sub>j \<and> t\<^sub>j \<le> t\<^sub>\<pi> + (duration \<pi>)\<close> 
                \<open>Some (precondition a) = res_inst_inv \<pi>\<close>
          by auto
     qed
  qed

  text\<open>Every invariant from @{const invs_of_plan_at} is placed as an invariant ground 
  action in between two consecutive happening time points in the induced happening 
  sequence.\<close>
  lemma invs_of_plan_at_ind_happ_seq:
    assumes "wf_plan \<pi>s"
        and "consec_htps \<pi>s t\<^sub>i t\<^sub>j"
        and "ind_happ_seq \<pi>s hs"
        and "i \<in> invs_of_plan_at t\<^sub>j \<pi>s"
    shows "\<exists>(t,A) \<in> set (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)). \<exists>a \<in> set A. i = precondition a"
  proof -
    let ?hs'="dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)"
    have "strict_sorted (map fst hs)"
      using \<open>ind_happ_seq \<pi>s hs\<close> unfolding ind_happ_seq_def by auto
    obtain t\<^sub>\<pi> \<pi> where "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s" and "t\<^sub>\<pi> < t\<^sub>j \<and> t\<^sub>j \<le> t\<^sub>\<pi> + (duration \<pi>)"
                       and "Some i = res_inst_inv \<pi>"
      using assms unfolding invs_of_plan_at_def by auto
    then have "is_htp \<pi>s t\<^sub>\<pi>"
      unfolding is_htp_def by (auto simp: durative_acts_def)
    then have "t\<^sub>\<pi> \<le> t\<^sub>i \<and> t\<^sub>j \<le> t\<^sub>\<pi> + (duration \<pi>)"
      using assms \<open>t\<^sub>\<pi> < t\<^sub>j \<and> t\<^sub>j \<le> t\<^sub>\<pi> + (duration \<pi>)\<close> unfolding consec_htps_def by auto
    then have "\<exists>(t',as) \<in> set hs. t\<^sub>i < t' \<and> t' < t\<^sub>j \<and> the (res_inst_snap_action \<pi> Over_All) \<in> set as"
      using assms \<open>(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s\<close> unfolding ind_happ_seq_def by auto
    (*then have "\<exists>t'. t\<^sub>i < t' \<and> t' < t\<^sub>j \<and> (\<exists>as. (t',as) \<in> set hs \<and> the (res_inst_snap_action \<pi> Over_All) \<in> set as)"
      using assms \<open>(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s\<close> unfolding ind_happ_seq_def by auto*)
    then obtain t A where "(t,A) \<in> set hs" and "t\<^sub>i < t \<and> t < t\<^sub>j" 
                       and "the (res_inst_snap_action \<pi> Over_All) \<in> set A"
      by auto
    obtain a where "Some a = res_inst_snap_action \<pi> Over_All"
      using \<open>Some i = res_inst_inv \<pi>\<close>
      by (metis option.discI res_inst_inv.simps(1) res_inst_snap_action.elims)
    then have "a \<in> set A"
      using \<open>the (res_inst_snap_action \<pi> Over_All) \<in> set A\<close> by (metis option.sel)

    have "(t,A) \<in> set ?hs'"
      using \<open>t\<^sub>i < t \<and> t < t\<^sub>j\<close>  \<open>(t, A) \<in> set hs\<close> 
            strict_sorted_drop_leq_take_le'[OF \<open>strict_sorted (map fst hs)\<close>]
      by auto
    have "wf_plan_action \<pi>"
      using assms \<open>(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s\<close> unfolding wf_plan_def 
      by (auto simp: durative_acts_def)
    then have "Some (precondition a) = res_inst_inv \<pi>"
      using assms \<open>Some a = res_inst_snap_action \<pi> Over_All\<close> res_inst_inv_refine by auto
    then have "i = precondition a"
      using \<open>Some i = res_inst_inv \<pi>\<close>
      by (metis option.sel)
    show ?thesis
      using \<open>(t,A) \<in> set ?hs'\<close> \<open>a \<in> set A\<close> \<open>i = precondition a\<close> by auto
  qed



  text \<open>In an induced happening sequence all ground actions between two consecutive happening 
  time points have empty effect. Those ground actions are the instantiated durative action 
  for the \texttt{(over all ...)} time specifier.\<close>
  lemma ind_happ_seq_leq\<^sub>i_le\<^sub>j_empty_eff:
    assumes "consec_htps \<pi>s t\<^sub>i t\<^sub>j"
        and "wf_plan \<pi>s"
        and "ind_happ_seq \<pi>s hs"
        and "(t\<^sub>a,A) \<in> set (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs))"
        and "a \<in> set A"
    shows "effect a = Effect [] []"
  proof -
    let ?hs'="dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)"
    have "strict_sorted (map fst hs)"
      using \<open>ind_happ_seq \<pi>s hs\<close> unfolding ind_happ_seq_def by auto
    then have "(t\<^sub>a,A) \<in> set hs"
      using \<open>(t\<^sub>a,A) \<in> set ?hs'\<close> by (meson set_dropWhileD set_takeWhileD)
    have "t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j"
      using \<open>(t\<^sub>a,A) \<in> set ?hs'\<close>
            strict_sorted_drop_leq_take_le[OF \<open>strict_sorted (map fst hs)\<close> \<open>(t\<^sub>a,A) \<in> set hs\<close>]
      by auto
    have "\<not>is_htp \<pi>s t\<^sub>a"
      using \<open>t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j\<close> \<open>consec_htps \<pi>s t\<^sub>i t\<^sub>j\<close> unfolding consec_htps_def by auto
    have "A \<noteq> []"
      using \<open>ind_happ_seq \<pi>s hs\<close> \<open>(t\<^sub>a,A) \<in> set hs\<close> unfolding ind_happ_seq_def by auto
    have "\<exists>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s. inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a)"
      using \<open>ind_happ_seq \<pi>s hs\<close> \<open>(t\<^sub>a,A) \<in> set hs\<close> \<open>a \<in> set A\<close> unfolding ind_happ_seq_def by auto
    then obtain t\<^sub>\<pi> \<pi> where "(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s" and "inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a)"
      by auto
    then have "is_htp \<pi>s t\<^sub>\<pi>"
      unfolding is_htp_def by auto
    let ?case1="res_inst \<pi> = Some a \<and> t\<^sub>\<pi> = t\<^sub>a"
    let ?case2="res_inst_snap_action \<pi> At_Start = Some a \<and> t\<^sub>\<pi> = t\<^sub>a"
    let ?case3="res_inst_snap_action \<pi> At_End = Some a \<and> t\<^sub>\<pi> + (duration \<pi>) = t\<^sub>a"
    let ?case4="res_inst_snap_action \<pi> Over_All = Some a \<and> 
          (\<exists>t\<^sub>i t\<^sub>j. consec_htps \<pi>s t\<^sub>i t\<^sub>j \<and> t\<^sub>\<pi> \<le> t\<^sub>i \<and> t\<^sub>j \<le> t\<^sub>\<pi> + (duration \<pi>) \<and> t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j)"
    have "?case1 \<or> ?case2 \<or> ?case3 \<or> ?case4"
      using \<open>inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a)\<close> by simp
    then show ?thesis
      proof (elim disjE)
        assume ?case1
        then show ?thesis
          using \<open>\<not>is_htp \<pi>s t\<^sub>a\<close> \<open>is_htp \<pi>s t\<^sub>\<pi>\<close> by auto
      next
        assume ?case2
        then show ?thesis
          using \<open>\<not>is_htp \<pi>s t\<^sub>a\<close> \<open>is_htp \<pi>s t\<^sub>\<pi>\<close> by auto
      next
        assume ?case3
        then have "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s"
          unfolding durative_acts_def is_act_simple_def
          using \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> by (cases \<pi>) auto
        then have "is_htp \<pi>s (t\<^sub>\<pi> + (duration \<pi>))"
          unfolding is_htp_def by auto
        then show ?thesis
          using \<open>?case3\<close> \<open>\<not>is_htp \<pi>s t\<^sub>a\<close> \<open>is_htp \<pi>s (t\<^sub>\<pi> + (duration \<pi>))\<close> by auto
      next
        assume ?case4
        let ?a\<^sub>i\<^sub>n\<^sub>v="the (res_inst_snap_action \<pi> Over_All)"
        have "wf_plan_action \<pi>"
          using \<open>wf_plan \<pi>s\<close> \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close>
          unfolding wf_plan_def by auto
        obtain a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a where a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a_def: "Some a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a = resolve_action_schema (name \<pi>)"
          using \<open>wf_plan_action \<pi>\<close> by (cases \<pi>) (auto split: option.splits)
        then have "a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a \<in> set (actions D)"
          unfolding resolve_action_schema_def by (metis index_by_eq_SomeD)
        then have "wf_action_schema a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a"
          using wf_domain
          unfolding wf_domain_def by auto
        then show ?thesis
          using \<open>?case4\<close> wf_over_all_empty_eff[OF \<open>wf_plan_action \<pi>\<close> 
                                                  \<open>wf_action_schema a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a\<close> a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a_def]
          by auto
      qed
    qed

  text \<open>Applying a happening containing only action with empty effect, doesn't 
  change the current state. \<close>
  lemma apply_happ_empty_effect:
    assumes "\<forall>(t\<^sub>a,A) \<in> set hs. \<forall>a \<in> set A. effect a = Effect [] []"
    shows "\<forall>h \<in> set hs. apply_happ h M = M"
    using assms by (induction hs) auto

  text \<open>Combining @{thm wf_ast_problem.ind_happ_seq_leq\<^sub>i_le\<^sub>j_empty_eff} 
  and @{thm apply_happ_empty_effect}: Applying the happening in between two consecutive 
  happening time points doesn't change the current state.\<close>
  lemma ind_happ_seq_leq\<^sub>i_le\<^sub>j:
    assumes "consec_htps \<pi>s t\<^sub>i t\<^sub>j"
        and "wf_plan \<pi>s"
        and "ind_happ_seq \<pi>s hs"
      shows "\<forall>h \<in> set (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)). apply_happ h M = M"
    using assms apply_happ_empty_effect ind_happ_seq_leq\<^sub>i_le\<^sub>j_empty_eff
    by auto

  lemma valid_happ_seq_M\<^sub>i_M\<^sub>i_precond:
    assumes "\<forall>h \<in> set hs. apply_happ h M\<^sub>i = M\<^sub>i"
        and "valid_happ_seq M\<^sub>i hs M\<^sub>i"
      shows "\<forall>(t\<^sub>a,as) \<in> set hs. \<forall>a\<in> set as. M\<^sub>i \<^sup>c\<TTurnstile>\<^sub>= precondition a"
    using assms by (induction M\<^sub>i hs M\<^sub>i rule: valid_happ_seq.induct) auto

  lemma valid_happ_seq_leq\<^sub>i_le\<^sub>j_aux1:
    assumes "consec_htps \<pi>s t\<^sub>i t\<^sub>j"
        and "wf_plan \<pi>s"
        and "ind_happ_seq \<pi>s hs"
        and "valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)) M\<^sub>j"
      shows "\<forall>(t\<^sub>a,as) \<in> set (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)). \<forall>a\<in> set as. M\<^sub>i \<^sup>c\<TTurnstile>\<^sub>= precondition a"
  proof -
    let ?hs'="dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)"
    have "\<forall>h \<in> set ?hs'. apply_happ h M\<^sub>i = M\<^sub>i"
      using assms ind_happ_seq_leq\<^sub>i_le\<^sub>j by simp
    have "valid_happ_seq M\<^sub>i ?hs' M\<^sub>i"
      using assms valid_happ_seq_M\<^sub>j_is_M\<^sub>i[OF \<open>\<forall>h \<in> set ?hs'. apply_happ h M\<^sub>i = M\<^sub>i\<close>] by auto
    then show ?thesis
      using assms \<open>\<forall>h \<in> set ?hs'. apply_happ h M\<^sub>i = M\<^sub>i\<close> valid_happ_seq_M\<^sub>i_M\<^sub>i_precond by simp
  qed

  lemma valid_happ_seq_leq\<^sub>i_le\<^sub>j_aux2:
    assumes "\<forall>h \<in> set hs. apply_happ h M\<^sub>i = M\<^sub>i"
        and "\<forall>(t\<^sub>a,A) \<in> set hs. \<forall>a\<in> set A. M\<^sub>i \<^sup>c\<TTurnstile>\<^sub>= precondition a"
        and "\<forall>(t\<^sub>a,A) \<in> set hs. \<forall>(t\<^sub>a',A') \<in> set hs. 
             \<forall>a \<in> set A. \<forall>a' \<in> set A'. acts_non_intrf a a'"
    shows "valid_happ_seq M\<^sub>i hs M\<^sub>i"
    using assms
    by (induction hs) (auto split: prod.splits simp: pairwise_def)

end \<comment> \<open>Context \<open>wf_ast_problem\<close>\<close> 

context ast_problem
begin

  text\<open>All invariants from @{const invs_of_plan_at} are satisfied iff an induced happening 
  sequence is valid in between two consecutive happening time points.\<close>
  lemma (in wf_ast_problem) valid_happ_seq_leq\<^sub>i_le\<^sub>j_invs_of_plan_at:
    assumes "wf_plan \<pi>s"
        and "consec_htps \<pi>s t\<^sub>i t\<^sub>j"
        and "ind_happ_seq \<pi>s hs"
    shows "valid_happ_seq M (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)) M 
            \<longleftrightarrow> (\<forall>i \<in> invs_of_plan_at t\<^sub>j \<pi>s. M \<^sup>c\<TTurnstile>\<^sub>= i)"
  proof
    let ?hs'="dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)"
    assume "valid_happ_seq M ?hs' M"
    then show "\<forall>i \<in> invs_of_plan_at t\<^sub>j \<pi>s. M \<^sup>c\<TTurnstile>\<^sub>= i"
      using assms  invs_of_plan_at_ind_happ_seq[OF assms]
            valid_happ_seq_leq\<^sub>i_le\<^sub>j_aux1 
       by fastforce
  next 
    let ?hs'="dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)"
    assume "\<forall>i \<in> invs_of_plan_at t\<^sub>j \<pi>s. M \<^sup>c\<TTurnstile>\<^sub>= i"
    have 1: "\<forall>h \<in> set ?hs'. apply_happ h M = M"
      using assms ind_happ_seq_leq\<^sub>i_le\<^sub>j by simp
    have 2: "\<forall>(t\<^sub>a,A) \<in> set ?hs'. \<forall>a\<in> set A. M \<^sup>c\<TTurnstile>\<^sub>= precondition a"
      using \<open>\<forall>i \<in> invs_of_plan_at t\<^sub>j \<pi>s. M \<^sup>c\<TTurnstile>\<^sub>= i\<close> ind_happ_seq_invs_of_plan_at[OF assms] by auto
    have "\<forall>(t\<^sub>a,A) \<in> set ?hs'. \<forall>a \<in> set A. effect a = Effect [] []"
      using assms ind_happ_seq_leq\<^sub>i_le\<^sub>j_empty_eff by auto
    then have 3: "\<forall>(t\<^sub>a,A) \<in> set ?hs'. \<forall>(t\<^sub>a',A') \<in> set ?hs'. 
                    \<forall>a \<in> set A. \<forall>a' \<in> set A'. acts_non_intrf a a'"
      unfolding acts_non_intrf_def by (auto simp: Let_def)
    show "valid_happ_seq M ?hs' M"
      using valid_happ_seq_leq\<^sub>i_le\<^sub>j_aux2[OF 1 2 3] by auto
  qed

  lemma drop_take_leq\<^sub>i_le_leq\<^sub>j_aux:
    assumes "t\<^sub>k \<le> t\<^sub>j"
        and "strict_sorted (map fst hs)"
    shows "takeWhile (le t\<^sub>k) hs @ takeWhile (leq t\<^sub>j) (dropWhile (le t\<^sub>k) hs) = takeWhile (leq t\<^sub>j) hs"
    using assms by (induction hs) (auto simp: le_def leq_def)

  text \<open>We can split up a happening sequence via @{const dropWhile} and @{const takeWhile}\<close>
  lemma drop_take_leq\<^sub>i_le_leq\<^sub>j_split_app:
    assumes "t\<^sub>i < t\<^sub>k" and "t\<^sub>k \<le> t\<^sub>j"
        and "strict_sorted (map fst hs)"
      shows "dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>k) hs) @ dropWhile (le t\<^sub>k) (takeWhile (leq t\<^sub>j) hs) 
              = dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs)"
    using \<open>t\<^sub>i < t\<^sub>k\<close> drop_take_leq\<^sub>i_le_leq\<^sub>j_aux[OF \<open>t\<^sub>k \<le> t\<^sub>j\<close> \<open>strict_sorted (map fst hs)\<close>]
          strict_sorted_drop_le_take_leq_comm[OF \<open>t\<^sub>k \<le> t\<^sub>j\<close> \<open>strict_sorted (map fst hs)\<close>]
    by (induction hs) (auto simp: le_def leq_def)

  text \<open>Some properties of @{const valid_happ_seq} that are needed later.\<close>

  lemma valid_happ_seq_app_iff:
    "valid_happ_seq M\<^sub>0 (hs\<^sub>1@hs\<^sub>2) M\<^sub>j \<longleftrightarrow> (\<exists>M\<^sub>i. valid_happ_seq M\<^sub>0 hs\<^sub>1 M\<^sub>i \<and> valid_happ_seq M\<^sub>i hs\<^sub>2 M\<^sub>j)"
    by (induction hs\<^sub>1 arbitrary: hs\<^sub>2 M\<^sub>0 M\<^sub>j) auto

  lemma valid_happ_seq_split_iff:
    "valid_happ_seq M\<^sub>0 hs M\<^sub>j \<longleftrightarrow> 
      (\<exists>M\<^sub>i. valid_happ_seq M\<^sub>0 (takeWhile f hs) M\<^sub>i \<and> valid_happ_seq M\<^sub>i (dropWhile f hs) M\<^sub>j)"
    using valid_happ_seq_app_iff by force

  text \<open>Every happening sequence contains a happening at every happening time point.\<close>
  lemma ind_happ_seq_happ_at_htps:
    assumes "is_htp \<pi>s t\<^sub>i"
      and "ind_happ_seq \<pi>s hs"
    shows "\<exists>A\<^sub>i. (t\<^sub>i,A\<^sub>i) \<in> set hs"
  proof -
    have "(\<exists>\<pi>. (t\<^sub>i,\<pi>) \<in> set \<pi>s) \<or> (\<exists>(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s. t\<^sub>i = t\<^sub>\<pi> + (duration \<pi>))"
      using \<open>is_htp \<pi>s t\<^sub>i\<close> unfolding is_htp_def by simp
    then show ?thesis
    proof
      assume "\<exists>\<pi>. (t\<^sub>i,\<pi>) \<in> set \<pi>s"
      then obtain \<pi> where "(t\<^sub>i,\<pi>) \<in> set \<pi>s"
        by auto
      then show ?thesis
        using \<open>ind_happ_seq \<pi>s hs\<close>
        unfolding ind_happ_seq_def durative_acts_def simple_acts_def 
        apply (cases \<pi>) by auto blast+
    next
      assume "\<exists>(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s. t\<^sub>i = t\<^sub>\<pi> + (duration \<pi>)"
      then obtain t\<^sub>\<pi> \<pi> where "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s" and "t\<^sub>i = t\<^sub>\<pi> + (duration \<pi>)"
        by auto
      then show ?thesis
        using \<open>ind_happ_seq \<pi>s hs\<close>
        unfolding ind_happ_seq_def durative_acts_def simple_acts_def 
        apply (cases \<pi>) by auto force+
    qed
  qed

  lemma distinct_single_set_list: "set xs = {x} \<Longrightarrow> distinct xs \<Longrightarrow> xs = [x]"
    by (induction xs) auto

  text \<open>An induced happening sequence contain exactly one happening for 
  every happening time point.\<close>
  lemma ind_happ_seq_le\<^sub>i_leq\<^sub>i:
    assumes "is_htp \<pi>s t\<^sub>i"
        and "ind_happ_seq \<pi>s hs"
    shows "\<exists>A\<^sub>i. dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>i) hs) = [(t\<^sub>i,A\<^sub>i)]"
  proof -
    have "strict_sorted (map fst hs)"
      using \<open>ind_happ_seq \<pi>s hs\<close>
      unfolding ind_happ_seq_def by auto
    let ?hs'="dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>i) hs)"
    have "set ?hs' \<subseteq> set hs"
      using set_dropWhileD set_takeWhileD by fastforce
    have "distinct hs"
      using \<open>strict_sorted (map fst hs)\<close> distinct_mapI by (auto simp: strict_sorted_iff)
    then have "distinct ?hs'"
      using distinct_dropWhile distinct_takeWhile by auto
    obtain A\<^sub>i where "(t\<^sub>i,A\<^sub>i) \<in> set hs"
      using ind_happ_seq_happ_at_htps[OF \<open>is_htp \<pi>s t\<^sub>i\<close> \<open>ind_happ_seq \<pi>s hs\<close>] by auto
    then have "(t\<^sub>i,A\<^sub>i) \<in> set ?hs'"
      unfolding le_def leq_def
      using \<open>strict_sorted (map fst hs)\<close> by (induction hs) auto
    have "\<forall>(t\<^sub>a,A) \<in> set ?hs'. t\<^sub>a = t\<^sub>i"
      using \<open>set ?hs' \<subseteq> set hs\<close> strict_sorted_drop_le_take_leq[OF \<open>strict_sorted (map fst hs)\<close>]
      by auto
    have "\<forall>(t\<^sub>1,A\<^sub>1) \<in> set hs. \<forall>(t\<^sub>2,A\<^sub>2) \<in> set hs. t\<^sub>1 = t\<^sub>2 \<longrightarrow> A\<^sub>1 = A\<^sub>2"
      using \<open>strict_sorted (map fst hs)\<close> by (auto simp: strict_sorted_iff distinct_map_fstD)
    then have "\<forall>(t\<^sub>1,A\<^sub>1) \<in> set ?hs'. \<forall>(t\<^sub>2,A\<^sub>2) \<in> set ?hs'. t\<^sub>1 = t\<^sub>2 \<longrightarrow> A\<^sub>1 = A\<^sub>2"
      using \<open>set ?hs' \<subseteq> set hs\<close> by blast
    then have "\<forall>(t\<^sub>a,as') \<in> set ?hs'. t\<^sub>a = t\<^sub>i \<and> as' = A\<^sub>i"
      using \<open>(t\<^sub>i,A\<^sub>i) \<in> set ?hs'\<close> \<open>\<forall>(t\<^sub>a,as) \<in> set ?hs'. t\<^sub>a = t\<^sub>i\<close> by auto force
    then have "set ?hs' = {(t\<^sub>i,A\<^sub>i)}"
      using \<open>(t\<^sub>i,A\<^sub>i) \<in> set ?hs'\<close> by blast
    then show ?thesis
      using distinct_single_set_list[OF \<open>set ?hs' = {(t\<^sub>i,A\<^sub>i)}\<close> \<open>distinct ?hs'\<close>] by simp
  qed

  text\<open>@{const invs_of_plan_at} is valid for a single happening time point iff any 
  induced happening sequence is valid from the previous happening time point to the 
  happening time point.\<close>
  lemma (in wf_ast_problem) valid_happ_seq_valid_state_seq_consec_htps:
    assumes "wf_plan \<pi>s"
        and "consec_htps \<pi>s t\<^sub>i t\<^sub>j"
        and "ind_happ_seq \<pi>s hs"
    shows "valid_happ_seq M (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs)) M' 
            \<longleftrightarrow> valid_state_seq M [t\<^sub>j] \<pi>s M'"
  proof
    let ?hs'="dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs)"
    assume "valid_happ_seq M ?hs' M'"

    have "is_htp \<pi>s t\<^sub>j" and "t\<^sub>i < t\<^sub>j" and "t\<^sub>j \<le> t\<^sub>j"
      using \<open>consec_htps \<pi>s t\<^sub>i t\<^sub>j\<close> unfolding consec_htps_def by auto
    have "strict_sorted (map fst hs)"
      using \<open>ind_happ_seq \<pi>s hs\<close> unfolding ind_happ_seq_def by auto
    then have "?hs' 
           = dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs) @ dropWhile (le t\<^sub>j) (takeWhile (leq t\<^sub>j) hs)"
      using drop_take_leq\<^sub>i_le_leq\<^sub>j_split_app[OF \<open>t\<^sub>i < t\<^sub>j\<close> \<open>t\<^sub>j \<le> t\<^sub>j\<close>] by fastforce
    then obtain M'' where "valid_happ_seq M (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)) M''" 
                 and "valid_happ_seq M'' (dropWhile (le t\<^sub>j) (takeWhile (leq t\<^sub>j) hs)) M'"
      using valid_happ_seq_app_iff \<open>valid_happ_seq M ?hs' M'\<close> by auto
    then have "M = M''" 
      using assms valid_happ_seq_M\<^sub>j_is_M\<^sub>i[OF ind_happ_seq_leq\<^sub>i_le\<^sub>j] by auto

    have "is_htp \<pi>s t\<^sub>j"
      using assms unfolding consec_htps_def by auto
    obtain A\<^sub>j where "dropWhile (le t\<^sub>j) (takeWhile (leq t\<^sub>j) hs) = [(t\<^sub>j,A\<^sub>j)]"
      using assms ind_happ_seq_le\<^sub>i_leq\<^sub>i[OF \<open>is_htp \<pi>s t\<^sub>j\<close>] by auto
    then have "(t\<^sub>j,A\<^sub>j) \<in> set hs"
      by (metis list.set_intros(1) set_dropWhileD set_takeWhileD)
    then have "set A\<^sub>j = acts_of_plan_at t\<^sub>j \<pi>s"
      using assms \<open>is_htp \<pi>s t\<^sub>j\<close> ind_happ_seq_htp_acts_of_plan_at by auto
    let ?as="acts_of_plan_at t\<^sub>j \<pi>s"
    have 1: "\<forall>i \<in> invs_of_plan_at t\<^sub>j \<pi>s. M \<^sup>c\<TTurnstile>\<^sub>= i"
     and 2: "\<forall>a\<in> ?as. M \<^sup>c\<TTurnstile>\<^sub>= precondition a" 
     and 3: "\<forall>a \<in> ?as. \<forall>b \<in> ?as. a \<noteq> b \<longrightarrow> acts_non_intrf a b"
     and 4: "apply_eff ?as M = M'"
      using valid_happ_seq_leq\<^sub>i_le\<^sub>j_invs_of_plan_at[OF assms]
            \<open>valid_happ_seq M (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)) M''\<close>
            \<open>valid_happ_seq M'' (dropWhile (le t\<^sub>j) (takeWhile (leq t\<^sub>j) hs)) M'\<close> 
            \<open>M = M''\<close>
            \<open>dropWhile (le t\<^sub>j) (takeWhile (leq t\<^sub>j) hs) = [(t\<^sub>j,A\<^sub>j)]\<close> 
            \<open>set A\<^sub>j = acts_of_plan_at t\<^sub>j \<pi>s\<close>
      by (auto simp: pairwise_def)
    then show "valid_state_seq M [t\<^sub>j] \<pi>s M'"
      by auto
  next
    let ?hs'="dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs)"
    assume "valid_state_seq M [t\<^sub>j] \<pi>s M'"
    let ?A\<^sub>j="acts_of_plan_at t\<^sub>j \<pi>s"
    have 1: "\<forall>i \<in> invs_of_plan_at t\<^sub>j \<pi>s. M \<^sup>c\<TTurnstile>\<^sub>= i"
     and 2: "\<forall>a\<in> ?A\<^sub>j. M \<^sup>c\<TTurnstile>\<^sub>= precondition a" 
     and 3: "\<forall>a \<in> ?A\<^sub>j. \<forall>b \<in> ?A\<^sub>j. a \<noteq> b \<longrightarrow> acts_non_intrf a b"
     and 4: "apply_eff ?A\<^sub>j M = M'"
      using \<open>valid_state_seq M [t\<^sub>j] \<pi>s M'\<close>
      by (induction M "[t\<^sub>j]" \<pi>s M' rule: valid_state_seq.induct) (auto simp: Let_def)

    have "valid_happ_seq M (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)) M"
      using 1 valid_happ_seq_leq\<^sub>i_le\<^sub>j_invs_of_plan_at[OF assms] by auto

    have "is_htp \<pi>s t\<^sub>j"
      using assms unfolding consec_htps_def by auto
    obtain A\<^sub>j where "dropWhile (le t\<^sub>j) (takeWhile (leq t\<^sub>j) hs) = [(t\<^sub>j,A\<^sub>j)]"
      using assms ind_happ_seq_le\<^sub>i_leq\<^sub>i[OF \<open>is_htp \<pi>s t\<^sub>j\<close>] by auto
    then have "(t\<^sub>j,A\<^sub>j) \<in> set hs"
      by (metis list.set_intros(1) set_dropWhileD set_takeWhileD)
    then have "set A\<^sub>j = acts_of_plan_at t\<^sub>j \<pi>s"
      using assms \<open>is_htp \<pi>s t\<^sub>j\<close> ind_happ_seq_htp_acts_of_plan_at by auto
    then have "valid_happ_seq M (dropWhile (le t\<^sub>j) (takeWhile (leq t\<^sub>j) hs)) M'"
      using 2 3 4 \<open>dropWhile (le t\<^sub>j) (takeWhile (leq t\<^sub>j) hs) = [(t\<^sub>j,A\<^sub>j)]\<close> by (auto simp: pairwise_def)

    have "is_htp \<pi>s t\<^sub>j" and "t\<^sub>i < t\<^sub>j" and "t\<^sub>j \<le> t\<^sub>j"
      using \<open>consec_htps \<pi>s t\<^sub>i t\<^sub>j\<close> unfolding consec_htps_def by auto
    have "strict_sorted (map fst hs)"
      using \<open>ind_happ_seq \<pi>s hs\<close> unfolding ind_happ_seq_def by auto
    then have "?hs' 
           = dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs) @ dropWhile (le t\<^sub>j) (takeWhile (leq t\<^sub>j) hs)"
      using drop_take_leq\<^sub>i_le_leq\<^sub>j_split_app[OF \<open>t\<^sub>i < t\<^sub>j\<close> \<open>t\<^sub>j \<le> t\<^sub>j\<close>] by fastforce
    then show "valid_happ_seq M ?hs' M'"
      using \<open>valid_happ_seq M (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs)) M\<close> 
            \<open>valid_happ_seq M (dropWhile (le t\<^sub>j) (takeWhile (leq t\<^sub>j) hs)) M'\<close>
            valid_happ_seq_app_iff
      by auto
  qed


  lemma cons_consec_htps:
    assumes "htps_seq \<pi>s htps" 
        and "htps = ts\<^sub>1 @ t\<^sub>i # t\<^sub>j # ts\<^sub>2"
      shows "consec_htps \<pi>s t\<^sub>i t\<^sub>j"
  proof -
    obtain ts' where "htps = ts\<^sub>1 @ t\<^sub>i # ts' @ t\<^sub>j # ts\<^sub>2" and "ts' = []"
      using assms by auto
    then have "\<forall>t \<in> set htps. t\<^sub>i < t \<and> t < t\<^sub>j \<longrightarrow> t \<in> set ts'"
      using assms unfolding htps_seq_def by (auto simp: sorted_append strict_sorted_iff)
    then have "\<not>(\<exists>t \<in> set htps. t\<^sub>i < t \<and> t < t\<^sub>j)"
      using \<open>ts' = []\<close> by auto
    then have "\<forall>t. t \<in> set htps \<longrightarrow> t \<le> t\<^sub>i \<or> t\<^sub>j \<le> t"
      by auto
    then show ?thesis
      using assms unfolding consec_htps_def htps_seq_def 
      by (auto simp: sorted_append strict_sorted_iff)
  qed

  lemma (in wf_ast_problem) valid_happ_seq_valid_state_seq_i_to_j_aux:
    fixes \<pi>s
    assumes "htps_seq \<pi>s htps"
        and "htps = ts\<^sub>1 @ t\<^sub>i # ts\<^sub>2 @ t\<^sub>j # ts\<^sub>3" 
        and "wf_plan \<pi>s"
        and "ind_happ_seq \<pi>s hs"
    shows "valid_happ_seq M (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs)) M' 
            \<longleftrightarrow> valid_state_seq M (ts\<^sub>2 @ [t\<^sub>j]) \<pi>s M'"
    using assms 
  proof (induction ts\<^sub>2 arbitrary: ts\<^sub>1 t\<^sub>i ts\<^sub>3 M)
    case Nil
    let ?hs'="dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs)"
    have "consec_htps \<pi>s t\<^sub>i t\<^sub>j"
      using Nil.prems cons_consec_htps by auto
    then show ?case 
      using Nil.prems valid_happ_seq_valid_state_seq_consec_htps by auto
  next
    case (Cons t\<^sub>i' ts\<^sub>2)
    have "strict_sorted htps"
      using assms unfolding htps_seq_def by auto
    then have "consec_htps \<pi>s t\<^sub>i t\<^sub>i'"
      using Cons.prems cons_consec_htps by auto
    have "t\<^sub>i \<in> set htps" and "t\<^sub>i' \<in> set htps" and "t\<^sub>j \<in> set htps"
      using Cons.prems by auto
    have "t\<^sub>i < t\<^sub>j"
      using Cons.prems split_list2_le[OF \<open>strict_sorted htps\<close> \<open>t\<^sub>i \<in> set htps\<close> \<open>t\<^sub>j \<in> set htps\<close>]
      by blast
    have "t\<^sub>i \<le> t\<^sub>i'"
      using \<open>consec_htps \<pi>s t\<^sub>i t\<^sub>i'\<close> unfolding consec_htps_def by auto
    have "htps = (ts\<^sub>1 @ [t\<^sub>i]) @ t\<^sub>i' # ts\<^sub>2 @ t\<^sub>j # ts\<^sub>3"
      using Cons.prems by auto
    then have "t\<^sub>i' \<le> t\<^sub>j"
      using Cons.prems split_list2_le[OF \<open>strict_sorted htps\<close> \<open>t\<^sub>i' \<in> set htps\<close> \<open>t\<^sub>j \<in> set htps\<close>]
            less_eq_rat_def 
      by blast

    let ?hs'="dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs)"
    have "strict_sorted (map fst hs)"
      using \<open>ind_happ_seq \<pi>s hs\<close> unfolding ind_happ_seq_def by auto
    then have hs'_app: "?hs' = dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>i') hs) 
                        @ dropWhile (leq t\<^sub>i') (takeWhile (leq t\<^sub>j) hs)"
      using drop_take_leq\<^sub>i_leq_leq\<^sub>j_simp[OF \<open>t\<^sub>i \<le> t\<^sub>i'\<close> \<open>t\<^sub>i' \<le> t\<^sub>j\<close>] by fastforce

    show "valid_happ_seq M ?hs' M' \<longleftrightarrow> valid_state_seq M ((t\<^sub>i' # ts\<^sub>2) @ [t\<^sub>j]) \<pi>s M'"
    proof
      assume "valid_happ_seq M ?hs' M'"
      then obtain M'' where ii': "valid_happ_seq M (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>i') hs)) M''" 
                        and i'j: "valid_happ_seq M'' (dropWhile (leq t\<^sub>i') (takeWhile (leq t\<^sub>j) hs)) M'"
        using hs'_app valid_happ_seq_app_iff by auto
      then have 1: "valid_state_seq M [t\<^sub>i'] \<pi>s M''"
        using Cons.prems \<open>consec_htps \<pi>s t\<^sub>i t\<^sub>i'\<close> valid_happ_seq_valid_state_seq_consec_htps by blast
      have 2: "valid_state_seq M'' (ts\<^sub>2 @ [t\<^sub>j]) \<pi>s M'"
        using assms Cons.IH \<open>htps = (ts\<^sub>1 @ [t\<^sub>i]) @ t\<^sub>i' # ts\<^sub>2 @ t\<^sub>j # ts\<^sub>3\<close> i'j by blast
      then show "valid_state_seq M ((t\<^sub>i' # ts\<^sub>2) @ [t\<^sub>j]) \<pi>s M'"
        using 1 2 valid_state_seq_app_iff[where ts\<^sub>1="[t\<^sub>i']"] by auto              
    next
      assume "valid_state_seq M ((t\<^sub>i' # ts\<^sub>2) @ [t\<^sub>j]) \<pi>s M'"
      then obtain M'' where i': "valid_state_seq M [t\<^sub>i'] \<pi>s M''" 
                        and ts\<^sub>2j: "valid_state_seq M'' (ts\<^sub>2 @ [t\<^sub>j]) \<pi>s M'"
        using valid_state_seq_app_iff[where ts\<^sub>1="[t\<^sub>i']"] by auto
      then have 1: "valid_happ_seq M (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>i') hs)) M''"
        using Cons.prems \<open>consec_htps \<pi>s t\<^sub>i t\<^sub>i'\<close> valid_happ_seq_valid_state_seq_consec_htps
        by blast
      have 2: "valid_happ_seq M'' (dropWhile (leq t\<^sub>i') (takeWhile (leq t\<^sub>j) hs)) M'"
        using assms Cons.IH \<open>htps = (ts\<^sub>1 @ [t\<^sub>i]) @ t\<^sub>i' # ts\<^sub>2 @ t\<^sub>j # ts\<^sub>3\<close> ts\<^sub>2j by blast
      then show "valid_happ_seq M ?hs' M'"
        using hs'_app 1 2 valid_happ_seq_app_iff by auto
    qed
  qed

  lemma prod_list_Nil: "\<forall>x\<^sub>1 x\<^sub>2. (x\<^sub>1,x\<^sub>2) \<notin> set xs \<Longrightarrow> xs = []"
    by (induction xs) auto

  text \<open>An induced happening sequence is only Nil iff the orginal plan was Nil\<close>
  lemma ind_happ_seq_Nil: "ind_happ_seq \<pi>s hs \<Longrightarrow> \<pi>s = [] \<longleftrightarrow> hs = []"
    unfolding ind_happ_seq_def simple_acts_def durative_acts_def is_act_simple_def 
    by (auto simp: prod_list_Nil) (* TODO: proof without 'prod_list_Nil' *)

  lemma htps_seq_Nil_iff:
    assumes "htps_seq \<pi>s htps"
    shows "\<pi>s = [] \<longleftrightarrow> htps = []"
  proof
    assume "\<pi>s = []"
    then show "htps = []"
      using assms dur_acts_subset unfolding htps_seq_def is_htp_def by fastforce
  next
    assume "htps = []"
    show "\<pi>s = []"
    proof (rule ccontr)
      assume "\<pi>s \<noteq> []"
      then obtain t\<^sub>\<pi> \<pi> where "(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s"
        by (meson prod_list_Nil)
      then have "t\<^sub>\<pi> \<in> set htps"
        using assms unfolding htps_seq_def is_htp_def by auto
      then show "False"
        using \<open>htps = []\<close> by simp
    qed
  qed

  lemma non_Nil_sorted_last_max: 
    assumes "(xs::('a::linorder) list) \<noteq> []" 
        and "sorted xs" 
        and "x\<^sub>m\<^sub>a\<^sub>x = last xs" 
    shows "\<forall>x \<in> set xs. x \<le> x\<^sub>m\<^sub>a\<^sub>x"
    using assms by (induction xs) auto

  text \<open>Proof for the existence of a sequence of happening time point for every plan. 
  Needed later in the proof for the completeness of the semantics.\<close>
  lemma htps_seq_exists: "\<exists>htps. htps_seq \<pi>s htps"
  proof (induction \<pi>s)
    case Nil
    then have "htps_seq [] []"
      unfolding htps_seq_def is_htp_def using dur_acts_subset by fastforce
    then show ?case 
      by auto
  next
    case (Cons \<pi> \<pi>s)
    then show ?case
    proof (cases \<pi>)
      case (Pair t\<^sub>\<pi> \<pi>')
      obtain htps' where "htps_seq \<pi>s htps'"
        using Cons.IH by auto
      then have "sorted htps'" and "distinct htps'"
        unfolding htps_seq_def by (auto simp: strict_sorted_iff)

      have "\<forall>t. t \<in> set htps' \<longleftrightarrow> is_htp \<pi>s t"
        using \<open>htps_seq \<pi>s htps'\<close> unfolding htps_seq_def by auto
      then have "\<forall>t. t \<in> set htps' \<longrightarrow> is_htp (\<pi>#\<pi>s) t"
        unfolding is_htp_def durative_acts_def is_act_simple_def by auto
      have "is_htp (\<pi>#\<pi>s) t\<^sub>\<pi>"
        unfolding is_htp_def using Pair by auto
      show ?thesis
      proof (cases \<pi>')
        case (Simple_Plan_Action n args)
        then obtain htps where "htps = insort_insert t\<^sub>\<pi> htps'"
          by auto
        then have "strict_sorted htps"
          using sorted_insort_insert[OF \<open>sorted htps'\<close>] 
                distinct_insort_insert[OF \<open>distinct htps'\<close>]
          by (auto simp: strict_sorted_iff)
        have "\<forall>t. is_htp \<pi>s t \<longrightarrow> t \<in> set htps" and "t\<^sub>\<pi> \<in> set htps"
          using \<open>\<forall>t. t \<in> set htps' \<longleftrightarrow> is_htp \<pi>s t\<close> 
                \<open>htps = insort_insert t\<^sub>\<pi> htps'\<close> 
          by (auto simp: set_insort_insert)
        then have "\<forall>t. is_htp (\<pi>#\<pi>s) t \<longrightarrow> t \<in> set htps"
          unfolding is_htp_def durative_acts_def is_act_simple_def
          using Pair Simple_Plan_Action by auto
        have "\<forall>t. t \<in> set htps \<longrightarrow> is_htp (\<pi>#\<pi>s) t"
          using \<open>\<forall>t. t \<in> set htps' \<longrightarrow> is_htp (\<pi>#\<pi>s) t\<close> 
                \<open>htps = insort_insert t\<^sub>\<pi> htps'\<close> 
                \<open>is_htp (\<pi>#\<pi>s) t\<^sub>\<pi>\<close>
          by (auto simp: set_insort_insert)
        show ?thesis 
          using \<open>strict_sorted htps\<close> 
                \<open>\<forall>t. is_htp (\<pi>#\<pi>s) t \<longrightarrow> t \<in> set htps\<close> 
                \<open>\<forall>t. t \<in> set htps \<longrightarrow> is_htp (\<pi>#\<pi>s) t\<close>
          by (auto simp: htps_seq_def)
      next
        case (Durative_Plan_Action n args d)
        then have "is_htp (\<pi>#\<pi>s) (t\<^sub>\<pi> + d)"
          unfolding is_htp_def durative_acts_def is_act_simple_def using Pair by auto
        obtain htps where "htps = insort_insert t\<^sub>\<pi> (insort_insert (t\<^sub>\<pi> + d) htps')"
          by auto
        then have "strict_sorted htps"
          using \<open>sorted htps'\<close> \<open>distinct htps'\<close>
          by (auto simp: sorted_insort_insert distinct_insort_insert strict_sorted_iff)
        have "\<forall>t. is_htp \<pi>s t \<longrightarrow> t \<in> set htps" and "t\<^sub>\<pi> \<in> set htps" and "(t\<^sub>\<pi> + d) \<in> set htps"
          using \<open>\<forall>t. t \<in> set htps' \<longleftrightarrow> is_htp \<pi>s t\<close> 
                \<open>htps = insort_insert t\<^sub>\<pi> (insort_insert (t\<^sub>\<pi> + d) htps')\<close> 
          by (auto simp: set_insort_insert)
        then have "\<forall>t. is_htp (\<pi>#\<pi>s) t \<longrightarrow> t \<in> set htps"
          unfolding is_htp_def durative_acts_def is_act_simple_def
          using Pair Durative_Plan_Action by auto
        have "\<forall>t. t \<in> set htps \<longrightarrow> is_htp (\<pi>#\<pi>s) t"
          using \<open>\<forall>t. t \<in> set htps' \<longrightarrow> is_htp (\<pi>#\<pi>s) t\<close> 
                \<open>htps = insort_insert t\<^sub>\<pi> (insort_insert (t\<^sub>\<pi> + d) htps')\<close> 
                \<open>is_htp (\<pi>#\<pi>s) t\<^sub>\<pi>\<close> \<open>is_htp (\<pi>#\<pi>s) (t\<^sub>\<pi> + d)\<close>
          by (auto simp: set_insort_insert)
        show ?thesis 
          using \<open>strict_sorted htps\<close> 
                \<open>\<forall>t. is_htp (\<pi>#\<pi>s) t \<longrightarrow> t \<in> set htps\<close> 
                \<open>\<forall>t. t \<in> set htps \<longrightarrow> is_htp (\<pi>#\<pi>s) t\<close>
          by (auto simp: htps_seq_def)
      qed
    qed
  qed

end

context wf_ast_problem
begin


  text \<open>Two induced happening sequences contain the same ground actions in between two 
  consecutive happening time points.\<close>
  lemma ind_happ_seqs_same_acts_leq\<^sub>i_le\<^sub>j:
    assumes "consec_htps \<pi>s t\<^sub>i t\<^sub>j" 
        and "ind_happ_seq \<pi>s hs\<^sub>1" 
        and "ind_happ_seq \<pi>s hs\<^sub>2"
        and "(t\<^sub>a,A) \<in> set (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs\<^sub>1))"
        and "a \<in> set A"
      shows "\<exists>t\<^sub>a' A'. (t\<^sub>a',A') \<in> set (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs\<^sub>2)) \<and> a \<in> set A'"
  proof -
    let ?hs\<^sub>1'="dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs\<^sub>1)"
    let ?hs\<^sub>2'="dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs\<^sub>2)"
    have "strict_sorted (map fst hs\<^sub>1)" and "strict_sorted (map fst hs\<^sub>2)"
      using \<open>ind_happ_seq \<pi>s hs\<^sub>1\<close> \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close> unfolding ind_happ_seq_def by auto
    have "(t\<^sub>a,A) \<in> set hs\<^sub>1"
      using \<open>(t\<^sub>a,A) \<in> set ?hs\<^sub>1'\<close> by (meson set_dropWhileD set_takeWhileD) 
    have "t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j"
      using \<open>(t\<^sub>a,A) \<in> set ?hs\<^sub>1'\<close>
            strict_sorted_drop_leq_take_le[OF \<open>strict_sorted (map fst hs\<^sub>1)\<close> \<open>(t\<^sub>a,A) \<in> set hs\<^sub>1\<close>]
      by auto
    have "\<exists>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s. inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a)"
      using \<open>ind_happ_seq \<pi>s hs\<^sub>1\<close> \<open>(t\<^sub>a,A) \<in> set hs\<^sub>1\<close> \<open>a \<in> set A\<close> 
      unfolding ind_happ_seq_def by auto
    then obtain t\<^sub>\<pi> \<pi> where "(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s" and "inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a)"
      by auto
    let ?case1="res_inst \<pi> = Some a \<and> t\<^sub>\<pi> = t\<^sub>a"
    let ?case2="res_inst_snap_action \<pi> At_Start = Some a \<and> t\<^sub>\<pi> = t\<^sub>a"
    let ?case3="res_inst_snap_action \<pi> At_End = Some a \<and> t\<^sub>\<pi> + (duration \<pi>) = t\<^sub>a"
    let ?case4="res_inst_snap_action \<pi> Over_All = Some a \<and> 
          (\<exists>t\<^sub>i t\<^sub>j. consec_htps \<pi>s t\<^sub>i t\<^sub>j \<and> t\<^sub>\<pi> \<le> t\<^sub>i \<and> t\<^sub>j \<le> t\<^sub>\<pi> + (duration \<pi>) \<and> t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j)"
    have "?case1 \<or> ?case2 \<or> ?case3 \<or> ?case4"
      using \<open>inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a)\<close> by simp
    then show ?thesis
    proof (elim disjE)
      assume ?case1
      then have "(t\<^sub>\<pi>,\<pi>) \<in> simple_acts \<pi>s"
        unfolding simple_acts_def is_act_simple_def using \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> by (cases \<pi>) auto
      then have "\<exists>as. (t\<^sub>\<pi>,as) \<in> set hs\<^sub>2 \<and> the (res_inst \<pi>) \<in> set as"
        using \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close> unfolding ind_happ_seq_def by auto
      then obtain A' where "(t\<^sub>\<pi>,A') \<in> set hs\<^sub>2" and "the (res_inst \<pi>) \<in> set A'" 
        by auto
      then have "(t\<^sub>a,A') \<in> set hs\<^sub>2"
        using \<open>?case1\<close> by auto
      show ?thesis
        using \<open>?case1\<close> \<open>t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j\<close> \<open>the (res_inst \<pi>) \<in> set A'\<close>
              strict_sorted_drop_leq_take_le[OF \<open>strict_sorted (map fst hs\<^sub>2)\<close> \<open>(t\<^sub>a,A') \<in> set hs\<^sub>2\<close>]
        by auto   
    next
      assume ?case2
      let ?a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t="the (res_inst_snap_action \<pi> At_Start)"
      have "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s"
        unfolding durative_acts_def is_act_simple_def
        using \<open>?case2\<close> \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> by (cases \<pi>) auto
      then have "\<exists>as. (t\<^sub>\<pi>,as) \<in> set hs\<^sub>2 \<and> ?a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t \<in> set as"
        using \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close> unfolding ind_happ_seq_def by auto
      then obtain A' where "(t\<^sub>\<pi>,A') \<in> set hs\<^sub>2" and "?a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t \<in> set A'" 
        by auto
      then have "(t\<^sub>a,A') \<in> set hs\<^sub>2"
        using \<open>?case2\<close> by auto
      show ?thesis
        using \<open>?case2\<close> \<open>t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j\<close> \<open>?a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t \<in> set A'\<close>
              strict_sorted_drop_leq_take_le[OF \<open>strict_sorted (map fst hs\<^sub>2)\<close> \<open>(t\<^sub>a,A') \<in> set hs\<^sub>2\<close>]
        by auto
    next
      assume ?case3
      let ?a\<^sub>e\<^sub>n\<^sub>d="the (res_inst_snap_action \<pi> At_End)"
      have "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s"
        unfolding durative_acts_def is_act_simple_def
        using \<open>?case3\<close> \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> by (cases \<pi>) auto
      then have "\<exists>as. (t\<^sub>\<pi> + (duration \<pi>),as) \<in> set hs\<^sub>2 \<and> ?a\<^sub>e\<^sub>n\<^sub>d \<in> set as"
        using \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close> unfolding ind_happ_seq_def by auto
      then obtain A' where "(t\<^sub>\<pi> + (duration \<pi>),A') \<in> set hs\<^sub>2" and "?a\<^sub>e\<^sub>n\<^sub>d \<in> set A'" 
        by auto
      then have "(t\<^sub>a,A') \<in> set hs\<^sub>2"
        using \<open>?case3\<close> by auto
      show ?thesis
        using \<open>?case3\<close> \<open>t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j\<close> \<open>?a\<^sub>e\<^sub>n\<^sub>d \<in> set A'\<close>
              strict_sorted_drop_leq_take_le[OF \<open>strict_sorted (map fst hs\<^sub>2)\<close> \<open>(t\<^sub>a,A') \<in> set hs\<^sub>2\<close>]
        by auto
    next
      assume ?case4
      let ?a\<^sub>i\<^sub>n\<^sub>v="the (res_inst_snap_action \<pi> Over_All)"
      obtain t\<^sub>i' t\<^sub>j' where "consec_htps \<pi>s t\<^sub>i' t\<^sub>j'" 
                      and "t\<^sub>\<pi> \<le> t\<^sub>i' \<and> t\<^sub>j' \<le> t\<^sub>\<pi> + duration \<pi>" 
                      and "t\<^sub>i' < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j'"
        using \<open>?case4\<close> by auto
      have "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s"
        unfolding durative_acts_def is_act_simple_def
        using \<open>?case4\<close> \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> by (cases \<pi>) auto
      (*then have "\<exists>t'. t\<^sub>i' < t' \<and> t' < t\<^sub>j' \<and> (\<exists>as. (t',as) \<in> set hs\<^sub>2 \<and>  ?a\<^sub>i\<^sub>n\<^sub>v \<in> set as)"
        using \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close> unfolding ind_happ_seq_def
        using \<open>consec_htps \<pi>s t\<^sub>i' t\<^sub>j'\<close> \<open>t\<^sub>\<pi> \<le> t\<^sub>i' \<and> t\<^sub>j' \<le> t\<^sub>\<pi> + duration \<pi>\<close> by auto*)
      then have "\<exists>(t',as) \<in> set hs\<^sub>2. t\<^sub>i' < t' \<and> t' < t\<^sub>j' \<and> ?a\<^sub>i\<^sub>n\<^sub>v \<in> set as"
        using \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close> unfolding ind_happ_seq_def
        using \<open>consec_htps \<pi>s t\<^sub>i' t\<^sub>j'\<close> \<open>t\<^sub>\<pi> \<le> t\<^sub>i' \<and> t\<^sub>j' \<le> t\<^sub>\<pi> + duration \<pi>\<close> by auto
      then obtain t\<^sub>a' A' where "(t\<^sub>a',A') \<in> set hs\<^sub>2" and "t\<^sub>i' < t\<^sub>a' \<and> t\<^sub>a' < t\<^sub>j'" and "?a\<^sub>i\<^sub>n\<^sub>v \<in> set A'"
        by auto
      then have "(t\<^sub>a',A') \<in> set hs\<^sub>2"
        using \<open>?case4\<close> by auto
      have "t\<^sub>i < t\<^sub>a' \<and> t\<^sub>a' < t\<^sub>j"
        using assms \<open>consec_htps \<pi>s t\<^sub>i' t\<^sub>j'\<close> \<open>t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j\<close> \<open>t\<^sub>i' < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j'\<close> 
              \<open>t\<^sub>i' < t\<^sub>a' \<and> t\<^sub>a' < t\<^sub>j'\<close> unfolding consec_htps_def by auto
      show ?thesis
        using \<open>?case4\<close> \<open>?a\<^sub>i\<^sub>n\<^sub>v \<in> set A'\<close> \<open>t\<^sub>i < t\<^sub>a' \<and> t\<^sub>a' < t\<^sub>j\<close>
              strict_sorted_drop_leq_take_le[OF \<open>strict_sorted (map fst hs\<^sub>2)\<close> \<open>(t\<^sub>a',A') \<in> set hs\<^sub>2\<close>]
        by auto
    qed
  qed

  text \<open>If one induced happening sequence is a valid happening sequence in between two 
  consecutive happening time points, then every other induced happening sequence is 
  also valid in between those consecutive happening time point.\<close>
  lemma valid_happ_seq_leq\<^sub>i_le\<^sub>j:
    assumes "consec_htps \<pi>s t\<^sub>i t\<^sub>j" 
        and "wf_plan \<pi>s"
        and "ind_happ_seq \<pi>s hs\<^sub>1" 
        and "ind_happ_seq \<pi>s hs\<^sub>2" 
        and "valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs\<^sub>1)) M\<^sub>j"
    shows "valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs\<^sub>2)) M\<^sub>j"
  proof -
    let ?hs\<^sub>1'="dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs\<^sub>1)"
    let ?hs\<^sub>2'="dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs\<^sub>2)"
    have "\<forall>h \<in> set ?hs\<^sub>1'. apply_happ h M\<^sub>i = M\<^sub>i"
      using assms ind_happ_seq_leq\<^sub>i_le\<^sub>j by simp
    have "M\<^sub>i = M\<^sub>j"
      using valid_happ_seq_M\<^sub>j_is_M\<^sub>i[OF \<open>\<forall>h \<in> set ?hs\<^sub>1'. apply_happ h M\<^sub>i = M\<^sub>i\<close>] 
            \<open>valid_happ_seq M\<^sub>i ?hs\<^sub>1' M\<^sub>j\<close> by simp
    have "\<forall>(t\<^sub>a,A) \<in> set ?hs\<^sub>1'. \<forall>a\<in> set A. M\<^sub>i \<^sup>c\<TTurnstile>\<^sub>= precondition a"
      using assms valid_happ_seq_leq\<^sub>i_le\<^sub>j_aux1 \<open>valid_happ_seq M\<^sub>i ?hs\<^sub>1' M\<^sub>j\<close> by simp
    have 1: "\<forall>h \<in> set ?hs\<^sub>2'. apply_happ h M\<^sub>i = M\<^sub>i"
      using assms ind_happ_seq_leq\<^sub>i_le\<^sub>j by simp
    have 2: "\<forall>(t\<^sub>a,A) \<in> set ?hs\<^sub>2'. \<forall>a\<in> set A. M\<^sub>i \<^sup>c\<TTurnstile>\<^sub>= precondition a"
      using assms ind_happ_seqs_same_acts_leq\<^sub>i_le\<^sub>j
            \<open>\<forall>(t\<^sub>a,A) \<in> set ?hs\<^sub>1'. \<forall>a\<in> set A. M\<^sub>i \<^sup>c\<TTurnstile>\<^sub>= precondition a\<close> by blast
    have "\<forall>(t\<^sub>a,A) \<in> set ?hs\<^sub>2'. \<forall>a \<in> set A. effect a = Effect [] []"
      using assms ind_happ_seq_leq\<^sub>i_le\<^sub>j_empty_eff by auto
    then have 3: "\<forall>(t\<^sub>a,A) \<in> set ?hs\<^sub>2'. \<forall>(t\<^sub>a',A') \<in> set ?hs\<^sub>2'. 
                    \<forall>a \<in> set A. \<forall>a' \<in> set A'. acts_non_intrf a a'"
      unfolding acts_non_intrf_def by (auto simp: Let_def)
    then show ?thesis
      using valid_happ_seq_leq\<^sub>i_le\<^sub>j_aux2[OF 1 2 3] \<open>M\<^sub>i = M\<^sub>j\<close> by auto
  qed


  text \<open>An induced happening sequence contain exactly one happening for 
  every happening time point.\<close>
  lemma ind_happ_seq_le\<^sub>i_leq\<^sub>i:
    assumes "is_htp \<pi>s t\<^sub>i"
        and "ind_happ_seq \<pi>s hs"
    shows "\<exists>A\<^sub>i. dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>i) hs) = [(t\<^sub>i,A\<^sub>i)]"
  proof -
    have "strict_sorted (map fst hs)"
      using \<open>ind_happ_seq \<pi>s hs\<close>
      unfolding ind_happ_seq_def by auto
    let ?hs'="dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>i) hs)"
    have "set ?hs' \<subseteq> set hs"
      using set_dropWhileD set_takeWhileD by fastforce
    have "distinct hs"
      using \<open>strict_sorted (map fst hs)\<close> distinct_mapI by (auto simp: strict_sorted_iff)
    then have "distinct ?hs'"
      using distinct_dropWhile distinct_takeWhile by auto
    obtain A\<^sub>i where "(t\<^sub>i,A\<^sub>i) \<in> set hs"
      using assms(1) assms(2) ast_problem.ind_happ_seq_happ_at_htps
      by blast
    then have "(t\<^sub>i,A\<^sub>i) \<in> set ?hs'"
      unfolding le_def leq_def
      using \<open>strict_sorted (map fst hs)\<close> by (induction hs) auto
    have "\<forall>(t\<^sub>a,A) \<in> set ?hs'. t\<^sub>a = t\<^sub>i"
      using \<open>set ?hs' \<subseteq> set hs\<close> strict_sorted_drop_le_take_leq[OF \<open>strict_sorted (map fst hs)\<close>]
      by auto
    have "\<forall>(t\<^sub>1,A\<^sub>1) \<in> set hs. \<forall>(t\<^sub>2,A\<^sub>2) \<in> set hs. t\<^sub>1 = t\<^sub>2 \<longrightarrow> A\<^sub>1 = A\<^sub>2"
      using \<open>strict_sorted (map fst hs)\<close> by (auto simp: strict_sorted_iff distinct_map_fstD)
    then have "\<forall>(t\<^sub>1,A\<^sub>1) \<in> set ?hs'. \<forall>(t\<^sub>2,A\<^sub>2) \<in> set ?hs'. t\<^sub>1 = t\<^sub>2 \<longrightarrow> A\<^sub>1 = A\<^sub>2"
      using \<open>set ?hs' \<subseteq> set hs\<close> by blast
    then have "\<forall>(t\<^sub>a,as') \<in> set ?hs'. t\<^sub>a = t\<^sub>i \<and> as' = A\<^sub>i"
      using \<open>(t\<^sub>i,A\<^sub>i) \<in> set ?hs'\<close> \<open>\<forall>(t\<^sub>a,as) \<in> set ?hs'. t\<^sub>a = t\<^sub>i\<close> by auto force
    then have "set ?hs' = {(t\<^sub>i,A\<^sub>i)}"
      using \<open>(t\<^sub>i,A\<^sub>i) \<in> set ?hs'\<close> by blast
    then show ?thesis
      using distinct_single_set_list[OF \<open>set ?hs' = {(t\<^sub>i,A\<^sub>i)}\<close> \<open>distinct ?hs'\<close>] by simp
  qed

  text \<open>Two induced happening sequences contain the same ground actions for 
  every happening time point.\<close>
  lemma ind_happ_seqs_same_acts_le\<^sub>i_leq\<^sub>i:
    assumes "is_htp \<pi>s t\<^sub>i" 
        and "ind_happ_seq \<pi>s hs\<^sub>1" 
        and "ind_happ_seq \<pi>s hs\<^sub>2"
        and "(t\<^sub>a,A) \<in> set (dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>i) hs\<^sub>1))"
        and "a \<in> set A"
    shows "\<exists>t\<^sub>a' A'. (t\<^sub>a',A') \<in> set (dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>i) hs\<^sub>2)) \<and> a \<in> set A'"
  proof -
    have "strict_sorted (map fst hs\<^sub>1)" and "strict_sorted (map fst hs\<^sub>2)"
      using \<open>ind_happ_seq \<pi>s hs\<^sub>1\<close> \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close>
      unfolding ind_happ_seq_def by auto
    let ?hs\<^sub>1'="dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>i) hs\<^sub>1)"
    let ?hs\<^sub>2'="dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>i) hs\<^sub>2)"
    have "(t\<^sub>a,A) \<in> set hs\<^sub>1"
      using \<open>(t\<^sub>a,A) \<in> set ?hs\<^sub>1'\<close> by (meson set_dropWhileD set_takeWhileD)
    have "t\<^sub>i = t\<^sub>a"
      using \<open>(t\<^sub>a,A) \<in> set ?hs\<^sub>1'\<close>
            strict_sorted_drop_le_take_leq[OF \<open>strict_sorted (map fst hs\<^sub>1)\<close> \<open>(t\<^sub>a,A) \<in> set hs\<^sub>1\<close>]
      by auto
    have "\<exists>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s. inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a)"
      using \<open>ind_happ_seq \<pi>s hs\<^sub>1\<close> \<open>(t\<^sub>a,A) \<in> set hs\<^sub>1\<close> \<open>a \<in> set A\<close>
      unfolding ind_happ_seq_def by auto
    then obtain t\<^sub>\<pi> \<pi> where "(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s" and "inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a)"
      by auto
    let ?case1="res_inst \<pi> = Some a \<and> t\<^sub>\<pi> = t\<^sub>a"
    let ?case2="res_inst_snap_action \<pi> At_Start = Some a \<and> t\<^sub>\<pi> = t\<^sub>a"
    let ?case3="res_inst_snap_action \<pi> At_End = Some a \<and> t\<^sub>\<pi> + (duration \<pi>) = t\<^sub>a"
    let ?case4="res_inst_snap_action \<pi> Over_All = Some a \<and> 
          (\<exists>t\<^sub>i t\<^sub>j. consec_htps \<pi>s t\<^sub>i t\<^sub>j \<and> t\<^sub>\<pi> \<le> t\<^sub>i \<and> t\<^sub>j \<le> t\<^sub>\<pi> + (duration \<pi>) \<and> t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j)"
    have "?case1 \<or> ?case2 \<or> ?case3 \<or> ?case4"
      using \<open>inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a)\<close> by simp
    then show ?thesis
      proof (elim disjE)
        assume ?case1
        then have "(t\<^sub>\<pi>,\<pi>) \<in> simple_acts \<pi>s"
          unfolding simple_acts_def is_act_simple_def using \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> by (cases \<pi>) auto
        then have "\<exists>as. (t\<^sub>\<pi>,as) \<in> set hs\<^sub>2 \<and> the (res_inst \<pi>) \<in> set as"
          using \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close> unfolding ind_happ_seq_def by auto
        then obtain A' where "(t\<^sub>\<pi>,A') \<in> set hs\<^sub>2" and "the (res_inst \<pi>) \<in> set A'" 
          by auto
        then have "(t\<^sub>a,A') \<in> set hs\<^sub>2"
          using \<open>?case1\<close> by auto
        show ?thesis
          using \<open>t\<^sub>i = t\<^sub>a\<close> \<open>?case1\<close> \<open>the (res_inst \<pi>) \<in> set A'\<close>
              strict_sorted_drop_le_take_leq[OF \<open>strict_sorted (map fst hs\<^sub>2)\<close> \<open>(t\<^sub>a,A') \<in> set hs\<^sub>2\<close>]
          by auto
      next
        assume ?case2
        let ?a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t="the (res_inst_snap_action \<pi> At_Start)"
        have "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s"
          unfolding durative_acts_def is_act_simple_def
          using \<open>?case2\<close> \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> by (cases \<pi>) auto
        then have "\<exists>as. (t\<^sub>\<pi>,as) \<in> set hs\<^sub>2 \<and> ?a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t \<in> set as"
          using \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close> unfolding ind_happ_seq_def by auto
        then obtain A' where "(t\<^sub>\<pi>,A') \<in> set hs\<^sub>2" and "?a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t \<in> set A'" 
          by auto
        then have "(t\<^sub>a,A') \<in> set hs\<^sub>2"
          using \<open>?case2\<close> by auto
        show ?thesis
          using \<open>t\<^sub>i = t\<^sub>a\<close> \<open>?case2\<close> \<open>?a\<^sub>s\<^sub>t\<^sub>a\<^sub>r\<^sub>t \<in> set A'\<close>
              strict_sorted_drop_le_take_leq[OF \<open>strict_sorted (map fst hs\<^sub>2)\<close> \<open>(t\<^sub>a,A') \<in> set hs\<^sub>2\<close>]
          by auto
    next
      assume ?case3
        let ?a\<^sub>e\<^sub>n\<^sub>d="the (res_inst_snap_action \<pi> At_End)"
        have "(t\<^sub>\<pi>,\<pi>) \<in> durative_acts \<pi>s"
          unfolding durative_acts_def is_act_simple_def
          using \<open>?case3\<close> \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> by (cases \<pi>) auto
        then have "\<exists>as. (t\<^sub>\<pi> + (duration \<pi>),as) \<in> set hs\<^sub>2 \<and> ?a\<^sub>e\<^sub>n\<^sub>d \<in> set as"
          using \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close> unfolding ind_happ_seq_def by auto
        then obtain A' where "(t\<^sub>\<pi> + (duration \<pi>),A') \<in> set hs\<^sub>2" and "?a\<^sub>e\<^sub>n\<^sub>d \<in> set A'" 
          by auto
        then have "(t\<^sub>a,A') \<in> set hs\<^sub>2"
          using \<open>?case3\<close> by auto
        show ?thesis
          using \<open>t\<^sub>i = t\<^sub>a\<close> \<open>?case3\<close> \<open>?a\<^sub>e\<^sub>n\<^sub>d \<in> set A'\<close>
              strict_sorted_drop_le_take_leq[OF \<open>strict_sorted (map fst hs\<^sub>2)\<close> \<open>(t\<^sub>a,A') \<in> set hs\<^sub>2\<close>]
          by auto
      next
        assume ?case4
        obtain t\<^sub>i' t\<^sub>j' where "consec_htps \<pi>s t\<^sub>i' t\<^sub>j'" 
                      and "t\<^sub>\<pi> \<le> t\<^sub>i' \<and> t\<^sub>i' < t\<^sub>\<pi> + duration \<pi>" 
                      and "t\<^sub>i' < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j'"
          using \<open>?case4\<close> by auto
        have "is_htp \<pi>s t\<^sub>a"
          using \<open>is_htp \<pi>s t\<^sub>i\<close> \<open>t\<^sub>i = t\<^sub>a\<close> by simp
        show ?thesis
          using \<open>is_htp \<pi>s t\<^sub>a\<close> \<open>t\<^sub>i' < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j'\<close> \<open>consec_htps \<pi>s t\<^sub>i' t\<^sub>j'\<close>
          unfolding consec_htps_def by auto
      qed
    qed

  text \<open>With @{thm ind_happ_seqs_same_acts_le\<^sub>i_leq\<^sub>i} we can prove: 
  If we have one induced happening sequence that is a valid happening sequence for a 
  single happening time point, then every other induced happening sequence is also valid 
  for that happening time point.\<close>
  lemma valid_happ_seq_le\<^sub>i_leq\<^sub>i:
    assumes "is_htp \<pi>s t\<^sub>i" 
        and "ind_happ_seq \<pi>s hs\<^sub>1" 
        and "ind_happ_seq \<pi>s hs\<^sub>2" 
        and "valid_happ_seq M\<^sub>i (dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>i) hs\<^sub>1)) M\<^sub>j"
    shows "valid_happ_seq M\<^sub>i (dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>i) hs\<^sub>2)) M\<^sub>j"
  proof -
    obtain A\<^sub>1 where "dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>i) hs\<^sub>1) = [(t\<^sub>i, A\<^sub>1)]"
      using assms ind_happ_seq_le\<^sub>i_leq\<^sub>i[OF \<open>is_htp \<pi>s t\<^sub>i\<close> \<open>ind_happ_seq \<pi>s hs\<^sub>1\<close>] by auto
    obtain A\<^sub>2 where "dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>i) hs\<^sub>2) = [(t\<^sub>i, A\<^sub>2)]"
      using assms ind_happ_seq_le\<^sub>i_leq\<^sub>i[OF \<open>is_htp \<pi>s t\<^sub>i\<close> \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close>] by auto
    have "set A\<^sub>1 = set A\<^sub>2"
      using ind_happ_seqs_same_acts_le\<^sub>i_leq\<^sub>i[OF \<open>is_htp \<pi>s t\<^sub>i\<close> \<open>ind_happ_seq \<pi>s hs\<^sub>1\<close>
                                                   \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close>]
             \<open>dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>i) hs\<^sub>1) = [(t\<^sub>i, A\<^sub>1)]\<close>
            ind_happ_seqs_same_acts_le\<^sub>i_leq\<^sub>i[OF \<open>is_htp \<pi>s t\<^sub>i\<close> \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close>
                                                   \<open>ind_happ_seq \<pi>s hs\<^sub>1\<close>]
            \<open>dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>i) hs\<^sub>2) = [(t\<^sub>i, A\<^sub>2)]\<close>
      by auto
    have "valid_happ_seq M\<^sub>i [(t\<^sub>i, A\<^sub>1)] M\<^sub>j"
      using \<open>valid_happ_seq M\<^sub>i (dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>i) hs\<^sub>1)) M\<^sub>j\<close> 
            \<open>dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>i) hs\<^sub>1) = [(t\<^sub>i, A\<^sub>1)]\<close> by simp
    then have "valid_happ_seq M\<^sub>i [(t\<^sub>i,A\<^sub>2)] M\<^sub>j"
      using \<open>set A\<^sub>1 = set A\<^sub>2\<close> by auto
    then show ?thesis
      using \<open>dropWhile (le t\<^sub>i) (takeWhile (leq t\<^sub>i) hs\<^sub>2) = [(t\<^sub>i, A\<^sub>2)]\<close> by auto
  qed


  text \<open>Putting together @{thm wf_ast_problem.valid_happ_seq_leq\<^sub>i_le\<^sub>j} and 
  @{thm valid_happ_seq_le\<^sub>i_leq\<^sub>i}. If we have one induced happening sequence that is 
  valid from a happening time point to the next consecutive happening time point, 
  that every other induced happening sequence is also valid for that interval.\<close>
  lemma valid_happ_seq_consec_htps:
    assumes "consec_htps \<pi>s t\<^sub>i t\<^sub>j"
        and "wf_plan \<pi>s"
        and "ind_happ_seq \<pi>s hs\<^sub>1" 
        and "ind_happ_seq \<pi>s hs\<^sub>2" 
        and "valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs\<^sub>1)) M\<^sub>j"
      shows "valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs\<^sub>2)) M\<^sub>j"
    using assms
  proof -
    have "is_htp \<pi>s t\<^sub>j" and "t\<^sub>i < t\<^sub>j" and "t\<^sub>j \<le> t\<^sub>j"
      using \<open>consec_htps \<pi>s t\<^sub>i t\<^sub>j\<close> unfolding consec_htps_def by auto
    have "strict_sorted (map fst hs\<^sub>1)" and "strict_sorted (map fst hs\<^sub>2)"
      using \<open>ind_happ_seq \<pi>s hs\<^sub>1\<close> \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close> unfolding ind_happ_seq_def by auto
    have "dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs\<^sub>1) 
           = dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs\<^sub>1) @ dropWhile (le t\<^sub>j) (takeWhile (leq t\<^sub>j) hs\<^sub>1)"
      using drop_take_leq\<^sub>i_le_leq\<^sub>j_split_app[OF \<open>t\<^sub>i < t\<^sub>j\<close> \<open>t\<^sub>j \<le> t\<^sub>j\<close> \<open>strict_sorted (map fst hs\<^sub>1)\<close>] 
      by simp
    then obtain M\<^sub>i' where "valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs\<^sub>1)) M\<^sub>i'" 
                 and "valid_happ_seq M\<^sub>i' (dropWhile (le t\<^sub>j) (takeWhile (leq t\<^sub>j) hs\<^sub>1)) M\<^sub>j"
      using valid_happ_seq_app_iff
            \<open>valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs\<^sub>1)) M\<^sub>j\<close> by auto
    have 1: "valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs\<^sub>2)) M\<^sub>i'"
      using valid_happ_seq_leq\<^sub>i_le\<^sub>j
              [OF \<open>consec_htps \<pi>s t\<^sub>i t\<^sub>j\<close> \<open>wf_plan \<pi>s\<close> \<open>ind_happ_seq \<pi>s hs\<^sub>1\<close> \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close>]
            \<open>valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs\<^sub>1)) M\<^sub>i'\<close> by auto
    have 2: "valid_happ_seq M\<^sub>i' (dropWhile (le t\<^sub>j) (takeWhile (leq t\<^sub>j) hs\<^sub>2)) M\<^sub>j"
      using valid_happ_seq_le\<^sub>i_leq\<^sub>i[OF \<open>is_htp \<pi>s t\<^sub>j\<close> \<open>ind_happ_seq \<pi>s hs\<^sub>1\<close> \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close>]
            \<open>valid_happ_seq M\<^sub>i' (dropWhile (le t\<^sub>j) (takeWhile (leq t\<^sub>j) hs\<^sub>1)) M\<^sub>j\<close> by auto
    have "dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs\<^sub>2) 
           = dropWhile (leq t\<^sub>i) (takeWhile (le t\<^sub>j) hs\<^sub>2) @ dropWhile (le t\<^sub>j) (takeWhile (leq t\<^sub>j) hs\<^sub>2)"
      using drop_take_leq\<^sub>i_le_leq\<^sub>j_split_app[OF \<open>t\<^sub>i < t\<^sub>j\<close> \<open>t\<^sub>j \<le> t\<^sub>j\<close> \<open>strict_sorted (map fst hs\<^sub>2)\<close>] 
      by simp
    then show ?thesis
      using valid_happ_seq_app_iff 1 2 by auto
  qed


  lemma htps_state_trace_unique_i_to_j_aux:
    fixes \<pi>s
    assumes "htps_seq \<pi>s htps" 
        and "htps = ts\<^sub>1 @ t\<^sub>i # ts\<^sub>2 @ t\<^sub>j # ts\<^sub>3" 
        and "wf_plan \<pi>s"
        and "ind_happ_seq \<pi>s hs\<^sub>1" 
        and "ind_happ_seq \<pi>s hs\<^sub>2" 
        and "valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs\<^sub>1)) M\<^sub>j"
    shows "valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs\<^sub>2)) M\<^sub>j"
    using assms
  proof (induction ts\<^sub>2 arbitrary: ts\<^sub>1 t\<^sub>i ts\<^sub>3 M\<^sub>i)
    case Nil
    then have "consec_htps \<pi>s t\<^sub>i t\<^sub>j"
       using cons_consec_htps by auto
    then show ?case
      using valid_happ_seq_consec_htps
              [OF \<open>consec_htps \<pi>s t\<^sub>i t\<^sub>j\<close> \<open>wf_plan \<pi>s\<close> \<open>ind_happ_seq \<pi>s hs\<^sub>1\<close> \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close>]
            \<open>valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs\<^sub>1)) M\<^sub>j\<close>
      by (simp add: leq_def)
  next
    case (Cons t\<^sub>i' ts\<^sub>2)
    then have "strict_sorted htps" and "distinct htps"
      using assms unfolding htps_seq_def by (auto simp: strict_sorted_iff)
    have "consec_htps \<pi>s t\<^sub>i t\<^sub>i'"
      using Cons.prems cons_consec_htps by auto
    have "t\<^sub>i \<in> set htps" and "t\<^sub>i' \<in> set htps" and "t\<^sub>j \<in> set htps"
      using \<open>htps = ts\<^sub>1 @ t\<^sub>i # (t\<^sub>i' # ts\<^sub>2) @ t\<^sub>j # ts\<^sub>3\<close> by auto
    have "t\<^sub>i < t\<^sub>j"
      using split_list2_le[OF \<open>strict_sorted htps\<close> \<open>t\<^sub>i \<in> set htps\<close> \<open>t\<^sub>j \<in> set htps\<close>]
            \<open>htps = ts\<^sub>1 @ t\<^sub>i # (t\<^sub>i' # ts\<^sub>2) @ t\<^sub>j # ts\<^sub>3\<close> by blast
    have "t\<^sub>i \<le> t\<^sub>i'"
      using \<open>consec_htps \<pi>s t\<^sub>i t\<^sub>i'\<close> unfolding consec_htps_def by auto
    have "htps = (ts\<^sub>1 @ [t\<^sub>i]) @ t\<^sub>i' # ts\<^sub>2 @ t\<^sub>j # ts\<^sub>3"
      using Cons.prems by auto
    then have "t\<^sub>i' \<le> t\<^sub>j"
      using Cons.prems split_list2_le[OF \<open>strict_sorted htps\<close> \<open>t\<^sub>i' \<in> set htps\<close> \<open>t\<^sub>j \<in> set htps\<close>]
            less_eq_rat_def by blast
    have "strict_sorted (map fst hs\<^sub>1)" and "strict_sorted (map fst hs\<^sub>2)"
      using \<open>ind_happ_seq \<pi>s hs\<^sub>1\<close> \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close> unfolding ind_happ_seq_def by auto
    have "\<exists>M\<^sub>i'. valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>i') hs\<^sub>1)) M\<^sub>i' 
            \<and> valid_happ_seq M\<^sub>i' (dropWhile (leq t\<^sub>i') (takeWhile (leq t\<^sub>j) hs\<^sub>1)) M\<^sub>j"
      using drop_take_leq\<^sub>i_leq_leq\<^sub>j_simp[OF \<open>t\<^sub>i \<le> t\<^sub>i'\<close> \<open>t\<^sub>i' \<le> t\<^sub>j\<close> \<open>strict_sorted (map fst hs\<^sub>1)\<close>]
            valid_happ_seq_app_iff
            \<open>valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs\<^sub>1)) M\<^sub>j\<close> 
      by (metis (no_types, lifting))
    then obtain M\<^sub>i' where "valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>i') hs\<^sub>1)) M\<^sub>i'"
                and "valid_happ_seq M\<^sub>i' (dropWhile (leq t\<^sub>i') (takeWhile (leq t\<^sub>j) hs\<^sub>1)) M\<^sub>j"
      by auto
    then have "valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>i') hs\<^sub>2)) M\<^sub>i'"
      using valid_happ_seq_consec_htps
              [OF \<open>consec_htps \<pi>s t\<^sub>i t\<^sub>i'\<close> \<open>wf_plan \<pi>s\<close> \<open>ind_happ_seq \<pi>s hs\<^sub>1\<close> \<open>ind_happ_seq \<pi>s hs\<^sub>2\<close>]
            \<open>valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>i') hs\<^sub>1)) M\<^sub>i'\<close> by simp
    have "htps = (ts\<^sub>1 @ [t\<^sub>i]) @ t\<^sub>i' # ts\<^sub>2 @ t\<^sub>j # ts\<^sub>3"
      using Cons.prems by simp
    then have "valid_happ_seq M\<^sub>i' (dropWhile (leq t\<^sub>i') (takeWhile (leq t\<^sub>j) hs\<^sub>2)) M\<^sub>j"
      using assms Cons.IH
            \<open>valid_happ_seq M\<^sub>i' (dropWhile (leq t\<^sub>i') (takeWhile (leq t\<^sub>j) hs\<^sub>1)) M\<^sub>j\<close> by fastforce
    then show ?case 
      using drop_take_leq\<^sub>i_leq_leq\<^sub>j_simp[OF \<open>t\<^sub>i \<le> t\<^sub>i'\<close> \<open>t\<^sub>i' \<le> t\<^sub>j\<close> \<open>strict_sorted (map fst hs\<^sub>2)\<close>]
            valid_happ_seq_app_iff
            \<open>valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>i') hs\<^sub>2)) M\<^sub>i'\<close>
            \<open>valid_happ_seq M\<^sub>i' (dropWhile (leq t\<^sub>i') (takeWhile (leq t\<^sub>j) hs\<^sub>2)) M\<^sub>j\<close>
      by (metis (no_types, lifting))
  qed

  text \<open>With @{thm wf_ast_problem.valid_happ_seq_consec_htps} we can now proof that if one 
  induced happening sequence is valid form a happening time point to another happening time 
  point (not just consecutive), than every other induced happening sequence is valid for 
  between those two happening time points.\<close>
  lemma valid_happ_seq_htp_i_to_htp_j:
    assumes "t\<^sub>i < t\<^sub>j" 
        and "is_htp \<pi>s t\<^sub>i" 
        and "is_htp \<pi>s t\<^sub>j"
        and "wf_plan \<pi>s"
        and "ind_happ_seq \<pi>s hs\<^sub>1" 
        and "ind_happ_seq \<pi>s hs\<^sub>2" 
        and "valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs\<^sub>1)) M\<^sub>j"
    shows "valid_happ_seq M\<^sub>i (dropWhile (leq t\<^sub>i) (takeWhile (leq t\<^sub>j) hs\<^sub>2)) M\<^sub>j"
  proof -
    obtain htps where "htps_seq \<pi>s htps"
      using htps_seq_exists by auto
    then have "strict_sorted htps" and "t\<^sub>i \<in> set htps" and "t\<^sub>j \<in> set htps"
      unfolding htps_seq_def using assms by (auto simp: strict_sorted_iff)
    then obtain ts\<^sub>1 ts\<^sub>2 ts\<^sub>3 where "htps = ts\<^sub>1 @ t\<^sub>i # ts\<^sub>2 @ t\<^sub>j # ts\<^sub>3"
      using \<open>t\<^sub>i < t\<^sub>j\<close> split_list2_le[OF \<open>strict_sorted htps\<close> \<open>t\<^sub>i \<in> set htps\<close> \<open>t\<^sub>j \<in> set htps\<close>] by auto
    then show ?thesis
      using assms \<open>htps_seq \<pi>s htps\<close> htps_state_trace_unique_i_to_j_aux by metis
  qed

  lemma happ_tp_leq_t\<^sub>m\<^sub>i\<^sub>n_t\<^sub>m\<^sub>a\<^sub>x:
    assumes "(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s"
        and "inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a)" 
    shows "(\<exists>t\<^sub>j. is_htp \<pi>s t\<^sub>j \<and> t\<^sub>j \<le> t\<^sub>a) \<and> (\<exists>t\<^sub>j. is_htp \<pi>s t\<^sub>j \<and> t\<^sub>a \<le> t\<^sub>j)"
  proof -
    let ?case1="res_inst \<pi> = Some a \<and> t\<^sub>\<pi> = t\<^sub>a"
    let ?case2="res_inst_snap_action \<pi> At_Start = Some a \<and> t\<^sub>\<pi> = t\<^sub>a"
    let ?case3="res_inst_snap_action \<pi> At_End = Some a \<and> t\<^sub>\<pi> + (duration \<pi>) = t\<^sub>a"
    let ?case4="res_inst_snap_action \<pi> Over_All = Some a \<and> 
          (\<exists>t\<^sub>i t\<^sub>j. consec_htps \<pi>s t\<^sub>i t\<^sub>j \<and> t\<^sub>\<pi> \<le> t\<^sub>i \<and> t\<^sub>j \<le> t\<^sub>\<pi> + (duration \<pi>) \<and> t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j)"
    have "?case1 \<or> ?case2 \<or> ?case3 \<or> ?case4"
      using \<open>inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a)\<close> by simp
    then show ?thesis
    proof (elim disjE)
      assume ?case1
      then show ?thesis
        using \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> by (auto simp: is_htp_def)
    next
      assume ?case2
      then show ?thesis
        using \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> by (auto simp: is_htp_def)
    next
      assume ?case3
      then show ?thesis
        unfolding is_htp_def durative_acts_def is_act_simple_def
        using \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> \<open>?case3\<close> by (cases \<pi>) fastforce+
    next
      assume ?case4
      then obtain t\<^sub>i t\<^sub>j where "consec_htps \<pi>s t\<^sub>i t\<^sub>j" and "t\<^sub>\<pi> \<le> t\<^sub>i \<and> t\<^sub>i < t\<^sub>\<pi> + (duration \<pi>)" 
                         and "t\<^sub>i < t\<^sub>a \<and> t\<^sub>a < t\<^sub>j"
        by auto
      then show ?thesis
        using \<open>consec_htps \<pi>s t\<^sub>i t\<^sub>j\<close> unfolding consec_htps_def by auto
    qed
  qed

  text \<open>Proof that every happening of a induced happening sequence is in between 
  the smallest and largest happening time point.\<close>
  lemma ind_happ_seq_htps_leq_t\<^sub>m\<^sub>i\<^sub>n_t\<^sub>m\<^sub>a\<^sub>x:
    fixes \<pi>s
    assumes "ind_happ_seq \<pi>s (hs'@hs)"
        and "\<forall>t\<^sub>i. is_htp \<pi>s t\<^sub>i \<longrightarrow> t\<^sub>m\<^sub>i\<^sub>n \<le> t\<^sub>i"
        and "\<forall>t\<^sub>i. is_htp \<pi>s t\<^sub>i \<longrightarrow> t\<^sub>i \<le> t\<^sub>m\<^sub>a\<^sub>x"
    shows "\<forall>(t\<^sub>a,A) \<in> set hs. t\<^sub>m\<^sub>i\<^sub>n \<le> t\<^sub>a \<and> t\<^sub>a \<le> t\<^sub>m\<^sub>a\<^sub>x"
    using assms
  proof (induction hs arbitrary: hs')
    case Nil
    then show ?case 
      by simp
  next
    case (Cons h hs)
    then show ?case
    proof (cases h)
      case (Pair t\<^sub>a A)
        then obtain a where "a \<in> set A"
          using \<open>ind_happ_seq \<pi>s (hs'@h#hs)\<close> unfolding ind_happ_seq_def by (cases A) auto
        then have "\<exists>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s. inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a)"
          using \<open>ind_happ_seq \<pi>s (hs'@h#hs)\<close> Pair unfolding ind_happ_seq_def by auto
        then obtain t\<^sub>\<pi> \<pi> where "(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s" and "inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a)"
          by auto
        obtain hs'' where "hs''=hs'@[h]"
          by simp
        then have "ind_happ_seq \<pi>s (hs''@hs)"
          using \<open>ind_happ_seq \<pi>s (hs'@h#hs)\<close> by simp
         show ?thesis
           using assms Pair Cons.IH[OF \<open>ind_happ_seq \<pi>s (hs''@hs)\<close>]
                 happ_tp_leq_t\<^sub>m\<^sub>i\<^sub>n_t\<^sub>m\<^sub>a\<^sub>x[OF \<open>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s\<close> \<open>inst_of_plan_action \<pi>s (t\<^sub>\<pi>,\<pi>) (t\<^sub>a,a)\<close>]
           by auto
    qed
  qed

  lemma valid_happ_seq_state_unique:
    assumes "valid_happ_seq M\<^sub>0 hs M\<^sub>i" and "valid_happ_seq M\<^sub>0 hs M\<^sub>i'"
    shows "M\<^sub>i = M\<^sub>i'"
    using assms by (induction M\<^sub>0 hs M\<^sub>i rule: valid_happ_seq.induct) auto

  lemma  valid_happ_seq_iff_valid_state_seq:
    fixes \<pi>s
    assumes "htps_seq \<pi>s htps"
        and "wf_plan \<pi>s"
        and "ind_happ_seq \<pi>s hs"
    shows "valid_happ_seq M\<^sub>0 hs M\<^sub>n \<longleftrightarrow> valid_state_seq M\<^sub>0 htps \<pi>s M\<^sub>n"
  proof (cases "\<pi>s = []")
    case True
      then have "hs = []" and "htps = []"
        using assms ind_happ_seq_Nil htps_seq_Nil_iff by auto
      then show ?thesis
        by auto
  next
    case False

    have "strict_sorted (map fst hs)"
      using \<open>ind_happ_seq \<pi>s hs\<close> unfolding ind_happ_seq_def by auto
    have "htps \<noteq> []" and "sorted htps" and "distinct htps" and "strict_sorted htps"
      using assms \<open>\<pi>s \<noteq> []\<close> htps_seq_Nil_iff unfolding htps_seq_def
      by (auto simp: strict_sorted_iff)

    text \<open>Obtain the smallest happening time point.\<close>
    obtain t\<^sub>m\<^sub>i\<^sub>n where "t\<^sub>m\<^sub>i\<^sub>n = hd htps"
      by auto
    then have "t\<^sub>m\<^sub>i\<^sub>n \<in> set htps"
      using \<open>htps \<noteq> []\<close> by auto
    have "is_htp \<pi>s t\<^sub>m\<^sub>i\<^sub>n" and "\<forall>t\<^sub>k. is_htp \<pi>s t\<^sub>k \<longrightarrow> t\<^sub>m\<^sub>i\<^sub>n \<le> t\<^sub>k"
      using assms \<open>htps \<noteq> []\<close> \<open>sorted htps\<close> \<open>t\<^sub>m\<^sub>i\<^sub>n = hd htps\<close> sorted_hd_min 
      by (auto simp: htps_seq_def)
    have "\<forall>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s. t\<^sub>m\<^sub>i\<^sub>n \<le> t\<^sub>\<pi>"
      using \<open>\<forall>t\<^sub>k. is_htp \<pi>s t\<^sub>k \<longrightarrow> t\<^sub>m\<^sub>i\<^sub>n \<le> t\<^sub>k\<close> by (auto simp: is_htp_def)
    
    text \<open>Obtain the largest happening time point.\<close>
    obtain t\<^sub>m\<^sub>a\<^sub>x where "t\<^sub>m\<^sub>a\<^sub>x = last htps"
      by auto
    then have "t\<^sub>m\<^sub>a\<^sub>x \<in> set htps"
      using \<open>htps \<noteq> []\<close> by auto
    then have "is_htp \<pi>s t\<^sub>m\<^sub>a\<^sub>x" and "\<forall>t\<^sub>k. is_htp \<pi>s t\<^sub>k \<longrightarrow> t\<^sub>k \<le> t\<^sub>m\<^sub>a\<^sub>x"
      using assms non_Nil_sorted_last_max[OF \<open>htps \<noteq> []\<close> \<open>sorted htps\<close> \<open>t\<^sub>m\<^sub>a\<^sub>x = last htps\<close>] 
      by (auto simp: htps_seq_def)

    have "\<forall>(t\<^sub>a,A)\<in>set hs. t\<^sub>m\<^sub>i\<^sub>n \<le> t\<^sub>a \<and> t\<^sub>a \<le> t\<^sub>m\<^sub>a\<^sub>x"
      using assms \<open>\<forall>t\<^sub>k. is_htp \<pi>s t\<^sub>k \<longrightarrow> t\<^sub>k \<le> t\<^sub>m\<^sub>a\<^sub>x\<close> \<open>\<forall>t\<^sub>k. is_htp \<pi>s t\<^sub>k \<longrightarrow> t\<^sub>m\<^sub>i\<^sub>n \<le> t\<^sub>k\<close> 
            ind_happ_seq_htps_leq_t\<^sub>m\<^sub>i\<^sub>n_t\<^sub>m\<^sub>a\<^sub>x[where hs'="[]"]
      by auto
    
    have "takeWhile (leq t\<^sub>m\<^sub>a\<^sub>x) hs = hs"
      using \<open>\<forall>(t\<^sub>a,A)\<in>set hs. t\<^sub>m\<^sub>i\<^sub>n \<le> t\<^sub>a \<and> t\<^sub>a \<le> t\<^sub>m\<^sub>a\<^sub>x\<close> by (auto simp: leq_def)
    have "dropWhile (le t\<^sub>m\<^sub>i\<^sub>n) (takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs) = takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs"
      using \<open>\<forall>(t\<^sub>a,A)\<in>set hs. t\<^sub>m\<^sub>i\<^sub>n \<le> t\<^sub>a \<and> t\<^sub>a \<le> t\<^sub>m\<^sub>a\<^sub>x\<close> \<open>strict_sorted (map fst hs)\<close>
      by (induction hs) (auto simp: le_def)

    obtain as\<^sub>m\<^sub>i\<^sub>n where "dropWhile (le t\<^sub>m\<^sub>i\<^sub>n) (takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs) = [(t\<^sub>m\<^sub>i\<^sub>n,as\<^sub>m\<^sub>i\<^sub>n)]"
      using assms ind_happ_seq_le\<^sub>i_leq\<^sub>i[OF \<open>is_htp \<pi>s t\<^sub>m\<^sub>i\<^sub>n\<close>] by auto
    then have "(t\<^sub>m\<^sub>i\<^sub>n,as\<^sub>m\<^sub>i\<^sub>n) \<in> set hs"
      by (metis list.set_intros(1) set_dropWhileD set_takeWhileD)
    then have "set as\<^sub>m\<^sub>i\<^sub>n = acts_of_plan_at t\<^sub>m\<^sub>i\<^sub>n \<pi>s"
      using assms \<open>is_htp \<pi>s t\<^sub>m\<^sub>i\<^sub>n\<close> ind_happ_seq_htp_acts_of_plan_at by auto
    let ?as="acts_of_plan_at t\<^sub>m\<^sub>i\<^sub>n \<pi>s"

    have "t\<^sub>m\<^sub>i\<^sub>n \<le> t\<^sub>m\<^sub>a\<^sub>x"
      using \<open>is_htp \<pi>s t\<^sub>m\<^sub>i\<^sub>n\<close> by (simp add: \<open>\<forall>t\<^sub>k. is_htp \<pi>s t\<^sub>k \<longrightarrow> t\<^sub>k \<le> t\<^sub>m\<^sub>a\<^sub>x\<close>)

    show "valid_happ_seq M\<^sub>0 hs M\<^sub>n \<longleftrightarrow> valid_state_seq M\<^sub>0 htps \<pi>s M\<^sub>n"
    proof
      assume "valid_happ_seq M\<^sub>0 hs M\<^sub>n"
      text \<open>Remove first happening from the happening sequence.\<close>
      then have "\<exists>M\<^sub>1. valid_happ_seq M\<^sub>0 (takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs) M\<^sub>1 
                    \<and> valid_happ_seq M\<^sub>1 (dropWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs) M\<^sub>n"
        using valid_happ_seq_app_iff[where hs\<^sub>1="takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs" 
                                       and hs\<^sub>2="dropWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs"] 
        by auto
      then obtain M\<^sub>1 where "valid_happ_seq M\<^sub>0 (dropWhile (le t\<^sub>m\<^sub>i\<^sub>n) (takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs)) M\<^sub>1"
                       and "valid_happ_seq M\<^sub>1 (dropWhile (leq t\<^sub>m\<^sub>i\<^sub>n) (takeWhile (leq t\<^sub>m\<^sub>a\<^sub>x) hs)) M\<^sub>n"
        using \<open>dropWhile (le t\<^sub>m\<^sub>i\<^sub>n) (takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs) = takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs\<close> 
              \<open>takeWhile (leq t\<^sub>m\<^sub>a\<^sub>x) hs = hs\<close>[symmetric] 
        by auto

      have "invs_of_plan_at t\<^sub>m\<^sub>i\<^sub>n \<pi>s = {}"
        unfolding invs_of_plan_at_def using \<open>\<forall>(t\<^sub>\<pi>,\<pi>) \<in> set \<pi>s. t\<^sub>m\<^sub>i\<^sub>n \<le> t\<^sub>\<pi>\<close> 
        by (auto simp: durative_acts_def)
      then have "valid_state_seq M\<^sub>0 [t\<^sub>m\<^sub>i\<^sub>n] \<pi>s M\<^sub>1"
        using \<open>valid_happ_seq M\<^sub>0 (dropWhile (le t\<^sub>m\<^sub>i\<^sub>n) (takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs)) M\<^sub>1\<close>
              \<open>dropWhile (le t\<^sub>m\<^sub>i\<^sub>n) (takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs) = [(t\<^sub>m\<^sub>i\<^sub>n,as\<^sub>m\<^sub>i\<^sub>n)]\<close> 
              \<open>set as\<^sub>m\<^sub>i\<^sub>n = acts_of_plan_at t\<^sub>m\<^sub>i\<^sub>n \<pi>s\<close>
        by (auto simp add: pairwise_def)

      have "t\<^sub>m\<^sub>i\<^sub>n = t\<^sub>m\<^sub>a\<^sub>x \<or> t\<^sub>m\<^sub>i\<^sub>n < t\<^sub>m\<^sub>a\<^sub>x"
        using \<open>t\<^sub>m\<^sub>i\<^sub>n \<le> t\<^sub>m\<^sub>a\<^sub>x\<close> by auto
      then show "valid_state_seq M\<^sub>0 htps \<pi>s M\<^sub>n"
      proof
        assume "t\<^sub>m\<^sub>i\<^sub>n = t\<^sub>m\<^sub>a\<^sub>x"
        then have "valid_happ_seq M\<^sub>0 hs M\<^sub>1"
          using \<open>dropWhile (le t\<^sub>m\<^sub>i\<^sub>n) (takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs) = takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs\<close> 
                \<open>valid_happ_seq M\<^sub>0 (dropWhile (le t\<^sub>m\<^sub>i\<^sub>n) (takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs)) M\<^sub>1\<close>
          by (simp add: \<open>takeWhile (leq t\<^sub>m\<^sub>a\<^sub>x) hs = hs\<close>)
        then have "M\<^sub>1 = M\<^sub>n"
          using valid_happ_seq_state_unique[OF \<open>valid_happ_seq M\<^sub>0 hs M\<^sub>n\<close> \<open>valid_happ_seq M\<^sub>0 hs M\<^sub>1\<close>]
          by auto
        have "htps = [t\<^sub>m\<^sub>i\<^sub>n]"
          using \<open>htps \<noteq> []\<close> \<open>strict_sorted htps\<close> \<open>t\<^sub>m\<^sub>i\<^sub>n = hd htps\<close> \<open>t\<^sub>m\<^sub>a\<^sub>x = last htps\<close> \<open>t\<^sub>m\<^sub>i\<^sub>n = t\<^sub>m\<^sub>a\<^sub>x\<close>
          by (induction htps) (auto split: if_splits)
        then show ?thesis
          using \<open>valid_state_seq M\<^sub>0 [t\<^sub>m\<^sub>i\<^sub>n] \<pi>s M\<^sub>1\<close> \<open>M\<^sub>1 = M\<^sub>n\<close> by auto
      next
        assume "t\<^sub>m\<^sub>i\<^sub>n < t\<^sub>m\<^sub>a\<^sub>x"
        then have "\<exists>htps'. htps = [] @ t\<^sub>m\<^sub>i\<^sub>n # htps' @ t\<^sub>m\<^sub>a\<^sub>x # []"
          using \<open>htps \<noteq> []\<close> \<open>t\<^sub>m\<^sub>i\<^sub>n = hd htps\<close> \<open>t\<^sub>m\<^sub>a\<^sub>x = last htps\<close>
          apply (induction htps)
          apply (auto split: if_splits)
          apply (metis append_butlast_last_id)
          done
        then obtain htps' where "htps = [] @ t\<^sub>m\<^sub>i\<^sub>n # htps' @ t\<^sub>m\<^sub>a\<^sub>x # []"
          by auto
        then have "htps_seq \<pi>s ([] @ t\<^sub>m\<^sub>i\<^sub>n # htps' @ t\<^sub>m\<^sub>a\<^sub>x # [])"
          using assms by auto
        then have "valid_state_seq M\<^sub>1 (htps' @ [t\<^sub>m\<^sub>a\<^sub>x]) \<pi>s M\<^sub>n"
          using assms \<open>valid_happ_seq M\<^sub>1 (dropWhile (leq t\<^sub>m\<^sub>i\<^sub>n) (takeWhile (leq t\<^sub>m\<^sub>a\<^sub>x) hs)) M\<^sub>n\<close>
                valid_happ_seq_valid_state_seq_i_to_j_aux
                  [OF \<open>htps_seq \<pi>s ([] @ t\<^sub>m\<^sub>i\<^sub>n # htps' @ t\<^sub>m\<^sub>a\<^sub>x # [])\<close>]
          by blast
        then show ?thesis
          using \<open>valid_state_seq M\<^sub>0 [t\<^sub>m\<^sub>i\<^sub>n] \<pi>s M\<^sub>1\<close> \<open>htps = [] @ t\<^sub>m\<^sub>i\<^sub>n # htps' @ t\<^sub>m\<^sub>a\<^sub>x # []\<close>
               valid_state_seq_app_iff[where ts\<^sub>1="[t\<^sub>m\<^sub>i\<^sub>n]" and ts\<^sub>2="htps' @ [t\<^sub>m\<^sub>a\<^sub>x]"]
          by auto
      qed
    next
      assume "valid_state_seq M\<^sub>0 htps \<pi>s M\<^sub>n"
      text \<open>Remove first happening from the happening sequence.\<close>
      then obtain M\<^sub>1 where "valid_state_seq M\<^sub>0 [t\<^sub>m\<^sub>i\<^sub>n] \<pi>s M\<^sub>1" and "valid_state_seq M\<^sub>1 (tl htps) \<pi>s M\<^sub>n"
        using \<open>t\<^sub>m\<^sub>i\<^sub>n = hd htps\<close> valid_state_seq_app_iff[where ts\<^sub>1="[t\<^sub>m\<^sub>i\<^sub>n]" and ts\<^sub>2="tl htps"]
        by (auto simp: \<open>htps \<noteq> []\<close>)
      then have "valid_happ_seq M\<^sub>0 (dropWhile (le t\<^sub>m\<^sub>i\<^sub>n) (takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs)) M\<^sub>1"
        using \<open>valid_state_seq M\<^sub>0 [t\<^sub>m\<^sub>i\<^sub>n] \<pi>s M\<^sub>1\<close> 
              \<open>dropWhile (le t\<^sub>m\<^sub>i\<^sub>n) (takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs) = [(t\<^sub>m\<^sub>i\<^sub>n,as\<^sub>m\<^sub>i\<^sub>n)]\<close> 
              \<open>set as\<^sub>m\<^sub>i\<^sub>n = acts_of_plan_at t\<^sub>m\<^sub>i\<^sub>n \<pi>s\<close>
        by (auto simp: Let_def pairwise_def)

      have "t\<^sub>m\<^sub>i\<^sub>n = t\<^sub>m\<^sub>a\<^sub>x \<or> t\<^sub>m\<^sub>i\<^sub>n < t\<^sub>m\<^sub>a\<^sub>x"
        using \<open>t\<^sub>m\<^sub>i\<^sub>n \<le> t\<^sub>m\<^sub>a\<^sub>x\<close> by auto
      then show "valid_happ_seq M\<^sub>0 hs M\<^sub>n"
      proof
        assume "t\<^sub>m\<^sub>i\<^sub>n = t\<^sub>m\<^sub>a\<^sub>x"
        have "htps = [t\<^sub>m\<^sub>i\<^sub>n]"
          using \<open>htps \<noteq> []\<close> \<open>strict_sorted htps\<close> \<open>t\<^sub>m\<^sub>i\<^sub>n = hd htps\<close> \<open>t\<^sub>m\<^sub>a\<^sub>x = last htps\<close> \<open>t\<^sub>m\<^sub>i\<^sub>n = t\<^sub>m\<^sub>a\<^sub>x\<close>
          by (induction htps) (auto split: if_splits)
        then have "M\<^sub>1 = M\<^sub>n"
          using \<open>valid_state_seq M\<^sub>0 [t\<^sub>m\<^sub>i\<^sub>n] \<pi>s M\<^sub>1\<close> 
                valid_state_seq_state_unique [OF \<open>valid_state_seq M\<^sub>0 htps \<pi>s M\<^sub>n\<close>]
          by (auto simp add: \<open>takeWhile (leq t\<^sub>m\<^sub>a\<^sub>x) hs = hs\<close>)
        then show ?thesis
          using \<open>dropWhile (le t\<^sub>m\<^sub>i\<^sub>n) (takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs) = takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs\<close>
                \<open>valid_happ_seq M\<^sub>0 (dropWhile (le t\<^sub>m\<^sub>i\<^sub>n) (takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs)) M\<^sub>1\<close> 
                \<open>t\<^sub>m\<^sub>i\<^sub>n = t\<^sub>m\<^sub>a\<^sub>x\<close>
          by (simp add: \<open>takeWhile (leq t\<^sub>m\<^sub>a\<^sub>x) hs = hs\<close>)
      next
        assume "t\<^sub>m\<^sub>i\<^sub>n < t\<^sub>m\<^sub>a\<^sub>x"
        then have "\<exists>htps'. htps = [] @ t\<^sub>m\<^sub>i\<^sub>n # htps' @ t\<^sub>m\<^sub>a\<^sub>x # []"
          using \<open>htps \<noteq> []\<close> \<open>t\<^sub>m\<^sub>i\<^sub>n = hd htps\<close> \<open>t\<^sub>m\<^sub>a\<^sub>x = last htps\<close>
          apply (induction htps)
          apply (auto split: if_splits)
          apply (metis append_butlast_last_id)
          done
        then obtain htps' where "htps = [] @ t\<^sub>m\<^sub>i\<^sub>n # htps' @ t\<^sub>m\<^sub>a\<^sub>x # []"
          by auto
        then have "htps_seq \<pi>s ([] @ t\<^sub>m\<^sub>i\<^sub>n # htps' @ t\<^sub>m\<^sub>a\<^sub>x # [])"
          using assms by auto
        then have "valid_happ_seq M\<^sub>1 (dropWhile (leq t\<^sub>m\<^sub>i\<^sub>n) (takeWhile (leq t\<^sub>m\<^sub>a\<^sub>x) hs)) M\<^sub>n"
          using assms \<open>valid_state_seq M\<^sub>1 (tl htps) \<pi>s M\<^sub>n\<close> \<open>htps = [] @ t\<^sub>m\<^sub>i\<^sub>n # htps' @ [t\<^sub>m\<^sub>a\<^sub>x]\<close>
                valid_happ_seq_valid_state_seq_i_to_j_aux
                  [OF \<open>htps_seq \<pi>s ([] @ t\<^sub>m\<^sub>i\<^sub>n # htps' @ t\<^sub>m\<^sub>a\<^sub>x # [])\<close>]
          by fastforce
        then show ?thesis
          using valid_happ_seq_app_iff[where hs\<^sub>1="takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs" 
                                     and hs\<^sub>2="dropWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs"]
              \<open>valid_happ_seq M\<^sub>0 (dropWhile (le t\<^sub>m\<^sub>i\<^sub>n) (takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs)) M\<^sub>1\<close>
              \<open>takeWhile (leq t\<^sub>m\<^sub>a\<^sub>x) hs = hs\<close>
              \<open>dropWhile (le t\<^sub>m\<^sub>i\<^sub>n) (takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs) = takeWhile (leq t\<^sub>m\<^sub>i\<^sub>n) hs\<close>
          by auto
      qed
    qed
  qed

  lemma (in wf_ast_problem) plan_happ_path_iff_valid_state_seq:
    assumes "wf_plan \<pi>s" and "htps_seq \<pi>s htps"
    shows "plan_happ_path M \<pi>s M' \<longleftrightarrow> valid_state_seq M htps \<pi>s M'"
    unfolding plan_happ_path_def
    using assms ind_happ_seq_exists valid_happ_seq_iff_valid_state_seq by blast

  lemmas plan_happ_path_iff_valid_state_seq_iff'
    = wf_ast_problem.plan_happ_path_iff_valid_state_seq[of P, OF wf_ast_problem.intro]

  lemma "strict_sorted xs \<Longrightarrow> strict_sorted ys \<Longrightarrow> set xs = set ys \<Longrightarrow> xs = ys"
    by (simp add: strict_sorted_iff sorted_distinct_set_unique)


  text \<open>Proof that a sequence of happening time points is unique for every plan\<close>
  lemma htps_seq_unique:
    assumes "htps_seq \<pi>s htps\<^sub>1"
        and "htps_seq \<pi>s htps\<^sub>2"
    shows "htps\<^sub>1 = htps\<^sub>2"
  proof -
    have "set htps\<^sub>1 = set htps\<^sub>2"
      using assms unfolding htps_seq_def by auto
    then show ?thesis
      using assms unfolding htps_seq_def by (simp add: strict_sorted_iff sorted_distinct_set_unique)
  qed
  

  lemma valid_plan_from2_iff:
    assumes "wf_problem"
    shows "valid_plan_from2 I \<pi>s \<longleftrightarrow> valid_plan_from I \<pi>s"
    unfolding valid_plan_from_def valid_plan_from2_def
    using htps_seq_exists htps_seq_unique
          plan_happ_path_iff_valid_state_seq_iff'[OF assms] 
    by blast

  lemma 
    assumes "wf_problem"
    shows "valid_plan2 \<pi>s \<longleftrightarrow> valid_plan \<pi>s"
    unfolding valid_plan_def valid_plan2_def 
    using valid_plan_from2_iff[OF assms] by blast

end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>

end \<comment> \<open>Theory\<close>
