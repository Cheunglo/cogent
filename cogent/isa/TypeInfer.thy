theory TypeInfer
  imports Cogent
begin

lemma canonical_trans_le_add1:
  fixes x y z :: "'a :: canonically_ordered_monoid_add"
  shows "x + y \<le> z \<Longrightarrow> x \<le> z"
  by (meson le_iff_add order_trans)

lemma canonical_trans_le_add2:
  fixes x y z :: "'a :: canonically_ordered_monoid_add"
  shows "x + y \<le> z \<Longrightarrow> y \<le> z"
  by (metis add.commute canonical_trans_le_add1)

chapter \<open> Cogent lemmas \<close>
(* TODO move *)

lemma case_variant_state_repeat[simp]:
  "case_variant_state x x tk = x"
  by (clarsimp split: variant_state.splits)

lemma case_record_state_repeat[simp]:
  "case_record_state x x tk = x"
  by (clarsimp split: record_state.splits)

subsection \<open> Weakening Lemmas \<close>

lemma weakening_comp_trans:
  "weakening_comp K a b \<Longrightarrow> weakening_comp K b c \<Longrightarrow> weakening_comp K a c"
  by (force simp add: weakening_comp.simps)

lemma weakening_trans:
  "K \<turnstile> xs \<leadsto>w ys \<Longrightarrow> K \<turnstile> ys \<leadsto>w zs \<Longrightarrow> K \<turnstile> xs \<leadsto>w zs"
  by (fastforce simp add: weakening_conv_all_nth weakening_comp.simps)

lemma consume_weakening:
  "\<lbrakk>K \<turnstile> xs \<leadsto>w ys; K \<turnstile> ys consumed\<rbrakk> \<Longrightarrow> K \<turnstile> xs consumed"
  by (metis is_consumed_def weakening_length weakening_trans)

subsection \<open> Drop-Share Equivalence \<close>

lemma sigil_kind_drop_impl_share:
  "D \<in> sigil_kind s \<Longrightarrow> S \<in> sigil_kind s"
  using sigil_kind.elims by auto

lemma sigil_kind_share_impl_drop:
  "S \<in> sigil_kind s \<Longrightarrow> D \<in> sigil_kind s"
  using sigil_kind.elims by auto

lemma sigil_kind_drop_iff_share:
  "D \<in> sigil_kind s \<longleftrightarrow> S \<in> sigil_kind s"
  using sigil_kind.elims by auto


definition well_kinded :: "kind \<Rightarrow> bool" where
  "well_kinded k \<equiv> D \<in> k \<longleftrightarrow> S \<in> k"

definition well_kinded_all :: "kind list \<Rightarrow> bool" where
  "well_kinded_all \<equiv> list_all well_kinded"

lemmas well_kinded_all_length =
  list_all_length[where P=\<open>well_kinded\<close>, simplified well_kinded_all_def[symmetric]]

lemmas well_kinded_all_simps[simp] =
  list_all_simps(1-2)[where P=\<open>well_kinded\<close>, simplified well_kinded_all_def[symmetric]]

lemma well_kinded_all_drop_is_share_nthD:
  "well_kinded_all K \<Longrightarrow> i < length K \<Longrightarrow> D \<in> K ! i \<longleftrightarrow> S \<in> K ! i"
  by (simp add: well_kinded_all_length well_kinded_def)

lemma drop_kind_iff_share_kind:
  assumes
    "well_kinded_all K"
    "K \<turnstile> t wellformed"
  shows
    "D \<in> kinding_fn K t \<longleftrightarrow> S \<in> kinding_fn K t"
  using assms
  by (induct t)
    (fastforce simp add: in_set_conv_nth list_all_length
      all_set_conv_all_nth sigil_kind_drop_iff_share prod_eq_iff
      kinding_fn_all_def kinding_fn_all_variant_def kinding_fn_all_record_def
      dest: well_kinded_all_drop_is_share_nthD
      split: record_state.splits variant_state.splits)+

lemma share_kind_iff_drop_kind:
  assumes
    "well_kinded_all K"
    "K \<turnstile> t wellformed"
  shows
    "S \<in> kinding_fn K t \<longleftrightarrow> D \<in> kinding_fn K t"
  using assms
  by (induct t)
    (fastforce simp add: in_set_conv_nth list_all_length
      all_set_conv_all_nth sigil_kind_drop_iff_share prod_eq_iff
      kinding_fn_all_def kinding_fn_all_variant_def kinding_fn_all_record_def
      dest: well_kinded_all_drop_is_share_nthD
      split: record_state.splits variant_state.splits)+


subsection \<open> Weakening and Splitting Interchange Lemmas \<close>

fun wksplit_to_splitwks_comp :: "kind list \<Rightarrow> bool \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> type option" where
  "wksplit_to_splitwks_comp K True (Some _) (Some _) (Some t) = Some t"
| "wksplit_to_splitwks_comp K _ None _ _ = None"
| "wksplit_to_splitwks_comp K _ (Some t) None     None     = Some t"
| "wksplit_to_splitwks_comp K _ (Some t) (Some _) None     = (if S \<in> kinding_fn K t then Some t else None)"
| "wksplit_to_splitwks_comp K _ (Some t) (Some _) (Some _) = Some t"

definition wksplit_to_splitwks :: "kind list \<Rightarrow> type option list \<Rightarrow> type option list \<Rightarrow> type option list \<Rightarrow> type option list" where
  "wksplit_to_splitwks K xs ys zs \<equiv> map (\<lambda>(d,g,g'). wksplit_to_splitwks_comp K False d g g') (zip xs (zip ys zs))"

lemma wksplit_to_splitwks_length[simp]:
  "length (wksplit_to_splitwks K xs ys zs) = min (length xs) (min (length ys) (length zs))"
  by (simp add: wksplit_to_splitwks_def)

lemma wksplit_to_splitwks_nthD[dest]:
  assumes
    "i < length xs"
    "i < length ys"
    "i < length zs"
  shows
    "wksplit_to_splitwks K xs ys zs ! i = wksplit_to_splitwks_comp K False (xs ! i) (ys ! i) (zs ! i)"
  using assms
  by (simp add: wksplit_to_splitwks_def)

lemma wksplit_to_splitwks_comp_correct:
  assumes
    "well_kinded_all K"
    "weakening_comp K d g"
    "split_comp K g g1 g2"
  shows
    "split_comp K d (wksplit_to_splitwks_comp K False d g g1) (wksplit_to_splitwks_comp K False d g g2)"
    "weakening_comp K (wksplit_to_splitwks_comp K False d g g1) g1"
    "weakening_comp K (wksplit_to_splitwks_comp K False d g g2) g2"
  using assms
  by (cases d; cases g; cases g1; cases g2; clarsimp simp add: split_comp_simps drop_kind_iff_share_kind)+

lemma wksplit_to_splitwks:
  assumes
    "well_kinded_all K"
    "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    "K \<turnstile> \<Delta> \<leadsto>w \<Gamma>"
  shows
    "K \<turnstile> \<Delta> \<leadsto> wksplit_to_splitwks K \<Delta> \<Gamma> \<Gamma>1 | wksplit_to_splitwks K \<Delta> \<Gamma> \<Gamma>2"
    "K \<turnstile> wksplit_to_splitwks K \<Delta> \<Gamma> \<Gamma>1 \<leadsto>w \<Gamma>1"
    "K \<turnstile> wksplit_to_splitwks K \<Delta> \<Gamma> \<Gamma>2 \<leadsto>w \<Gamma>2"
  using assms
  by (fastforce intro: wksplit_to_splitwks_comp_correct simp add: weakening_conv_all_nth split_conv_all_nth wksplit_to_splitwks_nthD)+

subsection \<open> Weakening and Split-bang Interchange Lemmas \<close>




fun wksplitb_to_splitbwks :: "kind list \<Rightarrow> nat set \<Rightarrow> type option list \<Rightarrow> type option list \<Rightarrow> type option list \<Rightarrow> type option list" where
  "wksplitb_to_splitbwks K is [] [] [] = []"
| "wksplitb_to_splitbwks K ws (x # xs) (y # ys) (z # zs) =
    (wksplit_to_splitwks_comp K (0 \<in> ws) x y z) # (wksplitb_to_splitbwks K (pred ` Set.remove 0 ws) xs ys zs)"
| "wksplitb_to_splitbwks a b (v # va) [] e = []"
| "wksplitb_to_splitbwks a b (v # va) d [] = []"
| "wksplitb_to_splitbwks a b [] (v # va) e = []"
| "wksplitb_to_splitbwks a b [] [] (v # va) = []"

lemma wksplitb_to_splitbwks_length[simp]:
  "length (wksplitb_to_splitbwks K ws xs ys zs) = min (length xs) (min (length ys) (length zs))"
  by (induct rule: wksplitb_to_splitbwks.induct) simp+

lemma wksplitb_to_splitbwks_nthD[dest]:
  assumes
    "i < length xs"
    "i < length ys"
    "i < length zs"
  shows
    "wksplitb_to_splitbwks K ws xs ys zs ! i = wksplit_to_splitwks_comp K (i \<in> ws) (xs ! i) (ys ! i) (zs ! i)"
  using assms
  by (induct xs ys zs arbitrary: i ws rule: list_induct3')
      (force simp add: less_Suc_eq_0_disj Suc_mem_image_pred_remove[symmetric])+

lemma wksplitb_to_splitbwks_eq_nth:
  "(wksplitb_to_splitbwks K ws xs ys zs = as)
    \<longleftrightarrow> (length as = min (length xs) (min (length ys) (length zs)) \<and>
        (\<forall>i. i<length xs \<longrightarrow> i<length ys \<longrightarrow> i<length zs \<longrightarrow> wksplitb_to_splitbwks K ws xs ys zs ! i = as ! i))"
  by (safe, simp,
      (induct xs ys zs arbitrary: ws as rule: list_induct3',
        (clarsimp simp add: All_less_Suc2 length_Suc_conv)+))

lemma wksplitb_to_splitbwks_comp_correct:
  assumes
    "well_kinded_all K"
    "weakening_comp K d g"
    "split_bang_comp K i g g1 g2"
  shows
    "split_bang_comp K i d (wksplit_to_splitwks_comp K i d g g1) (wksplit_to_splitwks_comp K i d g g2)"
    "weakening_comp K (wksplit_to_splitwks_comp K i d g g1) g1"
    "weakening_comp K (wksplit_to_splitwks_comp K i d g g2) g2"
  using assms
    apply -
    apply (cases i)
     apply (clarsimp simp add: split_bang_comp_simps weakening_comp.simps)
    apply (clarsimp simp add: split_bang_comp_simps wksplit_to_splitwks_comp_correct)
   apply (cases i)
    apply (clarsimp simp add: split_bang_comp_simps weakening_comp.simps)
   apply (clarsimp simp add: split_bang_comp_simps wksplit_to_splitwks_comp_correct)
  apply (cases i)
   apply (clarsimp simp add: split_bang_comp_simps weakening_comp.simps)
  apply (clarsimp simp add: split_bang_comp_simps wksplit_to_splitwks_comp_correct)
  done

lemma wksplitb_to_splitbwks:
  assumes
    "well_kinded_all K"
    "K \<turnstile> \<Delta> \<leadsto>w \<Gamma>"
    "K, is \<turnstile> \<Gamma> \<leadsto>b \<Gamma>1 | \<Gamma>2"
  shows
    "K, is \<turnstile> \<Delta> \<leadsto>b wksplitb_to_splitbwks K is \<Delta> \<Gamma> \<Gamma>1 | wksplitb_to_splitbwks K is \<Delta> \<Gamma> \<Gamma>2"
    "K \<turnstile> wksplitb_to_splitbwks K is \<Delta> \<Gamma> \<Gamma>1 \<leadsto>w \<Gamma>1"
    "K \<turnstile> wksplitb_to_splitbwks K is \<Delta> \<Gamma> \<Gamma>2 \<leadsto>w \<Gamma>2"
  using assms
  by (fastforce simp add: weakening_conv_all_nth split_bang_conv_all_nth
      wksplitb_to_splitbwks_nthD intro: wksplitb_to_splitbwks_comp_correct)+


section \<open> Weakening Typing Context \<close>

lemma typing_weaken_context:
  assumes "well_kinded_all K"
  shows "\<Xi>, K, \<Gamma> \<turnstile>  e  : t  \<Longrightarrow> K \<turnstile> \<Gamma>' \<leadsto>w \<Gamma> \<Longrightarrow> \<Xi>, K, \<Gamma>' \<turnstile>  e  : t"
    and "\<Xi>, K, \<Gamma> \<turnstile>* es : ts \<Longrightarrow> K \<turnstile> \<Gamma>' \<leadsto>w \<Gamma> \<Longrightarrow> \<Xi>, K, \<Gamma>' \<turnstile>* es : ts"
  using assms
proof (induct arbitrary: \<Gamma>' and \<Gamma>' rule: typing_typing_all.inducts)
  case typing_var then show ?case
    by (bestsimp
        intro!: typing_typing_all.intros
        simp add: weakening_conv_all_nth Cogent.empty_def
        dest: weakening_comp_trans)
next
  case (typing_app K \<Gamma> \<Gamma>1 \<Gamma>2)
  moreover then obtain \<Gamma>'1 \<Gamma>'2
    where
      "K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>'1 | \<Gamma>'2"
      "K \<turnstile> \<Gamma>'1 \<leadsto>w \<Gamma>1"
      "K \<turnstile> \<Gamma>'2 \<leadsto>w \<Gamma>2"
    using typing_app 
    by (meson wksplit_to_splitwks)
  ultimately show ?case
    by (force intro!: typing_typing_all.intros)
next
  case (typing_tuple K \<Gamma> \<Gamma>1 \<Gamma>2)
  moreover then obtain \<Gamma>'1 \<Gamma>'2
    where
      "K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>'1 | \<Gamma>'2"
      "K \<turnstile> \<Gamma>'1 \<leadsto>w \<Gamma>1"
      "K \<turnstile> \<Gamma>'2 \<leadsto>w \<Gamma>2"
    by (meson wksplit_to_splitwks)
  ultimately show ?case
    by (force intro!: typing_typing_all.intros)
next
  case (typing_split K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t u y t')
  moreover have
    "K \<turnstile> t wellformed"
    "K \<turnstile> u wellformed"
    using typing_split
    by (force dest: typing_to_wellformed)+
  moreover then obtain \<Gamma>'1 \<Gamma>'2
    where
      "K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>'1 | \<Gamma>'2"
      "K \<turnstile> \<Gamma>'1 \<leadsto>w \<Gamma>1"
      "K \<turnstile> Some t # Some u # \<Gamma>'2 \<leadsto>w Some t # Some u # \<Gamma>2"
    using typing_split
    by (meson wksplit_to_splitwks weakening_Cons weakening_comp.simps)
  ultimately show ?case
    by (force intro!: typing_typing_all.intros)
next
  case (typing_let K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t y u)
  moreover have
    "K \<turnstile> t wellformed"
    using typing_let
    by (force dest: typing_to_wellformed)+
  moreover then obtain \<Gamma>'1 \<Gamma>'2
    where
      "K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>'1 | \<Gamma>'2"
      "K \<turnstile> \<Gamma>'1 \<leadsto>w \<Gamma>1"
      "K \<turnstile> Some t # \<Gamma>'2 \<leadsto>w Some t # \<Gamma>2"
    using typing_let
    by (meson wksplit_to_splitwks weakening_Cons weakening_comp.simps)
  ultimately show ?case
    by (force intro!: typing_typing_all.intros)
next
  case (typing_letb K "is" \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t y u k)
  moreover have
    "K \<turnstile> t wellformed"
    using typing_letb
    by (force dest: typing_to_wellformed)+
  moreover then obtain \<Gamma>'1 \<Gamma>'2
    where
      "K, is \<turnstile> \<Gamma>' \<leadsto>b \<Gamma>'1 | \<Gamma>'2"
      "K \<turnstile> \<Gamma>'1 \<leadsto>w \<Gamma>1"
      "K \<turnstile> Some t # \<Gamma>'2 \<leadsto>w Some t # \<Gamma>2"
    using typing_letb
    by (meson wksplitb_to_splitbwks weakening_Cons weakening_comp.simps)
  ultimately show ?case
    by (force intro!: typing_typing_all.intros)
next
  case (typing_case K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x ts tag t a u b)
  moreover have
    "K \<turnstile> TSum ts wellformed"
    using typing_case
    by (force dest: typing_to_wellformed)+
  moreover then have
    "K \<turnstile> t wellformed"
    "K \<turnstile> TSum (tagged_list_update tag (t, Checked) ts) wellformed"
    using typing_case
    by (force dest: type_wellformed_fstsnd_triple_elem simp add: type_wellformed_fst_snd_updateI
        type_wellformed_fstsnd_triple_elem)+
  moreover then obtain \<Gamma>'1 \<Gamma>'2
    where
      "K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>'1 | \<Gamma>'2"
      "K \<turnstile> \<Gamma>'1 \<leadsto>w \<Gamma>1"
      "K \<turnstile> Some t # \<Gamma>'2 \<leadsto>w Some t # \<Gamma>2"
      "K \<turnstile> Some (TSum (tagged_list_update tag (t, Checked) ts)) # \<Gamma>'2 \<leadsto>w Some (TSum (tagged_list_update tag (t, Checked) ts)) # \<Gamma>2"
    using typing_case
    by (meson wksplit_to_splitwks weakening_Cons weakening_comp.simps)
  ultimately show ?case
    by (force intro!: typing_typing_all.intros)
next
  case (typing_if K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x a t b)
    moreover then obtain \<Gamma>'1 \<Gamma>'2
    where
      "K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>'1 | \<Gamma>'2"
      "K \<turnstile> \<Gamma>'1 \<leadsto>w \<Gamma>1"
      "K \<turnstile> \<Gamma>'2 \<leadsto>w \<Gamma>2"
      by (meson wksplit_to_splitwks)
  ultimately show ?case
    by (force intro!: typing_typing_all.intros)
next
  case (typing_take K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f n t k taken e' u)
  moreover have
    "K \<turnstile> TRecord ts s wellformed"
    using typing_take
    by (force dest: typing_to_wellformed)+
  moreover then have t_wellformed:
    "K \<turnstile> t wellformed"
    using typing_take
    by (force dest: type_wellformed_fstsnd_triple_nth)
  ultimately have
    "K \<turnstile> TRecord (ts[f := (n, t, taken)]) s wellformed"
    using typing_take
    by (force intro: type_wellformed_fstsnd_list_updI simp add: map_fst_update)
  then obtain \<Gamma>'1 \<Gamma>'2
    where
      "K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>'1 | \<Gamma>'2"
      "K \<turnstile> \<Gamma>'1 \<leadsto>w \<Gamma>1"
      "K \<turnstile> Some t # Some (TRecord (ts[f := (n, t, taken)]) s) # \<Gamma>'2 \<leadsto>w Some t # Some (TRecord (ts[f := (n, t, taken)]) s) # \<Gamma>2"
    using typing_take t_wellformed
    by (meson wksplit_to_splitwks weakening_Cons weakening_comp.simps)
    then show ?case
      using typing_take
    by (force intro!: typing_typing_all.intros)
next
  case (typing_put K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f n t taken k e')
  moreover then obtain \<Gamma>'1 \<Gamma>'2
    where
      "K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>'1 | \<Gamma>'2"
      "K \<turnstile> \<Gamma>'1 \<leadsto>w \<Gamma>1"
      "K \<turnstile> \<Gamma>'2 \<leadsto>w \<Gamma>2"
    by (meson wksplit_to_splitwks weakening_Cons weakening_comp.simps)
  ultimately show ?case
    by (force intro!: typing_typing_all.intros)
next
  case (typing_all_cons K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e t es ts)
  moreover then obtain \<Gamma>'1 \<Gamma>'2
    where
      "K \<turnstile> \<Gamma>' \<leadsto> \<Gamma>'1 | \<Gamma>'2"
      "K \<turnstile> \<Gamma>'1 \<leadsto>w \<Gamma>1"
      "K \<turnstile> \<Gamma>'2 \<leadsto>w \<Gamma>2"
    by (meson wksplit_to_splitwks)
  ultimately show ?case
    by (force intro!: typing_typing_all.intros)
qed (fastforce intro!: typing_typing_all.intros dest: consume_weakening)+

chapter \<open> Typing Inference \<close>

(* main theory *)

definition countPlus :: "('a :: plus) list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "\<oplus>" 75) where
  "xs \<oplus> ys \<equiv> map2 (+) xs ys"

lemma countPlus_simps[simp]:
  "countPlus [] [] = []"
  "countPlus (x # xs) (y # ys) = (x+y) # (xs \<oplus> ys)"
  "countPlus [] (y # ys) = []"
  "countPlus (x # xs) [] = []"
  by (simp add: countPlus_def)+

lemma countPlus_length[simp]:
  "length (C1 \<oplus> C2) = min (length C1) (length C2)"
  by (simp add: countPlus_def)

lemma countPlus_eq_Nil[simp]:
  "(C1 \<oplus> C2 = []) \<longleftrightarrow> (C1 = []) \<or> (C2 = [])"
  by (metis countPlus_length length_greater_0_conv min_less_iff_conj)
lemma countPlus_eq_Nil2[simp]:
  "([] = C1 \<oplus> C2) \<longleftrightarrow> (C1 = []) \<or> (C2 = [])"
  by (metis countPlus_length length_greater_0_conv min_less_iff_conj)

lemma countPlus_eq_Cons:
  "(C1 \<oplus> C2 = x # xs) \<longleftrightarrow> (\<exists>y ys z zs. C1 = y # ys \<and> C2 = z # zs \<and> x = y + z \<and> xs = ys \<oplus> zs)"
  by (case_tac C1; case_tac C2; force)
lemma countPlus_eq_Cons2:
  "(x # xs = C1 \<oplus> C2) \<longleftrightarrow> (\<exists>y ys z zs. C1 = y # ys \<and> C2 = z # zs \<and> x = y + z \<and> xs = ys \<oplus> zs)"
  by (case_tac C1; case_tac C2; force)

lemma countPlus_nth[simp]:
  "i < length C1 \<Longrightarrow> i < length C2 \<Longrightarrow> (C1 \<oplus> C2) ! i = C1 ! i + C2 ! i"
  by (simp add: countPlus_def)


definition countMax :: "('a :: sup) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "countMax xs ys \<equiv> map2 sup xs ys"

lemma countMax_simps[simp]:
  "countMax [] [] = []"
  "countMax (x # xs) (y # ys) = (sup x y) # (countMax xs ys)"
  "countMax [] (y # ys) = []"
  "countMax (x # xs) [] = []"
  by (simp add: countMax_def)+

lemma countMax_length[simp]:
  "length (countMax C1 C2) = min (length C1) (length C2)"
  by (simp add: countMax_def)

lemma countMax_eq_Nil[simp]:
  "(countMax C1 C2 = []) \<longleftrightarrow> (C1 = []) \<or> (C2 = [])"
  by (metis countMax_length length_greater_0_conv min_less_iff_conj)
lemma countMax_eq_Nil2[simp]:
  "([] = countMax C1 C2) \<longleftrightarrow> (C1 = []) \<or> (C2 = [])"
  by (metis countMax_length length_greater_0_conv min_less_iff_conj)

lemma countMax_eq_Cons:
  "(countMax C1 C2 = x # xs) \<longleftrightarrow> (\<exists>y ys z zs. C1 = y # ys \<and> C2 = z # zs \<and> x = sup y z \<and> xs = countMax ys zs)"
  by (case_tac C1; case_tac C2; force)
lemma countMax_eq_Cons2:
  "(x # xs = countMax C1 C2) \<longleftrightarrow> (\<exists>y ys z zs. C1 = y # ys \<and> C2 = z # zs \<and> x = sup y z \<and> xs = countMax ys zs)"
  by (case_tac C1; case_tac C2; force)

lemma countMax_nth[simp]:
  "i < length C1 \<Longrightarrow> i < length C2 \<Longrightarrow> countMax C1 C2 ! i = sup (C1 ! i) (C2 ! i)"
  by (induct C1 arbitrary: C2 i)
    (force simp add: less_Suc_eq_0_disj Suc_less_eq2 neq_Nil_conv length_Suc_conv)+

inductive ensure_use_bang :: "nat set \<Rightarrow> ('a :: {one,order}) list \<Rightarrow> bool" where
  ensure_use_bang_nil: "ensure_use_bang N []"
| ensure_use_bang_cons:
  "0 \<in> N \<longrightarrow> 1 \<le> x \<Longrightarrow> ensure_use_bang (pred ` Set.remove 0 N) xs \<Longrightarrow> ensure_use_bang N (x # xs)"

lemma ensure_use_bang_simps[simp]:
  "ensure_use_bang N [] = True"
  "ensure_use_bang N (x # xs) = ((0 \<in> N \<longrightarrow> 1 \<le> x) \<and> ensure_use_bang (pred ` Set.remove 0 N) xs)"
  by (blast intro: ensure_use_bang.intros elim: ensure_use_bang.cases)+

lemma ensure_use_bang_nthD[dest]:
  "ensure_use_bang N xs \<Longrightarrow> i < length xs \<Longrightarrow> i \<in> N \<Longrightarrow> 1 \<le> xs ! i"
  by (induct xs arbitrary: i N)
    (force simp add: Suc_mem_image_pred_remove less_Suc_eq_0_disj)+

lemma ensure_use_bang_all_nth:
  "ensure_use_bang N xs = (\<forall>i<length xs. i \<in> N \<longrightarrow> 1 \<le> xs ! i)"
  by (induct xs arbitrary: N)
    (bestsimp simp add: Suc_mem_image_pred_remove All_less_Suc2)+


fun context_bang_types :: "nat set \<Rightarrow> type list \<Rightarrow> type list" where
  "context_bang_types N [] = []"
| "context_bang_types N (t # ts) = (if 0 \<in> N then bang t else t) # context_bang_types (pred ` Set.remove 0 N) ts"

lemma context_bang_types_length[simp]:
  "length (context_bang_types N xs) = length xs"
  by (induct xs arbitrary: N) simp+

lemma context_bang_types_nth[simp]:
  assumes
    "i < length xs"
  shows
    "context_bang_types N xs ! i = (if i \<in> N then bang (xs ! i) else (xs ! i))"
  using assms
  by (induct xs arbitrary: i N)
     (force simp add: less_Suc_eq_0_disj Suc_mem_image_pred_remove)+

lemma context_bang_types_wellformed_iff:
  "K \<turnstile>* context_bang_types N ts wellformed \<longleftrightarrow> K \<turnstile>* ts wellformed"
  by (simp add: list_all_length)


fun remove_use_bang :: "nat set \<Rightarrow> ('a :: zero) list \<Rightarrow> 'a list" where
  "remove_use_bang N [] = []"
| "remove_use_bang N (x # xs) = (if 0 \<in> N then 0 else x) # remove_use_bang (pred ` Set.remove 0 N) xs"

lemma remove_use_bang_length[simp]:
  "length (remove_use_bang N xs) = length xs"
  by (induct xs arbitrary: N) simp+

lemma remove_use_bang_nth[simp]:
  assumes
    "i < length xs"
  shows
    "remove_use_bang N xs ! i = (if i \<in> N then 0 else (xs ! i))"
  using assms
  by (induct xs arbitrary: i N)
     (force simp add: less_Suc_eq_0_disj Suc_mem_image_pred_remove)+

section \<open> Linearity \<close>

text \<open>
  A type is used either not at all, once, or many times. A one time use is said to be linear,
  a non-use or a many-times use is said to be non-linear. (non-uses are related to relevancy and 
  many-uses are related to affine-ness.)
\<close>

datatype linearity = LMany ("\<omega>") | LOne | LNone

instantiation linearity :: "{one, linorder, bounded_lattice, canonically_ordered_monoid_add, zero_less_one}"
begin

definition "bot_linearity \<equiv> LNone"
fun sup_linearity :: "linearity \<Rightarrow> linearity \<Rightarrow> linearity" where
  "sup_linearity LNone b = b"
| "sup_linearity LOne LNone = LOne"
| "sup_linearity LOne b = b"
| "sup_linearity LMany b = LMany"
definition "top_linearity \<equiv> LMany"
fun inf_linearity :: "linearity \<Rightarrow> linearity \<Rightarrow> linearity" where
  "inf_linearity LMany b = b"
| "inf_linearity LOne LMany = LOne"
| "inf_linearity LOne b = b"
| "inf_linearity LNone b = LNone"

definition "zero_linearity \<equiv> LNone"

definition "one_linearity \<equiv> LOne"

fun less_eq_linearity :: "linearity \<Rightarrow> linearity \<Rightarrow> bool" where
  "less_eq_linearity LNone _ = True"
| "less_eq_linearity LOne LNone = False"
| "less_eq_linearity LOne _ = True"
| "less_eq_linearity LMany LMany = True"
| "less_eq_linearity LMany _ = False"

fun less_linearity :: "linearity \<Rightarrow> linearity \<Rightarrow> bool" where
  "less_linearity LNone LNone = False"
| "less_linearity LNone _ = True"
| "less_linearity LOne LOne = False"
| "less_linearity LOne LNone = False"
| "less_linearity LOne _ = True"
| "less_linearity LMany _ = False"

fun plus_linearity :: "linearity \<Rightarrow> linearity \<Rightarrow> linearity" where
  "plus_linearity LNone x = x"
| "plus_linearity LOne LNone = LOne"
| "plus_linearity LOne LOne = LMany"
| "plus_linearity LOne LMany = LMany"
| "plus_linearity LMany x = LMany"

lemma lin_add_sym: "a + b = b + (a :: linearity)"
  by (cases a; cases b; simp)

lemma lin_sup_sym: "sup a b = sup b (a :: linearity)"
  by (cases a; cases b; simp)


lemma linearity_1plus1[simp]: "1 + 1 = \<omega>"
  by (simp add: one_linearity_def)

lemma linearity_add_to_none_are_nones[simp]: "a + b = LNone \<longleftrightarrow> (a = LNone \<and> b = LNone)"
  using plus_linearity.elims by auto
lemmas linearity_add_to_none_are_nones2[simp] =
  trans[OF eq_commute linearity_add_to_none_are_nones]

lemma linearity_add_to_one_has_nonzero: "a + b = LOne \<Longrightarrow> (a \<noteq> LNone \<or> b \<noteq> LNone)"
  by auto

lemma linearity_sup_to_many_some_many[simp]: "sup a b = \<omega> \<longleftrightarrow> (a = \<omega> \<or> b = \<omega>)"
  using sup_linearity.elims
  by (cases a; cases b; simp)
lemmas linearity_sup_to_many_some_many2[simp] =
  trans[OF eq_commute linearity_sup_to_many_some_many]

instance
proof
  fix x y z :: linearity
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (cases x; cases y; simp)
  show "x \<le> x"
    by (cases x; simp)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z; simp)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y; simp)
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y; simp)
next
  fix a b c :: linearity
  show "a + b + c = a + (b + c)"
    by (cases a; cases b; cases c; simp)
  show "a + b = b + a"
    by (cases a; cases b; simp)
  show "0 + a = a"
    by (cases a; simp add: zero_linearity_def)
next
  fix a :: linearity
  show "bot \<le> a"
    by (simp add: bot_linearity_def)
  show "a \<le> top"
    by (cases a; simp add: top_linearity_def)
next
  fix x y z :: linearity
  show "inf x y \<le> x"
    by (cases x; cases y; simp)
  show "inf x y \<le> y"
    by (cases x; cases y; simp)
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z"
    by (cases x; cases y; cases z; simp)
  show "x \<le> sup x y"
    by (cases x; cases y; simp)
  show "y \<le> sup x y"
    by (cases x; cases y; simp)
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> sup y z \<le> x"
    by (cases x; cases y; cases z; simp)
next
  fix a b :: linearity
  show "(a \<le> b) = (\<exists>c. b = a + c)"
    by (cases "(a,b)" rule: less_eq_linearity.cases
        ; simp, (metis plus_linearity.simps(2-3))?)
next
  show "(0::linearity) < 1"
    by (simp add: zero_linearity_def one_linearity_def)
qed

end

lemma linearity_extra_simps[simp]:
  "(LNone = 0) = True"
  "(LOne = 1) = True"
  "(LOne = 0) = False"
  "(0 = LOne) = False"
  "(1 = LNone) = False"
  "(LNone = 1) = False"
  "(LNone \<noteq> 0) = False"
  "(0 \<noteq> LNone) = False"
  "(LOne \<noteq> 1) = False"
  "(1 \<noteq> LOne) = False"
  "(1::linearity) \<le> 0 \<longleftrightarrow> False"
  "(1::linearity) < 0 \<longleftrightarrow> False"
  "\<omega> \<le> 0 \<longleftrightarrow> False"
  "\<omega> < 0 \<longleftrightarrow> False"
  "\<omega> \<le> 1 \<longleftrightarrow> False"
  "\<omega> < 1 \<longleftrightarrow> False"
  by (simp add: lin_add_sym zero_linearity_def one_linearity_def)+

lemmas linearity_distinct_zero_one[simp] =
  linearity.distinct[simplified zero_linearity_def[symmetric] one_linearity_def[symmetric]]

lemma plus_linearity_simps[simp]:
  "x + LNone = x"
  "x + \<omega> = \<omega>"
  by (simp add: lin_add_sym zero_linearity_def one_linearity_def)+

lemma sup_linearity_simps[simp]:
  "sup 1 \<omega> = \<omega>"
  "sup x LNone = x"
  "sup x 0 = x"
  "sup 0 x = x"
  by (simp add: zero_linearity_def one_linearity_def bot_linearity_def[symmetric])+

lemma linearity_zero_case[simp]: "case_linearity p q r 0 = r"
  by (simp add: zero_linearity_def)

lemma linearity_one_case[simp]: "case_linearity p q r 1 = q"
  by (simp add: one_linearity_def)

lemmas linearity_order_simps[simp] =
  order_top_class.top_greatest[where a="a :: linearity" for a, simplified top_linearity_def]
  order_bot_class.bot_least[where a="a :: linearity" for a, simplified bot_linearity_def]
  order_bot_class.bot_least[where a="a :: linearity" for a, simplified bot_linearity_def zero_linearity_def[symmetric]]

lemma linearity_neq_none_iff: "x \<noteq> LNone \<longleftrightarrow> x = \<omega> \<or> x = LOne"
  by (cases x; simp)
lemmas linearity_neq_none_iff2 =
  linearity_neq_none_iff[simplified zero_linearity_def[symmetric] one_linearity_def[symmetric]]

lemma linearity_neq_one_iff: "x \<noteq> LOne \<longleftrightarrow> x = \<omega> \<or> x = LNone"
  by (cases x; simp)
lemmas linearity_neq_one_iff2 =
  linearity_neq_one_iff[simplified zero_linearity_def[symmetric] one_linearity_def[symmetric]]

lemma linearity_neq_many_iff: "x \<noteq> \<omega> \<longleftrightarrow> x = LOne \<or> x = LNone"
  by (cases x; simp)
lemmas linearity_neq_many_iff2 =
  linearity_neq_many_iff[simplified zero_linearity_def[symmetric] one_linearity_def[symmetric]]

lemma linearity_none_impl_iff: "(x = 0 \<longrightarrow> P) \<longleftrightarrow> x = 1 \<or> x = \<omega> \<or> P"
  by (force simp add: imp_conv_disj linearity_neq_none_iff2 simp del: disj_not1)

lemmas linearity_none_impl_iff2 = linearity_none_impl_iff[simplified zero_linearity_def one_linearity_def]

lemma linearity_one_impl_iff:  "(x = 1 \<longrightarrow> P) \<longleftrightarrow> x = 0 \<or> x = \<omega> \<or> P"
  by (force simp add: imp_conv_disj linearity_neq_one_iff2 simp del: disj_not1)

lemmas linearity_one_impl_iff2 = linearity_one_impl_iff[simplified zero_linearity_def one_linearity_def]

lemma linearity_many_impl_iff:  "(x = \<omega> \<longrightarrow> P) \<longleftrightarrow> x = 0 \<or> x = 1 \<or> P"
  by (force simp add: imp_conv_disj linearity_neq_many_iff2 simp del: disj_not1)

lemmas linearity_many_impl_iff2 = linearity_many_impl_iff[simplified zero_linearity_def one_linearity_def]

lemma linearity_add_to_one_iff: "(c1 :: linearity) + c2 = 1 \<longleftrightarrow> c1 = 1 \<and> c2 = 0 \<or> c1 = 0 \<and> c2 = 1"
  by (cases c1; cases c2; simp add: zero_linearity_def one_linearity_def)

lemma linearity_one_lt_eq_many:
  "1 < c \<longleftrightarrow> c = \<omega>"
  by (cases c; simp add: one_linearity_def)

lemma linearity_one_le_eq_one_or_many:
  "1 \<le> c \<longleftrightarrow> c = 1 \<or> c = \<omega>"
  by (cases c; simp add: one_linearity_def)

lemma linearity_gt_one_eq_zero_or_one:
  fixes c :: linearity
  shows
    "c \<le> 1 \<longleftrightarrow> c = 0 \<or> c = 1"
  by (cases c; simp add: zero_linearity_def one_linearity_def)


definition droppable :: "kind env \<Rightarrow> type \<Rightarrow> bool" where
  "droppable K t \<equiv> D \<in> kinding_fn K t"

lemma droppable_simps[simp]:
  "\<And>K i. i < length K \<Longrightarrow> droppable K (TVar i) \<longleftrightarrow> D \<in> K ! i"
  "\<And>K i. droppable K (TVarBang i) \<longleftrightarrow> True"
  "\<And>K n ts s. droppable K (TCon n ts s) \<longleftrightarrow> list_all (droppable K) ts \<and> D \<in> sigil_kind s"
  "\<And>K ta tb. droppable K (TFun ta tb) \<longleftrightarrow> True"
  "\<And>K p. droppable K (TPrim p) \<longleftrightarrow> True"
  "\<And>K ts. droppable K (TSum ts) \<longleftrightarrow> list_all (\<lambda>(_, t, y). case_variant_state True (droppable K t) y) ts"
  "\<And>K ta tb. droppable K (TProduct ta tb) \<longleftrightarrow> droppable K ta \<and> droppable K tb"
  "\<And>K ts s. droppable K (TRecord ts s) \<longleftrightarrow> list_all (\<lambda>(_, t, y). case_record_state True (droppable K t) y) ts \<and> D \<in> sigil_kind s"
  "\<And>K. droppable K TUnit \<longleftrightarrow> True"
  by (force simp add: droppable_def all_set_conv_all_nth list_all_length prod_eq_iff
      kinding_fn_all_def kinding_fn_all_variant_def kinding_fn_all_record_def
      split: variant_state.splits record_state.splits)+

lemma kinding_includes_drop_eq[simp]:
  "(\<exists>k. (K \<turnstile> t :\<kappa> k) \<and> D \<in> k) \<longleftrightarrow> K \<turnstile> t wellformed \<and> droppable K t"
  by (force simp add: kinding_def droppable_def)

definition shareable :: "kind env \<Rightarrow> type \<Rightarrow> bool" where
  "shareable K t \<equiv> S \<in> kinding_fn K t"

lemma shareable_simps[simp]:
  "\<And>K i. i < length K \<Longrightarrow> shareable K (TVar i) \<longleftrightarrow> S \<in> K ! i"
  "\<And>K i. shareable K (TVarBang i) \<longleftrightarrow> True"
  "\<And>K n ts s. shareable K (TCon n ts s) \<longleftrightarrow> list_all (shareable K) ts \<and> S \<in> sigil_kind s"
  "\<And>K ta tb. shareable K (TFun ta tb) \<longleftrightarrow> True"
  "\<And>K p. shareable K (TPrim p) \<longleftrightarrow> True"
  "\<And>K ts. shareable K (TSum ts) \<longleftrightarrow> list_all (\<lambda>(_, t, y). case_variant_state True (shareable K t) y) ts"
  "\<And>K ta tb. shareable K (TProduct ta tb) \<longleftrightarrow> shareable K ta \<and> shareable K tb"
  "\<And>K ts s. shareable K (TRecord ts s) \<longleftrightarrow> list_all (\<lambda>(_, t, y). case_record_state True (shareable K t) y) ts \<and> S \<in> sigil_kind s"
  "\<And>K. shareable K TUnit \<longleftrightarrow> True"
  by (auto simp add: shareable_def all_set_conv_all_nth list_all_length prod_eq_iff
      kinding_fn_all_def kinding_fn_all_variant_def kinding_fn_all_record_def
      split: variant_state.splits record_state.splits)+

lemma kinding_includes_share_eq[simp]:
  "(\<exists>k. (K \<turnstile> t :\<kappa> k) \<and> S \<in> k) \<longleftrightarrow> K \<turnstile> t wellformed \<and> shareable K t"
  by (force simp add: kinding_def shareable_def)

definition nonlinear :: "kind env \<Rightarrow> type \<Rightarrow> bool" where
  "nonlinear K t \<equiv> droppable K t \<and> shareable K t"

lemma nonlinear_simps[simp]:
  "\<And>K i. i < length K \<Longrightarrow> nonlinear K (TVar i) \<longleftrightarrow> D \<in> K ! i \<and> S \<in> K ! i"
  "\<And>K i. nonlinear K (TVarBang i) \<longleftrightarrow> True"
  "\<And>K n ts s. nonlinear K (TCon n ts s) \<longleftrightarrow> list_all (nonlinear K) ts \<and> D \<in> sigil_kind s \<and> S \<in> sigil_kind s"
  "\<And>K ta tb. nonlinear K (TFun ta tb) \<longleftrightarrow> True"
  "\<And>K p. nonlinear K (TPrim p) \<longleftrightarrow> True"
  "\<And>K ts. nonlinear K (TSum ts) \<longleftrightarrow> list_all (\<lambda>(_, t, y). case_variant_state True (nonlinear K t) y) ts"
  "\<And>K ta tb. nonlinear K (TProduct ta tb) \<longleftrightarrow> nonlinear K ta \<and> nonlinear K tb"
  "\<And>K ts s. nonlinear K (TRecord ts s) \<longleftrightarrow> list_all (\<lambda>(_, t, y). case_record_state True (nonlinear K t) y) ts \<and> D \<in> sigil_kind s \<and> S \<in> sigil_kind s"
  "\<And>K. nonlinear K TUnit \<longleftrightarrow> True"
  by (force simp add: nonlinear_def all_set_conv_all_nth list_all_length split: variant_state.splits record_state.splits)+

subsection \<open> Equivalence under well-kinded \<close>

lemma droppable_iff_nonlinear:
  "well_kinded_all K \<Longrightarrow> K \<turnstile> t wellformed \<Longrightarrow> droppable K t \<longleftrightarrow> nonlinear K t"
  by (induct t)
      (clarsimp
        simp add: list_all_length well_kinded_all_def well_kinded_def sigil_kind_drop_iff_share
        prod_eq_iff_proj_eq in_set_conv_nth
        split: prod.splits variant_state.splits record_state.splits; metis)+

lemma shareable_iff_nonlinear:
  "well_kinded_all K \<Longrightarrow> K \<turnstile> t wellformed \<Longrightarrow> shareable K t \<longleftrightarrow> nonlinear K t"
  by (induct t)
      (clarsimp
        simp add: list_all_length well_kinded_all_def well_kinded_def sigil_kind_drop_iff_share
        prod_eq_iff_proj_eq in_set_conv_nth
        split: prod.splits variant_state.splits record_state.splits; metis)+

lemma droppable_iff_shareable:
  "well_kinded_all K \<Longrightarrow> K \<turnstile> t wellformed \<Longrightarrow> droppable K t \<longleftrightarrow> shareable K t"
  by (simp add: droppable_iff_nonlinear shareable_iff_nonlinear)

lemma shareable_iff_droppable:
  "well_kinded_all K \<Longrightarrow> K \<turnstile> t wellformed \<Longrightarrow> shareable K t \<longleftrightarrow> droppable K t"
  by (simp add: droppable_iff_nonlinear shareable_iff_nonlinear)

definition is_drop_safe :: "kind env \<Rightarrow> type \<Rightarrow> ('a :: {one, semilattice_sup}) \<Rightarrow> bool" where
  "is_drop_safe K t c \<equiv> c \<ge> 1 \<or> droppable K t"

lemma is_drop_safe_linearity_simps[simp]:
  "is_drop_safe K t \<omega> = True"
  "is_drop_safe K t LOne = True"
  "is_drop_safe K t LNone = droppable K t"
  by (clarsimp simp add: one_linearity_def is_drop_safe_def)+

lemmas is_drop_safe_linearity_simps2 =
  is_drop_safe_linearity_simps(2-)[simplified zero_linearity_def[symmetric] one_linearity_def[symmetric]]

definition is_share_safe :: "kind list \<Rightarrow> type \<Rightarrow> ('a :: {one, semilattice_sup}) \<Rightarrow> bool" where
  "is_share_safe K t c \<equiv> c \<le> 1 \<or> shareable K t"

lemma is_share_safe_linearity_simps[simp]:
  "is_share_safe K t \<omega> = shareable K t"
  "is_share_safe K t LOne = True"
  "is_share_safe K t LNone = True"
  by (clarsimp simp add: one_linearity_def is_share_safe_def)+

lemmas is_share_safe_linearity_simps2 =
  is_share_safe_linearity_simps(2-)[simplified zero_linearity_def[symmetric] one_linearity_def[symmetric]]

definition is_used :: "kind env \<Rightarrow> type \<Rightarrow> ('a :: {one, semilattice_sup}) \<Rightarrow> bool" where
  "is_used K t c \<equiv> is_drop_safe K t c \<and> is_share_safe K t c"

lemma is_used_linearity_simps[simp]:
  "is_used K t \<omega> = shareable K t"
  "is_used K t LOne = True"
  "is_used K t LNone = droppable K t"
  by (clarsimp simp add: is_used_def)+

lemmas is_used_linearity_simps2 =
  is_used_linearity_simps(2-)[simplified zero_linearity_def[symmetric] one_linearity_def[symmetric]]


definition droppable_constraint :: "kind list \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> bool" where
  "droppable_constraint K \<equiv> list_all2 (is_drop_safe K)"

lemmas droppable_constraint_conv_all_nth =
  list_all2_conv_all_nth[where P=\<open>is_drop_safe K :: type \<Rightarrow> linearity \<Rightarrow> bool\<close> for K, simplified 
                         droppable_constraint_def[symmetric]]



definition merge_drop_condition_comp :: "kind list \<Rightarrow> type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool" where
  "merge_drop_condition_comp K t c1 c2 \<equiv> (c1 = 0 \<and> c2 \<noteq> 0) \<or> (c1 \<noteq> 0 \<and> c2 = 0) \<longrightarrow> droppable K t"

definition merge_drop_condition :: "kind list \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> linearity list \<Rightarrow> bool" where
  "merge_drop_condition K \<equiv> list_all3 (merge_drop_condition_comp K)"

lemmas merge_drop_condition_conv_all_nth =
  list_all3_conv_all_nth[where P=\<open>merge_drop_condition_comp K\<close> for K,
                         simplified merge_drop_condition_def[symmetric]]

lemmas merge_drop_condition_Nil1[simp] =
  list_all3_Nil1[where P=\<open>merge_drop_condition_comp K\<close> for K,
                         simplified merge_drop_condition_def[symmetric]]
lemmas merge_drop_condition_Nil2[simp] =
  list_all3_Nil2[where P=\<open>merge_drop_condition_comp K\<close> for K,
                         simplified merge_drop_condition_def[symmetric]]
lemmas merge_drop_condition_Nil3[simp] =
  list_all3_Nil3[where P=\<open>merge_drop_condition_comp K\<close> for K,
                         simplified merge_drop_condition_def[symmetric]]

lemmas merge_drop_condition_Cons[simp] =
  list_all3_Cons[where P=\<open>merge_drop_condition_comp K\<close> for K,
                         simplified merge_drop_condition_def[symmetric]]

lemmas merge_drop_condition_Cons1 =
  list_all3_Cons1[where P=\<open>merge_drop_condition_comp K\<close> for K,
                         simplified merge_drop_condition_def[symmetric]]
lemmas merge_drop_condition_Cons2 =
  list_all3_Cons2[where P=\<open>merge_drop_condition_comp K\<close> for K,
                         simplified merge_drop_condition_def[symmetric]]
lemmas merge_drop_condition_Cons3 =
  list_all3_Cons3[where P=\<open>merge_drop_condition_comp K\<close> for K,
                         simplified merge_drop_condition_def[symmetric]]

lemma merge_drop_condition_nthD[dest]:
  "\<lbrakk> merge_drop_condition K G C1 C2; C1 ! i = 0; C2 ! i \<noteq> 0; i < length G \<rbrakk> \<Longrightarrow> droppable K (G ! i)"
  "\<lbrakk> merge_drop_condition K G C1 C2; C1 ! i \<noteq> 0; C2 ! i = 0; i < length G \<rbrakk> \<Longrightarrow> droppable K (G ! i)"
  by (clarsimp simp add: merge_drop_condition_conv_all_nth merge_drop_condition_comp_def)+


(*
\<Gamma> is input.
C is output.
The expression is input.
For synthesising, the type is output.
For checking, the type is input.

Not that C being output means that in an assumption, C should be a variable.
If you want to enforce a structure on C, you have to use an equality so it can do computation.
*)
inductive tyinf_synth :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> bool"
          ("_, _, _, _ \<turnstile>\<down> _ : _" [30,0,0,0,0,20] 60)
      and tyinf_check :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> bool"
          ("_, _, _, _ \<turnstile>\<up> _ : _" [30,0,0,0,0,20] 60)
      and tyinf_all_synth :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> 'f expr list \<Rightarrow> type list \<Rightarrow> bool"
          ("_, _, _, _ \<turnstile>\<down>* _ : _" [30,0,0,0,0,20] 60) where

(* synthesising *)

  tyinf_var    : "\<lbrakk> i < length \<Gamma>
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, (replicate (length \<Gamma>) 0)[i := 1] \<turnstile>\<down> Var i : (\<Gamma> ! i)"

| tyinf_tuple  : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> t : \<tau>1
                  ; \<Xi>, K, \<Gamma>, C2 \<turnstile>\<down> u : \<tau>2
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<down> Tuple t u : TProduct \<tau>1 \<tau>2"

| tyinf_con    : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> x : t
                  ; (tag, t, Unchecked) \<in> set ts
                  ; K \<turnstile> TSum ts wellformed \<^cancel>\<open>FIXME: we don't need to check t\<close>
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Con ts tag x : TSum ts"

| tyinf_esac   : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> x : TSum ts
                  ; [(n, t, Unchecked)] = filter ((=) Unchecked \<circ> snd \<circ> snd) ts
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Esac x n : t"


| tyinf_lit    : "\<Xi>, K, \<Gamma>, replicate (length \<Gamma>) 0 \<turnstile>\<down> Lit l : TPrim (lit_type l)"

| tyinf_slit   : "\<Xi>, K, \<Gamma>, replicate (length \<Gamma>) 0 \<turnstile>\<down> SLit s : TPrim String"

| tyinf_unit   : "\<Xi>, K, \<Gamma>, replicate (length \<Gamma>) 0 \<turnstile>\<down> Unit : TUnit"

| tyinf_member : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> e : TRecord ts s
                  ; f < length ts
                  ; ts ! f = (n, t, Present)
                  ; droppable K (TRecord (ts[f := (n, t, Taken)]) s)
                  ; sigil_perm s \<noteq> Some Writable
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Member e f : t"

| tyinf_put    : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> e : \<tau>1
                  ; \<tau>1 = TRecord ts s
                  ; sigil_perm s \<noteq> Some ReadOnly
                  ; f < length ts
                  ; ts ! f = (n, t, taken)
                  ; droppable K t \<or> taken = Taken
                  ; \<Xi>, K, \<Gamma>, C2 \<turnstile>\<up> e' : t
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<down> Put e f e' : TRecord (ts[f := (n,t,Present)]) s"

| tyinf_prim   : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down>* args : ts' \<^cancel>\<open>FIXME: should this be checking?\<close>
                  ; prim_op_type oper = (ts,t)
                  ; ts' = map TPrim ts
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Prim oper args : TPrim t"

| tyinf_struct : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down>* es : ts
                  ; ts = ts' \<^cancel>\<open>FIXME: remove ts'\<close>
                  ; length ns = length ts'
                  ; distinct ns
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Struct ns ts' es : TRecord (zip ns (map (\<lambda>t. (t,Present)) ts)) Unboxed"

| tyinf_app    : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> a : \<tau>1
                  ; \<tau>1 = TFun x y
                  ; \<Xi>, K, \<Gamma>, C2 \<turnstile>\<up> b : x
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<down> App a b : y"

(* checking *)

| tyinf_cast   : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> e : \<tau>1
                  ; \<tau>1 = TPrim (Num nt)
                  ; upcast_valid nt nt1
                  ; nt1 = nt2 \<^cancel>\<open>FIXME: nt1 is unecessary\<close>
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<up> Cast nt1 e : TPrim (Num nt2)"

| tyinf_split  : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> x : TProduct t u
                  ; \<Xi>, K, (t # u # \<Gamma>), C2o \<turnstile>\<up> y : t'
                  ; C2o = ct # cu # C2
                  ; is_used K t ct
                  ; is_used K u cu
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<up> Split x y : t'"

| tyinf_let    : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> x : t
                  ; \<Xi>, K, (t # \<Gamma>), C2o \<turnstile>\<up> y : u
                  ; C2o = ct # C2
                  ; is_used K t ct
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<up> Let x y : u"

| tyinf_letb   : "\<lbrakk> \<Xi>, K, context_bang_types is \<Gamma>, C1 \<turnstile>\<down> x : t
                  ; \<Xi>, K, (t # \<Gamma>), C2o \<turnstile>\<up> y : u
                  ; C2o = ct # C2
                  ; is_used K t ct
                  ; E \<in> kinding_fn K t
                  ; ensure_use_bang is C2
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, remove_use_bang is C1 \<oplus> C2 \<turnstile>\<up> LetBang is x y : u"

| tyinf_case   : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> x : \<tau>1
                  ; \<tau>1 = TSum ts
                  ; (tag, t, Unchecked) \<in> set ts
                  ; \<Xi>, K, (t # \<Gamma>), C2ao \<turnstile>\<up> a : u
                  ; C2ao = ct # C2a
                  ; is_used K t ct
                  ; \<Xi>, K, (TSum (tagged_list_update tag (t, Checked) ts) # \<Gamma>), C2bo \<turnstile>\<up> b : u
                  ; C2bo = csum # C2b
                  ; is_used K (TSum (tagged_list_update tag (t, Checked) ts)) csum
                  ; merge_drop_condition K \<Gamma> C2a C2b
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> countMax C2a C2b \<turnstile>\<up> Case x tag a b : u"

| tyinf_if     : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> x : \<tau>
                  ; \<tau> = TPrim Bool
                  ; \<Xi>, K, \<Gamma>, C2a \<turnstile>\<up> a : t
                  ; \<Xi>, K, \<Gamma>, C2b \<turnstile>\<up> b : t
                  ; merge_drop_condition K \<Gamma> C2a C2b
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> (countMax C2a C2b) \<turnstile>\<up> If x a b : t"

| tyinf_take   : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> e : \<tau>1
                  ; \<tau>1 = TRecord ts s
                  ; sigil_perm s \<noteq> Some ReadOnly
                  ; f < length ts
                  ; ts ! f = (n, t, Present)
                  ; shareable K t \<or> taken = Taken
                  ; \<Xi>, K, (t # TRecord (ts [f := (n,t,taken)]) s # \<Gamma>), C2o \<turnstile>\<up> e' : u
                  ; C2o = ct # cr # C2
                  ; is_used K t ct
                  ; is_used K (TRecord (ts [f := (n,t,taken)]) s) cr
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<up> Take e f e' : u"

(* TODO: we don't need promote expressions *)
| tyinf_promote: "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> x : t'
                  ; K \<turnstile> t' \<sqsubseteq> t
                  ; t'' = t
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<up> Promote t'' x : t"

(* TODO: this can be absorbed into the subtyping case once promote expressions are removed.
 *       For the sake of efficiency, the "is the subtyping a refl" case should still be checked
 *       first by the tactic, using the subtyping_refl lemma.
 *)
| tyinf_switch: "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> x : \<tau>
                 ; \<tau> = \<tau>'
                 \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<up> x : \<tau>'"

| tyinf_all_empty : "\<Xi>, K, \<Gamma>, replicate (length \<Gamma>) 0 \<turnstile>\<down>* [] : []"

| tyinf_all_cons  : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> e : t
                     ; \<Xi>, K, \<Gamma>, C2 \<turnstile>\<down>* es : ts
                     \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<down>* (e # es) : (t # ts)"

| tyinf_afun   : "\<lbrakk> \<Xi> f = (K', t, u)
                  ; list_all2 (kinding K) ts K'
                  ; K \<turnstile>* ts wellformed
                  ; type_wellformed (length ts) t
                  ; type_wellformed (length ts) u
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, replicate (length \<Gamma>) 0 \<turnstile>\<down> AFun f ts : TFun (instantiate ts t) (instantiate ts u)"

| tyinf_fun    : "\<lbrakk> \<Xi>, K', [t], [1] \<turnstile>\<up> f : u
                  ; well_kinded_all K'
                  ; list_all2 (kinding K) ts K'
                  ; K \<turnstile>* ts wellformed
                  ; type_wellformed (length ts) t
                  ; type_wellformed (length ts) u
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, replicate (length \<Gamma>) 0 \<turnstile>\<down> Fun f ts : TFun (instantiate ts t) (instantiate ts u)"

(*
lemma "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<up> x : t
       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Annotate t x : t"
*)

inductive_cases tyinf_synth_varE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Var i : t"
inductive_cases tyinf_synth_tupleE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Tuple e1 e2 : t"
inductive_cases tyinf_synth_conE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Con ts tag x : t"
inductive_cases tyinf_synth_esacE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Esac x n : t"
inductive_cases tyinf_synth_litE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Lit l : t"
inductive_cases tyinf_synth_slitE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> SLit s : t"
inductive_cases tyinf_synth_unitE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Unit : t"
inductive_cases tyinf_synth_memberE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Member e f : t"
inductive_cases tyinf_synth_putE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Put e f e' : t"
inductive_cases tyinf_synth_primE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Prim oper arg : t"
inductive_cases tyinf_synth_structE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Struct ns ts es : t"
inductive_cases tyinf_synth_funE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Fun f ts : t"

inductive_cases tyinf_check_castE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Cast nm e : t"
inductive_cases tyinf_check_appE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> App x y : t"
inductive_cases tyinf_check_splitE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Split x y : t"
inductive_cases tyinf_check_letE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Let x y : t"
inductive_cases tyinf_check_letbE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> LetBang is x y : t"
inductive_cases tyinf_check_caseE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Case x tag a b : t"
inductive_cases tyinf_check_ifE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> If x a b : t"
inductive_cases tyinf_check_takeE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Take e f e' : t"

inductive_cases tyinf_check_varE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Var i : t"
inductive_cases tyinf_check_tupleE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Tuple e1 e2 : t"
inductive_cases tyinf_check_conE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Con ts tag x : t"
inductive_cases tyinf_check_esacE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Esac x n : t"
inductive_cases tyinf_check_litE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Lit l : t"
inductive_cases tyinf_check_slitE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> SLit s : t"
inductive_cases tyinf_check_unitE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Unit : t"
inductive_cases tyinf_check_memberE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Member e f : t"
inductive_cases tyinf_check_putE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Put e f e' : t"
inductive_cases tyinf_check_primE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Prim oper arg : t"
inductive_cases tyinf_check_structE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Struct ns ts es : t"
inductive_cases tyinf_check_funE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Fun f ts : t"

inductive_cases tyinf_check_promoteE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Promote t x : t"

inductive_cases tyinf_all_synth_consE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down>* (e # es) : ts"
inductive_cases tyinf_all_synth_nilE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down>* [] : ts"

lemmas tyinf_synth_safe_intros =
  tyinf_var tyinf_tuple tyinf_con tyinf_esac tyinf_lit tyinf_slit tyinf_unit tyinf_member tyinf_put
  tyinf_prim tyinf_struct tyinf_fun

lemmas tyinf_checking_safe_intros =
  tyinf_cast tyinf_app tyinf_split tyinf_let tyinf_letb tyinf_case tyinf_if tyinf_take
  tyinf_promote tyinf_all_empty tyinf_all_cons
  tyinf_synth_safe_intros[THEN tyinf_switch]

lemmas tyinf_safe_intros = tyinf_synth_safe_intros tyinf_checking_safe_intros


subsection \<open> Shareable Constraint \<close>

definition shareable_constraint :: "kind list \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> bool" where
  "shareable_constraint K \<equiv> list_all2 (is_share_safe K)"

lemmas shareable_constraint_conv_all_nth =
  list_all2_conv_all_nth[where P=\<open>is_share_safe K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> bool\<close> for K,
                         simplified shareable_constraint_def[symmetric]]

lemmas shareable_constraint_Nil1[simp] =
  list_all2_Nil[where P=\<open>is_share_safe K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> bool\<close> for K,
                 simplified shareable_constraint_def[symmetric]]
lemmas shareable_constraint_Nil2[simp] =
  list_all2_Nil2[where P=\<open>is_share_safe K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> bool\<close> for K,
                 simplified shareable_constraint_def[symmetric]]

lemmas shareable_constraint_Cons[simp] =
  list_all2_Cons[where P=\<open>is_share_safe K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> bool\<close> for K,
                 simplified shareable_constraint_def[symmetric]]
lemmas shareable_constraint_Cons1 =
  list_all2_Cons1[where P=\<open>is_share_safe K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> bool\<close> for K,
                  simplified shareable_constraint_def[symmetric]]
lemmas shareable_constraint_Cons2 =
  list_all2_Cons2[where P=\<open>is_share_safe K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> bool\<close> for K,
                  simplified shareable_constraint_def[symmetric]]

lemma shareable_constraint_shareable_nthD[dest]:
  "shareable_constraint K G C \<Longrightarrow> C ! i > 1 \<Longrightarrow> i < length G \<Longrightarrow> shareable K (G ! i)"
  by (force simp add: shareable_constraint_conv_all_nth is_share_safe_def)

lemma shareable_constraint_shareable_nth_manyD[dest]:
  "shareable_constraint K G C \<Longrightarrow> C ! i = \<omega> \<Longrightarrow> i < length G \<Longrightarrow> shareable K (G ! i)"
  by (simp add: shareable_constraint_shareable_nthD linearity_one_lt_eq_many)

lemma shareable_constraint_add[dest]:
  assumes "length C1 = length C2"
  shows
    "shareable_constraint K \<Gamma> (C1 \<oplus> C2) \<Longrightarrow> shareable_constraint K \<Gamma> C1"
    "shareable_constraint K \<Gamma> (C1 \<oplus> C2) \<Longrightarrow> shareable_constraint K \<Gamma> C2"
  using assms
  by (force dest: canonical_trans_le_add1 canonical_trans_le_add2
      simp add: shareable_constraint_conv_all_nth lin_add_sym is_share_safe_def)+

subsubsection \<open> New is_share_safe \<close>

text \<open>
  This judgement captures the additional constraints generated when two linearity contexts are
  added together.
\<close>

definition new_is_shared :: "kind list \<Rightarrow> type \<Rightarrow> ('a :: {one, canonically_ordered_monoid_add}) \<Rightarrow> 'a \<Rightarrow> bool" where
  "new_is_shared K \<equiv> (\<lambda>t c1 c2. c1 + c2 \<le> 1 \<or> shareable K t)"

definition new_shareable_constraint :: "kind list \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> linearity list \<Rightarrow> bool" where
  "new_shareable_constraint K \<equiv> list_all3 (new_is_shared K)"

lemmas new_shareable_constraint_conv_all_nth =
  list_all3_conv_all_nth[ where P=\<open>new_is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool\<close> for K
                        , simplified new_shareable_constraint_def[symmetric]]

lemmas new_shareable_constraint_Nil[simp,intro!] =
  all3Nil[ where P=\<open>new_is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool\<close> for K
         , simplified new_shareable_constraint_def[symmetric]]
lemmas new_shareable_constraint_Nil1[simp] =
  list_all3_Nil1[ where P=\<open>new_is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool\<close> for K
                , simplified new_shareable_constraint_def[symmetric]]
lemmas new_shareable_constraint_Nil2[simp] =
  list_all3_Nil2[ where P=\<open>new_is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool\<close> for K
                , simplified new_shareable_constraint_def[symmetric]]
lemmas new_shareable_constraint_Nil3[simp] =
  list_all3_Nil3[ where P=\<open>new_is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool\<close> for K
                , simplified new_shareable_constraint_def[symmetric]]

lemmas new_shareable_constraint_Cons =
  list_all3_Cons[ where P=\<open>new_is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool\<close> for K
                , simplified new_shareable_constraint_def[symmetric]]
lemmas new_shareable_constraint_Cons1 =
  list_all3_Cons1[ where P=\<open>new_is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool\<close> for K
                 , simplified new_shareable_constraint_def[symmetric]]
lemmas new_shareable_constraint_Cons2 =
  list_all3_Cons2[ where P=\<open>new_is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool\<close> for K
                 , simplified new_shareable_constraint_def[symmetric]]
lemmas new_shareable_constraint_Cons3 =
  list_all3_Cons3[ where P=\<open>new_is_shared K :: Cogent.type \<Rightarrow> linearity \<Rightarrow> linearity \<Rightarrow> bool\<close> for K
                 , simplified new_shareable_constraint_def[symmetric]]

lemma is_shared_plus_iff:
  "is_share_safe K t (c1 + c2) \<longleftrightarrow> is_share_safe K t c1 \<and> is_share_safe K t c2 \<and> new_is_shared K t c1 c2"
  unfolding is_share_safe_def new_is_shared_def
  by (force dest: canonical_trans_le_add1 canonical_trans_le_add2)

lemma shareable_constraint_plus_iff:
  assumes "length C1 = length C2"
  shows
    "shareable_constraint K \<Gamma> (C1 \<oplus> C2) \<longleftrightarrow>
      shareable_constraint K \<Gamma> C1
      \<and> shareable_constraint K \<Gamma> C2
      \<and> new_shareable_constraint K \<Gamma> C1 C2"
  using assms
  by (force simp add: shareable_constraint_conv_all_nth new_shareable_constraint_conv_all_nth
      is_shared_plus_iff)

subsection \<open> bang shareable_constraint \<close>

lemma is_shared_max_iff:
  shows "is_share_safe K t (sup c1 c2) \<longleftrightarrow> is_share_safe K t c1 \<and> is_share_safe K t c2"
  by (force simp add: is_share_safe_def one_linearity_def)

lemma shareable_constraint_max_iff:
  assumes "length C1 = length C2"
  shows "shareable_constraint K \<Gamma> (countMax C1 C2) \<longleftrightarrow> shareable_constraint K \<Gamma> C1 \<and> shareable_constraint K \<Gamma> C2"
  using assms
  by (force simp add: shareable_constraint_conv_all_nth new_shareable_constraint_conv_all_nth
      is_shared_max_iff)

lemma bang_is_shareable: "shareable K (bang t)"
  by (induct t)
    (fastforce simp add: list_all_length in_set_conv_nth bang_sigil_kind[simplified] shareable_def
      prod_eq_iff kinding_fn_all_def kinding_fn_all_variant_def kinding_fn_all_record_def
      split: variant_state.splits record_state.splits)+

lemma bang_is_share_safe: "is_share_safe K (bang t) c"
  by (simp add: is_share_safe_def bang_is_shareable)

lemma shareable_context_bang_types_if_shareable_remove_use_bang:
  "shareable_constraint K G (remove_use_bang N C) \<Longrightarrow> shareable_constraint K (context_bang_types N G) C"
  by (force simp add: shareable_constraint_conv_all_nth new_shareable_constraint_conv_all_nth
      is_shared_max_iff bang_is_share_safe is_share_safe_def bang_is_shareable)

lemma remove_use_bang_preserves_shareable_constraint:
  "shareable_constraint K G C \<Longrightarrow> shareable_constraint K G (remove_use_bang N C)"
  by (clarsimp simp add: shareable_constraint_conv_all_nth is_share_safe_def)


subsection \<open> Type Inference Properties \<close>

lemma tyinf_context_lengths:
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> e : t    \<Longrightarrow> length C = length \<Gamma>"
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> e : t    \<Longrightarrow> length C = length \<Gamma>"
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<down>* es : ts \<Longrightarrow> length C = length \<Gamma>"
  by (induct rule: tyinf_synth_tyinf_check_tyinf_all_synth.inducts) simp+

lemma list_all_update:
  "list_all P (xs[i := x]) \<longleftrightarrow> list_all P (take i xs) \<and> (i < length xs \<longrightarrow> P x) \<and> list_all P (drop (Suc i) xs)"
  by (induct xs arbitrary: i) (clarsimp split: nat.splits)+

lemma tyinf_preserves_wellformed[dest]:
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> e : t    \<Longrightarrow> K \<turnstile>* \<Gamma> wellformed \<Longrightarrow> K \<turnstile> t wellformed"
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> e : t    \<Longrightarrow> K \<turnstile>* \<Gamma> wellformed \<Longrightarrow> K \<turnstile> t wellformed"
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<down>* es : ts \<Longrightarrow> K \<turnstile>* \<Gamma> wellformed \<Longrightarrow> K \<turnstile>* ts wellformed"
proof (induct rule: tyinf_synth_tyinf_check_tyinf_all_synth.inducts)
  case tyinf_fun then show ?case
    by (force intro: instantiate_wellformed)
next
  case tyinf_afun then show ?case
    by (force intro: instantiate_wellformed)
next
  case tyinf_esac then show ?case
    by (clarsimp simp add: prod_eq_iff_proj_eq list_all_length map_fst_zip_take less_Suc_eq_0_disj
        singleton_filter_iff)
next
  case tyinf_put then show ?case
    by (force intro: distinct_upd_sameI simp add: list_all_length map_update nth_list_update)
next
  case tyinf_letb then show ?case
    by (simp add: context_bang_types_wellformed_iff)
next
  case tyinf_member then show ?case
    by (fastforce dest: type_wellformed_fstsnd_triple_nth)
next
  case tyinf_case then show ?case
    by (force simp add: list_all_iff)
next
  case tyinf_take then show ?case
    by (clarsimp simp add: prod_eq_iff_proj_eq distinct_fst_tags_update list_all_length
        nth_list_update All_less_Suc2)
next
  case tyinf_promote then show ?case
    by (force dest: subtyping_wellformed_preservation)
qed (simp; simp add: list_all_length map_fst_zip_take less_Suc_eq_0_disj)+

subsection \<open> Non-algorithmic Context Generation \<close>

definition tycount_context_gen_comp :: "type \<Rightarrow> linearity \<Rightarrow> type option" where
  "tycount_context_gen_comp \<equiv> (\<lambda>t c. if c = LNone then None else Some t)"

lemma tycount_context_gen_comp_simps[simp]:
  "tycount_context_gen_comp t \<omega> = Some t"
  "tycount_context_gen_comp t LOne = Some t"
  "tycount_context_gen_comp t LNone = None"
  by (simp add: tycount_context_gen_comp_def)+

lemmas tycount_context_gen_comp_simps2[simp] =
  tycount_context_gen_comp_simps(2-)[simplified
    zero_linearity_def[symmetric]
    one_linearity_def[symmetric]]

lemma context_gen_comp_None:
  "tycount_context_gen_comp t c = None \<longleftrightarrow> c = 0"
  by (cases c; simp)

lemma context_gen_comp_Some:
  "tycount_context_gen_comp t c = Some u \<longleftrightarrow> (t = u \<and> c \<noteq> 0)"
  by (cases c; simp)

definition tycount_context_gen :: "type list \<Rightarrow> linearity list \<Rightarrow> type option list" where
  "tycount_context_gen \<equiv> map2 tycount_context_gen_comp"

lemma tycount_context_gen_Nil[simp]:
  "tycount_context_gen [] [] = []"
  by (simp add: tycount_context_gen_def)

lemma tycount_context_gen_Cons[simp]:
  "tycount_context_gen (t # G) (c # C) = tycount_context_gen_comp t c # tycount_context_gen G C"
  by (simp add: tycount_context_gen_def)

lemma tycount_context_gen_length_eq[simp]:
  "length (tycount_context_gen G C) = min (length G) (length C)"
  by (simp add: tycount_context_gen_def)

lemma tycount_context_gen_nth[simp]:
  assumes
    "i < length G"
    "i < length C"
  shows
    "tycount_context_gen G C ! i = tycount_context_gen_comp (G ! i) (C ! i)"
  using assms
  by (simp add: tycount_context_gen_def)

subsubsection \<open> context_gen respects weaken \<close>

lemma weakens_to_context_gen:
  assumes
    "K \<turnstile> t wellformed"
    "is_drop_safe K t c"
  shows
    "weakening_comp K (Some t) (tycount_context_gen_comp t c)"
  using assms
  by (clarsimp simp add: context_gen_comp_Some weakening_comp.simps is_drop_safe_def
      linearity_one_le_eq_one_or_many droppable_def split: linearity.splits)

subsubsection \<open> join with + respects split \<close>

lemma tycount_context_gen_split_comp:
  assumes
    "K \<turnstile> t wellformed"
    "new_is_shared K t c1 c2"
  shows
    "K \<turnstile> tycount_context_gen_comp t (c1 + c2) \<leadsto> tycount_context_gen_comp t c1 \<parallel> tycount_context_gen_comp t c2"
  using assms
  by (force simp add: split_comp.simps tycount_context_gen_comp_def new_is_shared_def shareable_def
      linearity_add_to_one_iff linearity_gt_one_eq_zero_or_one zero_linearity_def)

lemma tycount_context_gen_split:
  assumes
    "K \<turnstile>* G wellformed"
    "new_shareable_constraint K G C1 C2"
  shows
    "K \<turnstile> tycount_context_gen G (C1 \<oplus> C2) \<leadsto> tycount_context_gen G C1 | tycount_context_gen G C2"
  using assms
  by (clarsimp simp add: split_conv_all_nth list_all_length
      new_shareable_constraint_conv_all_nth tycount_context_gen_split_comp)


subsubsection \<open> join with countPlusBang respects split bang \<close>

fun bangL_comp :: "bool \<Rightarrow> type \<Rightarrow> linearity \<Rightarrow> type option" where
  "bangL_comp i t c = (if i then Some (bang t) else tycount_context_gen_comp t c)"

fun bangR_comp :: "bool \<Rightarrow> type \<Rightarrow> linearity \<Rightarrow> type option" where
  "bangR_comp i t c = (if i then Some t else tycount_context_gen_comp t c)"

fun tycount_context_gen_bang ::
  "(bool \<Rightarrow> type \<Rightarrow> linearity \<Rightarrow> type option) \<Rightarrow> nat set \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> type option list"
where
  "tycount_context_gen_bang _ N [] [] = []"
| "tycount_context_gen_bang f N (t # ts) (c # cs) =
    f (0 \<in> N) t c # tycount_context_gen_bang f (pred ` Set.remove 0 N) ts cs"
| "tycount_context_gen_bang _ N [] (_ # _) = []"
| "tycount_context_gen_bang _ N (_ # _) [] = []"

lemma tycount_context_gen_bang_length[simp]:
    "length (tycount_context_gen_bang f N G C) = min (length G) (length C)"
  by (induct arbitrary: N rule: list_induct2') force+

lemma tycount_context_gen_bang_nth[simp]:
  assumes
    "i < length G"
    "i < length C"
  shows
    "tycount_context_gen_bang f N G C ! i = f (i \<in> N) (G ! i) (C ! i)"
  using assms
  by (induct arbitrary: i N rule: list_induct2')
     (force simp add: less_Suc_eq_0_disj Suc_mem_image_pred_remove)+


lemma tycount_context_gen_split_bang_comp:
  assumes
    "K \<turnstile> t wellformed"
    "i \<longrightarrow> 1 \<le> c2"
    "new_is_shared K t (if i then 0 else c1) c2"
  shows
    "K , i \<turnstile> tycount_context_gen_comp t ((if i then 0 else c1) + c2) \<leadsto>b
      bangL_comp i t c1 \<parallel> bangR_comp i t c2"
  using assms
  by (cases c1; cases c2; clarsimp simp add:
      split_comp.simps split_bang_comp.simps one_linearity_def
      new_is_shared_def shareable_def linearity_gt_one_eq_zero_or_one)

lemmas tycount_context_gen_split_bang_comp_True =
  tycount_context_gen_split_bang_comp[where i=True, simplified]

lemmas tycount_context_gen_split_bang_comp_False =
  tycount_context_gen_split_bang_comp[where i=False, simplified]

lemma tycount_context_gen_split_bang:
  assumes
    "K \<turnstile>* G wellformed"
    "ensure_use_bang N C2"
    "new_shareable_constraint K G (remove_use_bang N C1) C2"
  shows
    "K , N \<turnstile> tycount_context_gen G (remove_use_bang N C1 \<oplus> C2) \<leadsto>b
      tycount_context_gen_bang bangL_comp N G (remove_use_bang N C1) | tycount_context_gen_bang bangR_comp N G C2"
  using assms
  by (force simp add:
      tycount_context_gen_split_bang_comp_True
      tycount_context_gen_split_bang_comp_False
      ensure_use_bang_all_nth
      split_bang_conv_all_nth list_all_length new_shareable_constraint_conv_all_nth
      split_bang.simps)

subsubsection \<open> join with sup respects split \<close>

lemma tycount_context_gen_max_split_comp:
  assumes
    "K \<turnstile> t wellformed"
    "new_is_shared K t c1 c2"
  shows
    "K \<turnstile> tycount_context_gen_comp t (sup c1 c2) \<leadsto> tycount_context_gen_comp t c1 \<parallel> tycount_context_gen_comp t c2"
  using assms
  by (force simp add: zero_linearity_def one_linearity_def new_is_shared_def shareable_def
      split_comp.simps tycount_context_gen_comp_def linearity_neq_none_iff)

lemma tycount_context_gen_max_split:
  assumes
    "K \<turnstile>* G wellformed"
    "new_shareable_constraint K G C1 C2"
  shows
    "K \<turnstile> tycount_context_gen G (countMax C1 C2) \<leadsto> tycount_context_gen G C1 | tycount_context_gen G C2"
  using assms
  by (clarsimp simp add: split_conv_all_nth list_all_length
      new_shareable_constraint_conv_all_nth tycount_context_gen_max_split_comp)

subsubsection \<open> join sup can be weakened \<close>

lemma tycount_context_gen_weaken_max_comp:
  assumes
    "K \<turnstile> t wellformed"
    "merge_drop_condition_comp K t c1 c2"
  shows
    "weakening_comp K (tycount_context_gen_comp t (sup c1 c2)) (tycount_context_gen_comp t c1)"
    "weakening_comp K (tycount_context_gen_comp t (sup c1 c2)) (tycount_context_gen_comp t c2)"
  using assms
  by (force simp add:
      tycount_context_gen_comp_def weakening_comp.simps merge_drop_condition_comp_def
      droppable_def zero_linearity_def linearity_none_impl_iff2 linearity_neq_none_iff
      split: if_splits)+

lemma tycount_context_gen_weaken_max:
  assumes
    "K \<turnstile>* G wellformed"
    "merge_drop_condition K G C1 C2"
  shows
    "K \<turnstile> tycount_context_gen G (countMax C1 C2) \<leadsto>w tycount_context_gen G C1"
    "K \<turnstile> tycount_context_gen G (countMax C1 C2) \<leadsto>w tycount_context_gen G C2"
  using assms
  by (fastforce intro: tycount_context_gen_weaken_max_comp
      simp add: list_all_length weakening_conv_all_nth merge_drop_condition_conv_all_nth)+


subsection \<open> Misc Lemmas \<close>


lemmas tyinf_shareable_constraint_plus_iff =
  shareable_constraint_plus_iff[OF trans[OF
      tyinf_context_lengths(1) tyinf_context_lengths(1)[symmetric]]]
  shareable_constraint_plus_iff[OF trans[OF
      tyinf_context_lengths(1) tyinf_context_lengths(2)[symmetric]]]
  shareable_constraint_plus_iff[OF trans[OF
      tyinf_context_lengths(2) tyinf_context_lengths(1)[symmetric]]]
  shareable_constraint_plus_iff[OF trans[OF
      tyinf_context_lengths(1) tyinf_context_lengths(3)[symmetric]]]

  shareable_constraint_plus_iff[OF trans[OF
      tyinf_context_lengths(2) tyinf_context_lengths(2)[symmetric]]]

  shareable_constraint_plus_iff[OF trans[OF
      tyinf_context_lengths(1) tyinf_context_lengths(2)[symmetric,
        where \<Gamma>="x # \<Gamma>" and C="cx # C" for x \<Gamma> cx C, simplified]]]
  shareable_constraint_plus_iff[OF trans[OF
      tyinf_context_lengths(1) tyinf_context_lengths(2)[symmetric,
        where \<Gamma>="x # y # \<Gamma>" and C="cx # cy # C" for x y \<Gamma> cx cy C, simplified]]]

lemmas tyinf_shareable_constraint_max_iff =
  shareable_constraint_max_iff[OF trans[OF tyinf_context_lengths(1) tyinf_context_lengths(1)[symmetric]]]
  shareable_constraint_max_iff[OF trans[OF tyinf_context_lengths(1) tyinf_context_lengths(2)[symmetric]]]
  shareable_constraint_max_iff[OF trans[OF tyinf_context_lengths(2) tyinf_context_lengths(1)[symmetric]]]
  shareable_constraint_max_iff[OF trans[OF tyinf_context_lengths(2) tyinf_context_lengths(2)[symmetric]]]


lemma weakening_context_correspond:
  assumes
    "i < length G"
  shows
    "tycount_context_gen G ((replicate (length G) 0)[i := 1]) = (replicate (length G) None)[i := Some (G ! i)]"
  using assms
  by (auto simp add: tycount_context_gen_comp_def nth_list_update list_eq_iff_nth_eq
      split: linearity.splits)


lemma ite_less_than_one_helper:
  fixes c :: "'a :: zero_less_one"
  shows "(if P then 0 else c) \<le> 1 \<longleftrightarrow> P \<or> \<not>P \<and> c \<le> 1"
  by (clarsimp simp add: order.order_iff_strict split: if_splits)


lemma weaken_context_gen_bangL:
  assumes
    "K \<turnstile>* G wellformed"
  shows
    "K \<turnstile> tycount_context_gen_bang bangL_comp N G (remove_use_bang N C) \<leadsto>w tycount_context_gen (context_bang_types N G) C"
  using assms bang_kinding_fn
  by (force simp add: weakening_conv_all_nth weakening_comp.simps
      context_gen_comp_Some context_gen_comp_None list_all_length)

lemma weaken_context_gen_bangR:
  assumes
    "ensure_use_bang N C"
    "K \<turnstile>* G wellformed"
  shows
    "K \<turnstile> tycount_context_gen_bang bangR_comp N G C \<leadsto>w tycount_context_gen G C"
  using assms
  by (force simp add: list_all_length weakening_conv_all_nth weakening_comp.simps
      context_gen_comp_Some)

lemma wellformed_types_impl_context_gen_wellformed:
  assumes
  "K \<turnstile>* G wellformed"
shows
  "K \<turnstile>* tycount_context_gen G C ctxt-wellformed"
  using assms
  by (simp add: list_all_length tycount_context_gen_comp_def)


section \<open> Main Theorem: An Inferred Typing Implies a Non-Algorithmic Typing \<close>

theorem tyinf_to_typing:
  assumes
    "well_kinded_all K"
    "shareable_constraint K G C"
    "K \<turnstile>* G wellformed"
  shows
  "\<Xi>, K, G, C \<turnstile>\<down> e : t    \<Longrightarrow> \<Xi>, K, tycount_context_gen G C \<turnstile> e : t"
  "\<Xi>, K, G, C \<turnstile>\<up> e : t    \<Longrightarrow> \<Xi>, K, tycount_context_gen G C \<turnstile> e : t"
  "\<Xi>, K, G, C \<turnstile>\<down>* es : ts \<Longrightarrow> \<Xi>, K, tycount_context_gen G C \<turnstile>* es : ts"
  using assms
proof (induct rule: tyinf_synth_tyinf_check_tyinf_all_synth.inducts)
  case tyinf_var then show ?case
    by (force intro!: typing_typing_all.intros 
        simp add: list_all_length Cogent.empty_def weakening_conv_all_nth weakening_comp.simps
        nth_list_update)
next case tyinf_tuple then show ?case
    by (auto
        intro!: typing_typing_all.intros tycount_context_gen_split
        simp add: tyinf_shareable_constraint_plus_iff)
next
  case (tyinf_member \<Xi> K \<Gamma> C e ts s f n t)
  moreover then have
    "K \<turnstile> t wellformed"
    using tyinf_member
    by (force intro: type_wellformed_fstsnd_triple_indexed)
  moreover have
    "D \<in> kinding_fn K (TRecord (ts[f := (n, t, Taken)]) s)"
    using tyinf_member droppable_def by blast
  ultimately show ?case
    by (force intro!: typing_typing_all.intros kinding_kinding_allI wellformed_record_update_wellformed)
next
  case tyinf_put then show ?case
    by (simp add: tyinf_shareable_constraint_plus_iff droppable_def,
        blast intro: typing_typing_all.intros
        tycount_context_gen_split kinding_kinding_allI)
next
  case tyinf_struct then show ?case
    by (force intro!: typing_typing_all.intros simp add: zip_map2)
next
  case tyinf_app then show ?case
    by (fastforce
        intro!: typing_typing_all.intros tycount_context_gen_split kinding_kinding_allI
        simp add: tyinf_shareable_constraint_plus_iff)
next
  case (tyinf_split \<Xi> K \<Gamma> C1 x t u C2o y t' ct cu C2)
  moreover have
    "K \<turnstile> t wellformed"
    "K \<turnstile> u wellformed"
    using tyinf_split
    by (force dest!: tyinf_preserves_wellformed)+
  ultimately show ?case
    apply (clarsimp simp add: shareable_iff_nonlinear droppable_iff_nonlinear
        tyinf_shareable_constraint_plus_iff is_used_def)
    apply (rule typing_typing_all.intros)
      apply (rule tycount_context_gen_split; blast)
     apply blast
    apply (force
        intro: wellformed_types_impl_context_gen_wellformed weakening_refl typing_weaken_context
        simp add: weakens_to_context_gen weakening_Cons)
    done
next
  case (tyinf_fun \<Xi> K' t f u K ts \<Gamma>)
  moreover have
    "is_share_safe K' t 1"
    "K' \<turnstile> t wellformed"
    using tyinf_fun
    by (simp add: is_share_safe_def list_all2_conv_all_nth)+
  ultimately show ?case
    by (force intro!: typing_typing_all.intros simp add: is_consumed_conv_all_nth)
next
  case (tyinf_afun \<Xi> f K' t u K ts \<Gamma>)
  moreover then have
    "K' \<turnstile> t wellformed"
    "K' \<turnstile> u wellformed"
    by (simp add: list_all2_conv_all_nth)+
  ultimately show ?case
    by (force intro!: typing_typing_all.intros simp add: is_consumed_conv_all_nth)
next
  case (tyinf_let \<Xi> K \<Gamma> C1 x t C2o y u ct C2)
  moreover have
    "K \<turnstile> t wellformed"
    using tyinf_let
    by force
  ultimately show ?case
    apply (clarsimp simp add: shareable_iff_nonlinear droppable_iff_nonlinear
        tyinf_shareable_constraint_plus_iff is_used_def)
    apply (rule typing_typing_all.intros)
      apply (rule tycount_context_gen_split; blast)
     apply blast
    apply (force intro!: weakening_cons weakens_to_context_gen
        intro: weakening_refl wellformed_types_impl_context_gen_wellformed typing_weaken_context)
    done
next
  case (tyinf_letb \<Xi> K N \<Gamma> C1 x t C2o y u ct C2)
  moreover have
    "length C1 = length C2"
    using tyinf_letb
    by (force dest!: tyinf_context_lengths)
  moreover then have
    "shareable_constraint K \<Gamma> (remove_use_bang N C1)"
    "shareable_constraint K (context_bang_types N \<Gamma>) C1"
    "shareable_constraint K \<Gamma> C2"
    "is_share_safe K t ct"
    using tyinf_letb
    by (force simp add: shareable_constraint_plus_iff is_used_def
        intro: shareable_context_bang_types_if_shareable_remove_use_bang)+
  moreover have
    "K \<turnstile> t wellformed"
    using tyinf_letb
    by (force simp add: context_bang_types_wellformed_iff)
  ultimately show ?case
    apply (clarsimp simp add: shareable_iff_nonlinear droppable_iff_nonlinear
        tyinf_shareable_constraint_plus_iff context_bang_types_wellformed_iff)
    apply (rule typing_typing_all.intros)
        apply (rule tycount_context_gen_split_bang)
          apply blast
         apply blast
        apply (force simp add: shareable_constraint_plus_iff)
       apply (force intro: typing_weaken_context weaken_context_gen_bangL)
      apply (fastforce intro: typing_weaken_context weakens_to_context_gen weaken_context_gen_bangR
        simp add: weakening_Cons is_used_def)
     apply (force intro: kinding_kinding_allI)+
    done
next
  case (tyinf_case \<Xi> K \<Gamma> C1 x \<tau>1 ts tag t C2ao a u c2a C2a C2bo b c2b C2b)
  moreover have C_lengths: "length C2a = length \<Gamma>" "length C2b = length \<Gamma>" "length C1 = length \<Gamma>"
    using tyinf_case
    by (force dest!: tyinf_context_lengths)+
  moreover then have
    "shareable_constraint K \<Gamma> C1"
    "shareable_constraint K \<Gamma> C2a"
    "shareable_constraint K \<Gamma> C2b"
    "new_shareable_constraint K \<Gamma> C1 (countMax C2a C2b)"
    using tyinf_case.prems
    by (clarsimp simp add: shareable_constraint_plus_iff shareable_constraint_max_iff)+
  moreover have sum_wellformed: "K \<turnstile> TSum ts wellformed"
    using tyinf_case
    by (force dest!: tyinf_preserves_wellformed)
  moreover have "K \<turnstile> t wellformed"
    using tyinf_case sum_wellformed
    by (force dest!: type_wellformed_fstsnd_triple_elem)
  moreover then have
    "K \<turnstile> TSum (tagged_list_update tag (t, Checked) ts) wellformed"
    using tyinf_case sum_wellformed
    by (simp add: type_wellformed_fst_snd_updateI)
  ultimately show ?case
    apply (clarsimp simp add: is_used_def)
    apply (rule typing_typing_all.intros)
        apply (rule tycount_context_gen_split; blast)
           apply blast
        apply blast

     apply (rule typing_weaken_context[OF _ _ weakening_cons], blast, blast)
      apply (fastforce intro: weakens_to_context_gen)
     apply (rule tycount_context_gen_weaken_max(1); blast)

    apply (rule typing_weaken_context[OF _ _ weakening_cons], blast, blast)
     apply (fastforce intro: weakens_to_context_gen)
    apply (rule tycount_context_gen_weaken_max(2); blast)
    done
next
  case (tyinf_if \<Xi> K \<Gamma> C1 x \<tau> C2a a t C2b b)
  moreover have C_lengths: "length C2a = length \<Gamma>" "length C2b = length \<Gamma>" "length C1 = length \<Gamma>"
    using tyinf_if
    by (force dest!: tyinf_context_lengths)+
  moreover then have
    "shareable_constraint K \<Gamma> C1"
    "shareable_constraint K \<Gamma> C2a"
    "shareable_constraint K \<Gamma> C2b"
    "new_shareable_constraint K \<Gamma> C1 (countMax C2a C2b)"
    using tyinf_if.prems
    by (clarsimp simp add: shareable_constraint_plus_iff shareable_constraint_max_iff)+
  ultimately show ?case
    apply clarsimp
    apply (rule typing_typing_all.intros)
       apply (rule tycount_context_gen_split; blast)
      apply blast
     apply (blast intro!: typing_weaken_context tycount_context_gen_weaken_max(1))
    apply (blast intro!: typing_weaken_context tycount_context_gen_weaken_max(2))
    done
next
  case (tyinf_take \<Xi> K \<Gamma> C1 e \<tau>1 ts s f n t taken C2o e' u ct cr C2)
  moreover have record_wellformed:
    "K \<turnstile> TRecord ts s wellformed"
    using tyinf_take
    by blast
  moreover then have
    "K \<turnstile> t wellformed"
    using tyinf_take.hyps(5-6) tyinf_take.prems
    by (force dest: type_wellformed_fstsnd_triple_nth)
  moreover then have
    "K \<turnstile> TRecord (ts[f := (n, t, taken)]) s wellformed"
    using tyinf_take.hyps record_wellformed
    by (metis wellformed_record_update_wellformed prod_eq_iff_proj_eq)
  ultimately show ?case
    apply -
    apply (clarsimp simp add: tyinf_shareable_constraint_plus_iff shareable_def)
    apply (intro typing_typing_all.intros)
           apply (rule tycount_context_gen_split; blast)
          apply blast
         apply blast
        apply blast
       apply blast
      apply (rule kinding_kinding_allI; blast)
     apply assumption
    apply (fastforce intro!: weakening_refl intro: typing_weaken_context weakens_to_context_gen 
        wellformed_types_impl_context_gen_wellformed
        simp add: weakening_Cons is_used_def)
    done
next
  case tyinf_all_cons then show ?case
    by (force
        intro!: typing_typing_all.intros
        tycount_context_gen_split
        simp add: tyinf_shareable_constraint_plus_iff)
qed (auto intro: typing_typing_all.intros
        simp add: list_all_length is_consumed_conv_all_nth weakening_comp_simps2)

lemma all_weakens_to_tycount_gen:
  assumes
    "droppable_constraint K G C"
    "K \<turnstile>* G wellformed"
  shows
    "K \<turnstile> map Some G \<leadsto>w tycount_context_gen G C"
  using assms
  by (force simp add:
      list_all_length weakening_conv_all_nth weakening_comp.simps
      tycount_context_gen_comp_def droppable_constraint_conv_all_nth is_drop_safe_def
      linearity_one_le_eq_one_or_many droppable_def)


lemma tyinf_to_typing_all_present:
  assumes
    "well_kinded_all K"
    "shareable_constraint K G C"
    "droppable_constraint K G C"
    "K \<turnstile>* G wellformed"
  shows
  "\<Xi>, K, G, C \<turnstile>\<down> e : t    \<Longrightarrow> \<Xi>, K, (map Some G) \<turnstile> e : t"
  "\<Xi>, K, G, C \<turnstile>\<up> e : t    \<Longrightarrow> \<Xi>, K, (map Some G) \<turnstile> e : t"
  "\<Xi>, K, G, C \<turnstile>\<down>* es : ts \<Longrightarrow> \<Xi>, K, (map Some G) \<turnstile>* es : ts"
  using assms
  by (force intro: all_weakens_to_tycount_gen typing_weaken_context tyinf_to_typing)+


section \<open> Type Inference Tactic \<close>

(* Obviously true, but ensures C' and t' are schematic *)
lemma tyinf_inferI:
  "\<lbrakk> \<Xi>, K, \<Gamma>, C' \<turnstile>\<down> e : t'
   ; C = C'
   ; t = t'
   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> e : t"
  by fast

(* Obviously true, but ensures C' is schematic *)
lemma tyinf_checkI:
  "\<lbrakk> \<Xi>, K, \<Gamma>, C' \<turnstile>\<up> e : t
   ; C = C'
   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<up> e : t"
  by fast

ML \<open>
fun trace_tac ctxt (st : thm) = print_tac ctxt (@{make_string} st) st;
fun trace_tac' ctxt  _ = trace_tac ctxt;
fun typinfer_tac_N (n : int) (ctxt : Proof.context) (fn_thms : thm list) : tactic =
  let val tac = (resolve_tac ctxt fn_thms ORELSE'
                 resolve_tac ctxt @{thms tyinf_safe_intros} ORELSE'
                 fast_force_tac (ctxt addsimps @{thms kinding_simps is_used_def is_share_safe_def subtyping_simps is_drop_safe_def}));
   in REPEAT_DETERM_N n (FIRSTGOAL tac)
   end;
fun typinfer_tac ctxt fn_thms = typinfer_tac_N ~1 ctxt fn_thms;
\<close>

definition
  ty1 :: " Cogent.type"
where
  "ty1 \<equiv> TRecord [(''b'', (TPrim (Num U8), Present)), (''a'', (TPrim (Num U32), Present))] Unboxed"

definition
  expr1 :: "string Cogent.expr"
where
  "expr1 \<equiv> Take (Var 0) 0 (Take (Var 1) 1 (Struct [''b'',''a''] [TPrim (Num U8), TPrim (Num U32)] [Var 2, Var 0]))"

schematic_goal typing1: "\<Xi>, [], [ty1], ?C \<turnstile>\<up> expr1 : ty1"
  apply (unfold expr1_def ty1_def)
  apply (tactic \<open>typinfer_tac @{context} []\<close>)
  done
thm typing1[simplified]

definition
  ty2a :: "Cogent.type"
where
  "ty2a \<equiv> TRecord
            [ (''a'', TCon ''A'' [] (Boxed Writable undefined), Present)
            , (''b'', TCon ''A'' [] (Boxed Writable undefined), Taken)]
            Unboxed"

definition
  ty2b :: "Cogent.type"
where
  "ty2b \<equiv> TRecord
            [ (''a'', TCon ''A'' [] (Boxed Writable undefined), Taken)
            , (''b'', TCon ''A'' [] (Boxed Writable undefined), Present)]
            Unboxed"

definition
  expr2 :: "string Cogent.expr"
where
  "expr2 \<equiv> Take (Var 0) 0 (Put (Var 1) 1 (Var 0))"

schematic_goal typing2: "\<Xi>, [], [ty2a], ?C \<turnstile>\<up> expr2 : ty2b"
  unfolding expr2_def ty2a_def ty2b_def
  apply clarsimp
  apply (tactic \<open>typinfer_tac @{context} []\<close>)
  done
thm typing2[simplified]

schematic_goal typing3:
  "\<exists>ts. \<Xi>, [], [TCon ''A'' [] (Boxed Writable undefined)], ?C \<turnstile>\<down> Struct [''a'',''b''] ts [Var 0, Var 0] : ?t"
  apply (rule exI)
  apply (tactic \<open>typinfer_tac @{context} []\<close>)
  done
thm typing3[simplified]


end
