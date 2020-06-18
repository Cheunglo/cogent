theory Manual_AllRefine
  imports Generated_AllRefine
begin


thm  Generated_cogent_shallow.corres_shallow_C_wordarray_put2_u32[no_vars]


overloading
  valRel_WordArrayU32 \<equiv> valRel
begin
  definition valRel_WordArrayU32: 
    "\<And>\<xi> x v. valRel_WordArrayU32 (\<xi> :: (funtyp,vabstyp) vabsfuns) (x :: (32 word) WordArray) (v :: (funtyp, vabstyp) vval) \<equiv> 
      \<exists>xs. v = VAbstract (VWA xs) \<and> length x = length xs \<and> (\<forall>i < length xs. xs ! i = VPrim (LU32 (x ! i)))"
end

overloading
  wordarray_put2' \<equiv> wordarray_put2
begin
definition wordarray_put2':
 "wordarray_put2' (x :: ('a WordArray, 32 word, 'a) WordArrayPutP) \<equiv> (WordArrayPutP.arr\<^sub>f x)[unat (WordArrayPutP.idx\<^sub>f x) := WordArrayPutP.val\<^sub>f x]" 
end
thm wordarray_put2'

thm valRel_WordArrayU32

definition \<xi>0 :: "(char list, atyp, 32 word) uabsfuns" 
  where
  "\<xi>0 x y z = 
      (let (y1, y2) = y;
           (z1, z2) = z
      in
           (if x = ''wordarray_put2_0'' then
                (case y2 of 
                      URecord [(UPtr p r, _), 
                            (UPrim (LU32 idx), _ ), (UPrim (LU32 val), _)] 
                        \<Rightarrow> (\<lambda>l. (case y1 p of option.Some (UAbstract (WAU32 len arr))
                                      \<Rightarrow> (if l = arr + 4 * idx \<and> idx < len 
                                            then option.Some (UPrim (LU32 val)) else y1 l)
                                  | _ \<Rightarrow> y1 l)) = z1 \<and> 
                            UPtr p r = z2
                    | _ \<Rightarrow> False)
           else False))" 

definition \<xi>m :: "(char list, vatyp) vabsfuns" 
  where
  "\<xi>m x y z = (if x = ''wordarray_put2_0'' then
                (case y of 
                      VRecord [VAbstract (VWA xs), 
                            VPrim (LU32 idx), VPrim (LU32 val)] 
                        \<Rightarrow> VAbstract (VWA (xs[unat idx := VPrim (LU32 val)])) = z
                    | _ \<Rightarrow> False)
           else False)" 


definition \<xi>p :: "(char list, vatyp) vabsfuns" 
  where
  "\<xi>p x y z = (if x = ''wordarray_put2'' then
                (case y of 
                      VRecord [VAbstract (VWA xs), 
                            VPrim (LU32 idx), VPrim (LU32 val)] 
                        \<Rightarrow> VAbstract (VWA (xs[unat idx := VPrim (LU32 val)])) = z
                    | _ \<Rightarrow> False)
           else False)" 



lemma word_mult_cancel_left: 
  fixes a b c :: "('a::len) word"
  assumes "0 \<le> a" "0 \<le> b" "0 \<le> c"
  assumes "uint c * uint a \<le> uint (max_word :: ('a::len) word)"
  assumes "uint c * uint b \<le> uint (max_word :: ('a::len) word)"
  shows "c * a = c * b \<longleftrightarrow> c = 0 \<or> a = b"
  apply (rule iffI)
   using assms
   apply (unfold word_mult_def word_of_int_def)
    apply (clarsimp simp:Abs_word_inject max_word_def uint_word_of_int m1mod2k uint_0_iff )
   apply fastforce
   done

locale WordArray = main_pp_inferred begin
  definition "abs_repr_u a \<equiv> case a of
      WAU32 _ _ \<Rightarrow> (''WordArray'', [RPrim (Num U32)])
    | _ \<Rightarrow> (''Unknown Abstract Type'', [])"

  definition "abs_typing_u a name \<tau>s sig (r :: ptrtyp set) (w :: ptrtyp set) \<sigma> \<equiv>
    (case a of
      WAU32 len arr \<Rightarrow> name = ''WordArray'' \<and> \<tau>s = [TPrim (Num U32)] \<and> sig \<noteq> Unboxed \<and>
                      (sigil_perm sig = option.Some ReadOnly \<longrightarrow> w = {} \<and> r = {arr + 4 * i | i. i < len}) \<and>
                      (sigil_perm sig = option.Some Writable \<longrightarrow> r = {} \<and> w = {arr + 4 * i | i. i < len}) \<and>
                      (\<forall>i < len. \<exists>x. \<sigma>(arr + 4 * i) = option.Some (UPrim (LU32 x))) \<and> 4 * unat len \<le> unat (max_word :: ptrtyp)
    | _ \<Rightarrow> name = ''Unknown Abstract Type'' \<and> \<tau>s = [] \<and> r = {} \<and> w = {} \<and> sig = Unboxed)"

  definition "abs_typing_v a name \<tau>s \<equiv>
    (case a of
      VWA xs \<Rightarrow> name = ''WordArray'' \<and> \<tau>s = [TPrim (Num U32)] \<and> (\<forall>i < length xs. \<exists>x. xs ! i = VPrim (LU32 x))
    | _ \<Rightarrow> name = ''Unknown Abstract Type'' \<and> \<tau>s = [])"

  definition  "abs_upd_val' au av name \<tau>s sig (r :: ptrtyp set) (w :: ptrtyp set) \<sigma> \<equiv>
    abs_typing_u au name \<tau>s sig r w \<sigma> \<and> abs_typing_v av name \<tau>s \<and>
    (case au of
      WAU32 len arr \<Rightarrow>
        (case av of 
          VWA xs \<Rightarrow> unat len = length xs \<and> 
                      (\<forall>i < len. \<exists>x. \<sigma>(arr + 4 * i) = option.Some (UPrim (LU32 x)) \<and> 
                                     xs ! (unat i) = VPrim (LU32 x))
          | _ \<Rightarrow> False)
      | _ \<Rightarrow> (case av of
                VTOther _ \<Rightarrow> True
             |  _ \<Rightarrow> False))"

lemma distinct_indices:
  "abs_typing_u (WAU32 len arr) n ts s r w \<sigma> \<Longrightarrow> \<forall>i < len. \<forall>j < len. i = j \<longleftrightarrow> 4 * i = 4 * j"
  apply clarsimp
  apply (rule iffI)
   apply (clarsimp simp: abs_typing_u_def)
  apply (clarsimp simp: abs_typing_u_def)
  apply (subgoal_tac "0 \<le> i")
   apply (frule_tac b = j and c = 4 in word_mult_cancel_left; clarsimp simp: uint_nat)
    apply (subgoal_tac "int (unat i) < int (unat len)")
     apply linarith
    apply (simp add: unat_mono)
   apply (subgoal_tac "int (unat j) < int (unat len)")
    apply linarith
   apply (simp add: unat_mono)
  apply simp
  done      
end

sublocale WordArray \<subseteq> Generated_cogent_shallow _ abs_repr_u abs_typing_v abs_typing_u abs_upd_val'
  apply (unfold abs_repr_u_def[abs_def] abs_typing_v_def[abs_def] abs_typing_u_def[abs_def] abs_upd_val'_def[abs_def])
  apply (unfold_locales; clarsimp split: vatyp.splits atyp.splits)
          apply (case_tac s; clarsimp; case_tac x11a; clarsimp)
         apply (case_tac s; clarsimp; case_tac x11a; clarsimp)
        apply (case_tac s; clarsimp; case_tac x11a; clarsimp)
       apply (case_tac s; clarsimp; case_tac x11a; clarsimp)
      apply (case_tac s; clarsimp; case_tac x11a; clarsimp; erule_tac x = i in allE; clarsimp)
     apply (case_tac s, (case_tac s', simp_all)+)[]
    apply (unfold UpdateSemantics.frame_def)
    apply (erule_tac x = "x12 + 4 * i" in allE; clarsimp)
    apply (erule_tac x = i in allE; clarsimp)
    apply (rule_tac x = x in exI)
    apply (case_tac s; clarsimp; case_tac x11a; clarsimp;
           drule_tac x = "x12 + 4 * i" in orthD1; simp; rule_tac x = i in exI; simp)
   apply (case_tac s; clarsimp; case_tac x11a; clarsimp)
  apply (case_tac s; clarsimp; case_tac x11a; clarsimp)
   apply (rule conjI; clarsimp; erule_tac x = "x12 + 4 * i" in allE; clarsimp)
    apply (erule_tac x = i in allE; clarsimp)
    apply (rule_tac x = x in exI)
    apply auto[1]
   apply (erule_tac x = i in allE; clarsimp)
   apply auto[1]
  apply (rule conjI; clarsimp; erule_tac x = "x12 + 4 * i" in allE; clarsimp)
    apply (erule_tac x = i in allE; clarsimp)
    apply (rule_tac x = x in exI)
    apply auto[1]
   apply (erule_tac x = i in allE; clarsimp)
   apply auto[1]
  done

context WordArray begin

section "Prove Correspondence From Isabelle Shallow Embedding to C"

theorem shallow_C_wordarray_put2_corres:
"\<lbrakk>\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd wordarray_put2_0_type))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_put2_0'' []) (Var i))
         (do x <- wordarray_put2_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma>
         (assoc_lookup
           [(''wordarray_put2_0'', wordarray_put2_0_type), (''wordarray_put2_u32'', Generated_TypeProof.wordarray_put2_u32_type)]
           ([], TUnit, TUnit))
         \<Gamma>' \<sigma> st;
 
 value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>m \<xi>p; vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C abs_repr_u abs_upd_val' rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
 value_sem.proc_env_matches abs_typing_v \<xi>m \<Xi>;
 value_sem.matches abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C abs_repr_u abs_typing_u abs_upd_val' rename (Generated.state_rel abs_repr_u)
     (Generated_Shallow_Desugar.wordarray_put2_u32 vv\<^sub>s) Generated_TypeProof.wordarray_put2_u32 (wordarray_put2_u32' uv\<^sub>C) \<xi>0 \<xi>m \<xi>p
     [uv\<^sub>m] [vv\<^sub>m] \<Xi> [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))] \<sigma> s"
  apply clarsimp
  apply (subgoal_tac "\<exists>arr idx val. vv\<^sub>s = \<lparr>WordArrayPutP.arr\<^sub>f = arr, idx\<^sub>f = idx, val\<^sub>f = val\<rparr>")
   prefer 2
   apply (case_tac vv\<^sub>s; clarsimp)
  apply clarsimp
  apply (subgoal_tac "\<exists>arrv. vv\<^sub>p = VRecord [VAbstract (VWA arrv), VPrim (LU32 idx), VPrim (LU32 val)]")
   prefer 2
   apply (clarsimp simp: val_rel_shallow_C_def valRel_WordArrayPutP valRel_WordArrayU32)
  apply clarsimp
  apply (drule_tac x = 0 in meta_spec)
  apply (drule_tac x = "[uv\<^sub>m]" in meta_spec)
  apply (drule_tac x = uv\<^sub>C in meta_spec)
  apply (drule_tac x = "[option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]" in meta_spec)
  apply (drule_tac x = \<sigma> in meta_spec)
  apply (drule_tac x = s in meta_spec)
  apply (clarsimp simp:  corres_shallow_C_def)
  apply (monad_eq simp: wordarray_put2_u32'_def)
  apply (drule meta_mp)
   apply (drule val_rel_shallow_C_elim(3); simp)
  apply (drule meta_mp)
   apply (clarsimp simp: Generated_TypeProof.wordarray_put2_u32_type_def 
                         Generated_TypeProof.abbreviatedType1_def 
                         wordarray_put2_0_type_def)
  apply (clarsimp simp: corres_def)
  apply (erule impE)
   apply (clarsimp simp: \<Xi>_def)
  apply (erule impE)
   apply (clarsimp simp: \<Xi>_def)
  apply (erule impE)
   apply (rule_tac x = r in exI)
   apply (rule_tac x = x in exI)
   apply (frule u_v_matches_to_matches_ptrs)
   apply (clarsimp simp: \<Xi>_def
                         Generated_TypeProof.wordarray_put2_u32_type_def 
                         Generated_TypeProof.abbreviatedType1_def 
                         wordarray_put2_0_type_def)
  apply clarsimp
  apply (erule_tac x = r' in allE)
  apply (erule_tac x = s' in allE)
  apply clarsimp
  apply (rule_tac x = \<sigma>' in exI)
  apply (rule_tac x = ra in exI)
  apply (clarsimp simp: Generated_TypeProof.wordarray_put2_u32_def)
  apply (rule conjI)
   apply (rule_tac \<sigma>' = \<sigma> and a' = uv\<^sub>m in u_sem_let)
    apply (rule u_sem_var[where i = 0 and \<gamma> = "[_]", simplified])
   apply (rule u_sem_abs_app)
     apply (rule u_sem_afun)
    apply (rule u_sem_var)
   apply (erule u_sem_appE; clarsimp)
    apply (erule u_sem_afunE; clarsimp)
    apply (erule u_sem_varE; clarsimp)
   apply (erule u_sem_afunE; clarsimp)
  apply (rule_tac x = "VAbstract (VWA (arrv[unat idx := VPrim (LU32 val)]))" in exI)
  apply clarsimp
  apply (rule conjI)
   apply (rule v_sem_let)
    apply (rule v_sem_var)
   apply (rule v_sem_abs_app)
     apply (rule v_sem_afun)
    apply (rule v_sem_var)
   apply (clarsimp simp: \<xi>m_def)
  apply (clarsimp simp: Generated_Shallow_Desugar.wordarray_put2_u32_def wordarray_put2')
  apply (subst val_rel_shallow_C_def)
  apply (clarsimp simp: valRel_WordArrayPutP valRel_WordArrayU32)
  apply (rule conjI)
   apply (drule val_rel_shallow_C_elim(1))
   apply (clarsimp simp: valRel_WordArrayPutP valRel_WordArrayU32)
  apply (rule conjI)
   apply (drule val_rel_shallow_C_elim(1))
   apply (clarsimp simp: valRel_WordArrayPutP valRel_WordArrayU32)
   apply (erule_tac x = i in allE)
   apply clarsimp
   apply (case_tac "i = unat idx"; clarsimp)
  apply (frule_tac i = 0 and 
                   \<tau> = "(prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))" 
                       in u_v_matches_proj_single')
    apply simp
   apply simp
  apply clarsimp
  apply (frule val_rel_shallow_C_elim(3); clarsimp simp: val_rel_simp)
  apply (erule u_v_recE)
  apply (erule u_v_r_consE; clarsimp simp: Generated_TypeProof.wordarray_put2_u32_type_def abbreviatedType1_def)
  apply (erule u_v_r_consE; clarsimp)+
  apply (erule u_v_r_emptyE; clarsimp)
  apply (erule u_v_primE)+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (erule u_v_p_absE; clarsimp)
  apply (erule u_sem_appE; erule u_sem_afunE; clarsimp)
  apply (erule u_sem_varE; clarsimp)
  apply (rule_tac x = "TCon ''WordArray'' [TPrim (Num U32)] (Boxed Writable undefined)" in exI)
  apply (rule_tac x = ra in exI)
  apply (rule_tac x = "insert (ptr_val (arr_C uv\<^sub>C)) wa" in exI)
  apply (clarsimp simp: \<xi>0_def)
  apply (rule_tac ptrl = undefined and a = a in u_v_p_abs_w[where ts = "[TPrim (Num U32)]", simplified])
     apply simp
    apply (clarsimp simp: abs_upd_val'_def)
    apply (case_tac a; clarsimp)
    apply (rule conjI)
     apply (clarsimp simp: abs_typing_u_def)
    apply (rule conjI)
     apply (clarsimp simp: abs_typing_v_def)
     apply (erule_tac x = i in allE)
     apply clarsimp
     apply (case_tac "i = unat (idx_C uv\<^sub>C)"; clarsimp)
    apply clarsimp
    apply (rule conjI; clarsimp)
     apply (drule distinct_indices)
     apply (erule_tac x = i in allE)+
     apply clarsimp
     apply (erule_tac x = "idx_C uv\<^sub>C" in allE)
     apply (cut_tac a = "idx_C uv\<^sub>C" and b = x11 in unat_mono; clarsimp)
    apply (erule_tac x = i in allE)
    apply clarsimp
    apply (case_tac "unat i = unat (idx_C uv\<^sub>C)"; clarsimp)
   apply (clarsimp simp: abs_upd_val'_def)
   apply (case_tac a; clarsimp simp: abs_typing_u_def)
  apply clarsimp
  done

section "Sanity Checks"

lemma value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m_\<xi>p: 
  "value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>m \<xi>p"
  apply (clarsimp simp: rename_def \<Xi>_def \<xi>m_def \<xi>p_def val.rename_mono_prog_def)
  apply (rule conjI)
   apply clarsimp
   apply (case_tac v; clarsimp)
   apply (case_tac x4; clarsimp)
   apply (case_tac a; clarsimp)
   apply (case_tac list; clarsimp)
    apply (case_tac x5; clarsimp)
   apply (case_tac x5; clarsimp)
   apply (case_tac a; clarsimp)
   apply (case_tac x1a; clarsimp)
   apply (case_tac lista; clarsimp)
   apply (case_tac list; clarsimp)
    apply (case_tac a; clarsimp)
    apply (case_tac x1a; clarsimp)
   apply (case_tac a; clarsimp)
   apply (case_tac x1a; clarsimp)
  apply (case_tac ts; clarsimp)
  apply (case_tac list; clarsimp)
  apply (case_tac a; clarsimp)
  apply (case_tac x5; clarsimp)
  apply (case_tac x1; clarsimp)
  apply (case_tac "f = ''wordarray_put2''"; clarsimp)
  done

lemma val_proc_env_matches_\<xi>m_\<Xi>:
  "val.proc_env_matches \<xi>m \<Xi>"
  apply (clarsimp simp: val.proc_env_matches_def \<Xi>_def)
  apply (case_tac "f = ''wordarray_put2_0''")
   defer
   apply (case_tac "f = ''wordarray_put2_u32''")
    apply (clarsimp simp: \<xi>m_def)
   apply (rule FalseE)
   apply (clarsimp simp: \<xi>m_def)
  apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType1_def \<xi>m_def)
  apply (case_tac v; clarsimp)
  apply (case_tac x4; clarsimp)
  apply (case_tac a; clarsimp)
  apply (case_tac x5; clarsimp)
  apply (case_tac list; clarsimp)
  apply (case_tac a; clarsimp)
  apply (case_tac x1a; clarsimp)
  apply (case_tac lista; clarsimp)
  apply (case_tac a; clarsimp)
  apply (case_tac x1a; clarsimp)
  apply (case_tac list; clarsimp)
  apply (erule val.v_t_recordE)
  apply (erule val.v_t_r_consE; clarsimp)
  apply (rule val.v_t_abstract)
   apply (erule val.v_t_abstractE)
   apply (clarsimp simp: abs_typing_v_def)
   apply (erule_tac x = i in allE; clarsimp)
   apply (case_tac "i = unat x4")
    apply (rule_tac x = x4a in exI; simp)
   apply (rule_tac x = x in exI; simp)
  apply simp
  done

lemma proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>:
  "proc_env_u_v_matches \<xi>0 \<xi>m \<Xi>"
  apply (clarsimp simp: proc_env_u_v_matches_def)
  apply (clarsimp simp: \<Xi>_def)
  apply (case_tac "f = ''wordarray_put2_0''")
   prefer 2
   apply (case_tac "f = ''wordarray_put2_u32''"; clarsimp simp: \<xi>0_def)
  apply clarsimp
  apply (subst (asm) wordarray_put2_0_type_def)
  apply clarsimp
  apply (clarsimp simp: \<xi>0_def)
  apply (case_tac aa; clarsimp)
  apply (case_tac x4; clarsimp)
  apply (case_tac a; clarsimp)
  apply (case_tac list; clarsimp)
  apply (case_tac a; clarsimp)
  apply (case_tac x1; clarsimp)
  apply (case_tac lista; clarsimp)
  apply (case_tac a; clarsimp)
  apply (case_tac x1; clarsimp)
  apply (case_tac list; clarsimp)
  apply (clarsimp simp: wordarray_put2_u32_type_def abbreviatedType1_def)
  apply (erule u_v_recE')
  apply clarsimp
  apply (erule u_v_r_consE'; clarsimp)+
  apply (erule u_v_r_emptyE')
  apply clarsimp
  apply (erule u_v_primE')+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (erule u_v_p_absE'; clarsimp)
  apply (case_tac a)
   prefer 2
   apply (clarsimp simp: abs_upd_val'_def abs_typing_u_def)
  apply clarsimp
  apply (case_tac a')
   prefer 2
   apply (clarsimp simp: abs_upd_val'_def)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x = ra in exI)
   apply (rule_tac x = "insert x91 w" in exI)
   apply (clarsimp simp: \<xi>m_def)
   apply (rule conjI)
    apply (rule_tac a = "WAU32 x11 x12" and 
                 ptrl = undefined in u_v_p_abs_w[where ts = "[TPrim (Num U32)]", simplified])
       apply simp
      apply (clarsimp simp: abs_upd_val'_def)
      apply (rule conjI)
       apply (clarsimp simp: abs_typing_u_def)
      apply (rule conjI)
       apply (clarsimp simp: abs_typing_v_def)
       apply (erule_tac x = i in allE; clarsimp)
       apply (case_tac "i = unat x4"; clarsimp)
      apply clarsimp
      apply (rule conjI)
       apply clarsimp
       apply (drule distinct_indices)
       apply (erule_tac x = i in allE)
       apply (erule_tac x = i in allE)
       apply clarsimp
       apply (erule_tac x = x4 in allE)
       apply clarsimp
       apply (cut_tac a = x4  and b = x11 in unat_mono; simp)
      apply clarsimp
      apply (erule_tac x = i in allE; clarsimp)
      apply (case_tac "unat i = unat x4"; clarsimp)
     apply (clarsimp simp: abs_upd_val'_def)
     apply (erule_tac x = x4 in allE)
     apply clarsimp
    apply clarsimp
   apply (clarsimp simp: frame_def)
   apply (rule conjI; clarsimp)
    apply (rule conjI)
     apply clarsimp
    apply (rule conjI; clarsimp)
    apply (clarsimp simp: abs_upd_val'_def abs_typing_u_def)
   apply (rule conjI; clarsimp)
  apply (rule_tac x = "VAbstract (VWA (x1[unat x4 := VPrim (LU32 x4a)]))" in exI)
  apply (clarsimp simp: \<xi>m_def)
  done

lemma upd_proc_env_matches_ptrs_\<xi>0_\<Xi>:
  "upd.proc_env_matches_ptrs \<xi>0 \<Xi>"
  apply (unfold upd.proc_env_matches_ptrs_def)
  apply clarsimp
  apply (subst (asm) \<Xi>_def)
  apply (case_tac  "f = ''wordarray_put2_0''")
   apply clarsimp
   apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType1_def)
   apply (clarsimp simp:  \<Xi>_def)
   apply (case_tac v; clarsimp simp: \<xi>0_def)
   apply (case_tac x4; clarsimp)
   apply (case_tac a; clarsimp)
   apply (case_tac list; clarsimp)
   apply (case_tac a; clarsimp)
   apply (case_tac x1; clarsimp)
   apply (case_tac lista; clarsimp)
   apply (case_tac a; clarsimp)
   apply (case_tac x1; clarsimp)
   apply (case_tac list; clarsimp)
   apply (erule upd.u_t_recE; clarsimp)
   apply (erule upd.u_t_r_consE; clarsimp)+
   apply (erule upd.u_t_p_absE; clarsimp)
   apply (erule upd.u_t_primE)+
   apply (subst (asm) lit_type.simps)+
   apply (erule upd.u_t_r_emptyE)
   apply clarsimp
  apply (rename_tac p i v r av w)
   apply (case_tac av; clarsimp)
   apply (rule_tac x = r in exI)
    apply (rule_tac x = "insert p w" in exI)
    apply (rule conjI)
     apply (rename_tac len arr)
     apply (rule_tac ptrl = undefined and a = "WAU32 len arr" in upd.u_t_p_abs_w[where ts = "[TPrim (Num U32)]", simplified])
        apply simp
       apply (clarsimp simp: abs_typing_u_def)
      apply (clarsimp simp: abs_typing_u_def)
     apply clarsimp
    apply (clarsimp simp: frame_def abs_typing_u_def)
    apply (rule conjI; clarsimp)
     apply (rule conjI)
      apply (rule disjI2)
      apply (rule disjI2)
      apply (rule_tac x = i in exI; simp)
     apply (rule conjI; clarsimp)
    apply (rule conjI; clarsimp)
   apply (clarsimp simp: abs_typing_u_def)
  apply (case_tac  "f = ''wordarray_put2_u32''")
   apply (clarsimp simp: wordarray_put2_u32_type_def abbreviatedType1_def \<xi>0_def)
  apply (clarsimp simp: \<xi>0_def)
  done


lemma proc_ctx_wellformed_\<Xi>:
  "proc_ctx_wellformed \<Xi>"
  apply (clarsimp simp: proc_ctx_wellformed_def \<Xi>_def)
  apply (case_tac "f = ''wordarray_put2_0''"; clarsimp)
   apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType1_def)
  apply (case_tac "f = ''wordarray_put2_u32''"; clarsimp)
  apply (clarsimp simp: wordarray_put2_u32_type_def abbreviatedType1_def)
  done


lemma upd_C_wordarray_put2_corres:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd wordarray_put2_0_type))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_put2_0'' []) (Var i))
         (do x <- wordarray_put2_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma>
         (assoc_lookup
           [(''wordarray_put2_0'', wordarray_put2_0_type), (''wordarray_put2_u32'', Generated_TypeProof.wordarray_put2_u32_type)]
           ([], TUnit, TUnit))
         \<Gamma>' \<sigma> st"
  apply (rule afun_corres; simp)
  apply (clarsimp simp: abs_rel_def; rename_tac r w)
  apply (thin_tac "i < length \<gamma>")
  apply (thin_tac "val_rel (\<gamma> ! i) v'")
  apply (thin_tac "\<Gamma>' ! i = option.Some (prod.fst (prod.snd wordarray_put2_0_type))")
  apply (clarsimp simp: val_rel_simp wordarray_put2_0_type_def abbreviatedType1_def)
  apply (erule upd.u_t_recE)
  apply (erule upd.u_t_r_consE; clarsimp)+
  apply (erule upd.u_t_primE)+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (erule upd.u_t_r_emptyE)
  apply (erule upd.u_t_p_absE; clarsimp simp: abs_typing_u_def)
  apply (case_tac a; clarsimp)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_put2_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def)
   apply (erule_tac x = "arr_C x'" in allE)
   apply (erule_tac x = "values_C (heap_WordArray_u32_C st (arr_C x')) +\<^sub>p uint (idx_C x')" in allE)
   apply (clarsimp simp: heap_rel_ptr_def heap_rel_ptr_w32_def abs_repr_u_def is_valid_simp type_rel_simp)
   apply (erule_tac x = "idx_C x'" in allE)+
   apply (clarsimp simp: val_rel_simp heap_simp type_rel_simp)
  apply clarsimp
  apply (rule_tac x = "\<lambda>l. (case (\<sigma> \<circ> ptr_val \<circ> arr_C) x' of 
                                option.Some (UAbstract (WAU32 len arr)) \<Rightarrow>
                                      (if l = arr + 4 * idx_C x' \<and> idx_C x' < len 
                                          then option.Some (UPrim (LU32 (val_C x'))) 
                                      else \<sigma> l)
                              | _  \<Rightarrow> \<sigma> l)" in exI)
  apply (rule_tac x = "UPtr (ptr_val y') (RCon ''WordArray'' [RPrim (Num U32)])" in exI)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_put2_0'_def \<xi>0_def)
  apply (rule conjI)
   apply (rule_tac x = "RCon ''WordArray'' [RPrim (Num U32)]" in exI, simp)
  apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta heap_rel_ptr_w32_meta)
  apply (rule conjI)
   apply (clarsimp simp: heap_rel_meta_def)
   apply (rule conjI; clarsimp)
    apply (clarsimp simp: type_rel_simp)
   apply (monad_eq simp: wordarray_put2_0'_def)
   apply (case_tac "idx_C x' < SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C st (arr_C x')))"; 
          drule_tac p = x and uv = uv in all_heap_rel_ptrD; clarsimp simp: is_valid_simp heap_simp)
  apply (erule_tac x = "arr_C x'" in allE)
  apply (clarsimp simp: heap_rel_meta_def abs_repr_u_def type_rel_simp val_rel_simp)
  apply (monad_eq simp: wordarray_put2_0'_def heap_simp is_valid_simp)
  apply (rule conjI; clarsimp)
   apply (drule_tac p = "values_C (heap_WordArray_u32_C st (arr_C x')) +\<^sub>p uint (idx_C x')" and 
                   uv = uv in all_heap_rel_ptrD; clarsimp simp: type_rel_simp val_rel_simp)
  apply (rule conjI)
   apply (clarsimp simp: ptr_add_def)
   apply (metis Ptr_ptr_val mult.commute)
  apply clarsimp
  apply (case_tac "idx_C x' < SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C st (arr_C x')))";
         drule_tac p = x and uv = uv in all_heap_rel_ptrD; clarsimp simp: type_rel_simp val_rel_simp)
  done

(*
lemma value_matches_assm: 
  "\<lbrakk>valRel \<xi>p (arr :: (32 word) WordArray) (VAbstract (VWA arrv))\<rbrakk> \<Longrightarrow>
    val.matches \<Xi> [VRecord [VAbstract (VWA arrv), VPrim (LU32 (idx :: 32 word)), VPrim (LU32 (val :: 32 word))]]
    [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]"
  apply (clarsimp simp: val.matches_def Generated_TypeProof.wordarray_put2_u32_type_def Generated_TypeProof.abbreviatedType1_def)
  apply (rule val.v_t_record)
   apply (rule val.v_t_r_cons1)
    apply (rule val.v_t_abstract)
     apply (clarsimp simp: abs_typing_v_def valRel_WordArrayU32)
    apply fastforce
   apply (rule val.v_t_r_cons1)
    apply auto[1]
   apply (rule val.v_t_r_cons1)
    apply auto[1]
   apply (rule val.v_t_r_empty)
  apply auto
  done


lemma 
  "\<lbrakk>\<sigma> p = option.Some (UAbstract (WAU32 len arr)); 4 * unat len \<le> unat (max_word :: ptrtyp); 
    \<forall>i < len. \<exists>x. \<sigma>(arr + 4 * i) = option.Some (UPrim (LU32 x));
    u = URecord [(UPtr p (RCon ''WordArray'' [RPrim (Num U32)]), RPtr (RCon ''WordArray'' [RPrim (Num U32)])),
            (UPrim (LU32 idx), RPrim (Num U32)), (UPrim (LU32 val), RPrim (Num U32))];
    v = VRecord [VAbstract (VWA arrv), VPrim (LU32 idx), VPrim (LU32 val)]\<rbrakk> 
  \<Longrightarrow>  u_v_matches \<Xi> \<sigma> [u] [v] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))] {} 
       (insert p {arr + 4 * i | i. i < len})"
  apply (insert u_v_matches_some[of \<Xi> \<sigma> u v 
                                    "prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type)"
                                    "{}" "(insert p {arr + 4 * i |i. i < len})" "[]" "[]" "[]" "{}" "{}"])
  apply (drule meta_mp)
   apply (clarsimp simp: wordarray_put2_u32_type_def abbreviatedType1_def)
   apply (rule u_v_struct)
    apply (rule u_v_r_cons1[of \<Xi> \<sigma> "UPtr p (RCon ''WordArray'' [RPrim (Num U32)])" 
                                 "VAbstract (VWA arrv)" 
                                 "TCon ''WordArray'' [TPrim (Num U32)] (Boxed Writable undefined)"
                                 "{}" "(insert p {arr + 4 * i |i. i < len})" 
                                 "[(UPrim (LU32 idx), RPrim (Num U32)), (UPrim (LU32 val), RPrim (Num U32))]" 
                                 "[VPrim (LU32 idx), VPrim (LU32 val)]" 
                                 "[(''idx'', TPrim (Num U32), Present),(''val'', TPrim (Num U32), Present)]"
                                 "{}" "{}" "RPtr (RCon ''WordArray'' [RPrim (Num U32)])" "''arr''", simplified])
     apply (rule_tac ptrl = undefined and a = "WAU32 len arr" in u_v_p_abs_w[where ts = "[TPrim (Num U32)]", simplified])
        apply simp
       apply (clarsimp simp: abs_upd_val'_def)
       apply (rule conjI)
        apply (clarsimp simp: abs_typing_u_def)
       apply (rule conjI)
        apply (clarsimp simp: abs_typing_v_def)
        defer
        defer
        apply simp
       apply clarsimp
       apply (erule_tac x = i in allE)
       apply clarsimp
      prefer 2
      apply simp
     prefer 2
     apply clarsimp
     apply (drule meta_mp)
      apply (rule u_v_matches_empty[where \<tau>s = "[]", simplified])
     apply simp
    apply (rule u_v_r_cons1[of \<Xi> \<sigma> "UPrim (LU32 idx)" 
                                 "VPrim (LU32 idx)" 
                                 "TPrim (Num U32)"
                                 "{}" "{}" 
                                 "[(UPrim (LU32 val), RPrim (Num U32))]" 
                                 "[VPrim (LU32 val)]" 
                                 "[(''val'', TPrim (Num U32), Present)]"
                                 "{}" "{}" "RPrim (Num U32)" "''idx''", simplified])
     apply (metis lit_type.simps(4) upd_val_rel_upd_val_rel_record.intros(1))
    apply (rule u_v_r_cons1[of \<Xi> \<sigma> "UPrim (LU32 val)" 
                                 "VPrim (LU32 val)" 
                                 "TPrim (Num U32)"
                                 "{}" "{}" 
                                 "[]" 
                                 "[]" 
                                 "[]"
                                 "{}" "{}" "RPrim (Num U32)" "''val''", simplified])
     apply (metis lit_type.simps(4) upd_val_rel_upd_val_rel_record.intros(1))
  apply (rule u_v_r_empty)
  oops                   
*)

(*
section "Alternate Attempt"

theorem manual_generated_theorem':
"\<lbrakk>Generated_cogent_shallow abs_repr_u abs_typing_v abs_typing_u abs_upd_val';
 \<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd wordarray_put2_0_type))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_put2_0'' []) (Var i))
         (do x <- wordarray_put2_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma>
         (assoc_lookup
           [(''wordarray_put2_0'', wordarray_put2_0_type), (''wordarray_put2_u32'', Generated_TypeProof.wordarray_put2_u32_type)]
           ([], TUnit, TUnit))
         \<Gamma>' \<sigma> st;
 correspondence_init abs_repr_u abs_typing_v abs_typing_u abs_upd_val';
 value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>m \<xi>p; vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C abs_repr_u abs_upd_val' rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
 value_sem.proc_env_matches abs_typing_v \<xi>m \<Xi>;
 value_sem.matches abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C abs_repr_u abs_typing_u abs_upd_val' rename (Generated.state_rel abs_repr_u)
     (Generated_Shallow_Desugar.wordarray_put2_u32 vv\<^sub>s) Generated_TypeProof.wordarray_put2_u32 (wordarray_put2_u32' uv\<^sub>C) \<xi>0 \<xi>m \<xi>p
     [uv\<^sub>m] [vv\<^sub>m] \<Xi> [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))] \<sigma> s"
  apply clarsimp
  apply (subgoal_tac "\<exists>arr idx val. vv\<^sub>s = \<lparr>WordArrayPutP.arr\<^sub>f = arr, idx\<^sub>f = idx, val\<^sub>f = val\<rparr>")
   prefer 2
   apply (case_tac vv\<^sub>s; clarsimp)
  apply clarsimp
  apply (subgoal_tac "\<exists>arrv. vv\<^sub>p = VRecord [VAbstract (VWA arrv), VPrim (LU32 idx), VPrim (LU32 val)]")
   prefer 2
   apply (clarsimp simp: val_rel_shallow_C_def valRel_WordArrayPutP valRel_WordArrayU32)
  apply clarsimp
  apply (subgoal_tac "(\<forall>i < length arrv. arrv ! i = VPrim (LU32 (arr ! i))) \<and> length arr = length arrv")
   prefer 2
   apply (clarsimp simp: val_rel_shallow_C_def valRel_WordArrayPutP valRel_WordArrayU32)
  apply clarsimp
  apply (subgoal_tac "val_rel uv\<^sub>m uv\<^sub>C")
  prefer 2
   apply (clarsimp simp: val_rel_shallow_C_def)
  apply (clarsimp simp: val_rel_simp)
  apply (rule_tac vv\<^sub>s = vv\<^sub>s and 
                  vv\<^sub>p = vv\<^sub>p and
                   \<tau>o = "prod.snd (prod.snd Generated_TypeProof.wordarray_put2_u32_type)" and 
                  prog\<^sub>p = "expr.Let (Var 0) (App (AFun ''wordarray_put2'' [TPrim (Num U32)]) (Var 0))"
                      in corres_shallow_C_intro)
          apply (clarsimp simp: Generated_TypeProof.wordarray_put2_u32_def rename_def)
         apply simp
        apply simp
       apply simp
  
       apply (clarsimp simp: Generated_TypeProof.wordarray_put2_u32_type_def
                             Generated_TypeProof.abbreviatedType1_def
                             Generated_TypeProof.wordarray_put2_u32_def)
(*
       apply (rule_tac ?\<Gamma>1.0 = "[option.Some (TRecord 
                                    [(''arr'', TCon ''WordArray'' [TPrim (Num U32)] (Boxed Writable undefined), Present),
                                     (''idx'', TPrim (Num U32), Present), 
                                     (''val'', TPrim (Num U32), Present)]  Unboxed)]" and 
                       ?\<Gamma>2.0 = "[]" and 
                       t = "TCon ''WordArray'' [TPrim (Num U32)] (Boxed Writable undefined)" in typing_let)
         
*)
       defer
      apply (clarsimp simp: Generated_TypeProof.wordarray_put2_u32_def)
      apply (monad_eq simp: wordarray_put2_u32'_def)
(*
       apply (rule_tac ?\<Gamma>1.0 = "[option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]" and
                       ?\<Gamma>2.0 = "[]" and
                       t = "(prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))" in corres_let)
  *)
      defer
      defer
      apply simp
     apply (clarsimp simp: val_rel_shallow_C_def)
    prefer 3
    apply (clarsimp simp: val.scorres_def)
    apply (erule v_sem_varE; clarsimp)
    apply (erule v_sem_appE)
     prefer 2
     apply (rule FalseE)
     apply blast
    apply (erule v_sem_afunE)
    apply (erule v_sem_varE)
    apply (clarsimp simp: \<xi>p_def)
    apply (clarsimp simp: Generated_Shallow_Desugar.wordarray_put2_u32_def wordarray_put2' valRel_WordArrayU32)
    apply (erule_tac x = i in allE; clarsimp)
    apply (case_tac "i = unat idx"; clarsimp)

      apply (rule_tac ?\<Gamma>1.0 = "[option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]" and
                       ?\<Gamma>2.0 = "[option.None]" and
                       t = "(prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))" in typing_let)
     apply (fastforce intro!: left simp: split_def wordarray_put2_u32_type_def abbreviatedType1_def)
    apply (rule typing_var; clarsimp simp: Cogent.empty_def weakening_def)
    apply (rule keep; clarsimp simp: wordarray_put2_u32_type_def abbreviatedType1_def)
   
(*
     prefer 2
     apply (rule typing_var; clarsimp simp: Cogent.empty_def)
     apply (clarsimp simp: weakening_conv_all_nth)
     apply (rule keep)
     apply (clarsimp simp: Generated_TypeProof.wordarray_put2_u32_type_def abbreviatedType1_def)
    apply (clarsimp simp: Generated_TypeProof.wordarray_put2_u32_type_def abbreviatedType1_def)
    apply (clarsimp simp: split_conv_all_nth)
*)
(*  apply (clarsimp simp: corres_shallow_C_def)*)
  oops
*)
(*
\<xi>_m == monomorphic value semantics contexts for values
\<xi>_p == polymorphic ...
vv_s == value of the argument of the function, i.e. wordarray_put2, in the shallow Isabelle embedding
vv_p == value of the argument of the function, i.e. wordarray_put2, in the polymorphic value semantics
vv_m == value of the argument of the function, i.e. wordarray_put2, in the monomorphic value semantics
uv_m == value of the argument of the function, i.e. wordarray_put2, in the monomorphic update semantics
uv_c == value of the argument of the function, i.e. wordarray_put2, in the autocorres generated C
*)

section "Stronger Correspondence defintions"

definition
  corres_strong ::
  "((funtyp, abstyp, ptrtyp) store \<times> 's) set \<Rightarrow>
   funtyp expr \<Rightarrow>
   ('s,('a::cogent_C_val)) nondet_monad \<Rightarrow>
   (funtyp, abstyp, ptrtyp) uabsfuns \<Rightarrow>
   (funtyp, abstyp, ptrtyp) uval env \<Rightarrow>
   (funtyp \<Rightarrow> poly_type) \<Rightarrow>
   ctx \<Rightarrow>
   (funtyp, abstyp, ptrtyp) store \<Rightarrow>
   's \<Rightarrow>
   bool"
where
  "corres_strong srel c m \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s \<equiv>
   (\<sigma>,s) \<in> srel \<longrightarrow>
   (\<exists>r w. upd.matches_ptrs \<Xi>' \<sigma> \<gamma> \<Gamma>' r w \<longrightarrow>
   (\<not> prod.snd (m s)) \<and>
   (\<forall>r' s'. (r',s') \<in> prod.fst (m s) \<longrightarrow>
     (\<exists>\<sigma>' r.(\<xi>', \<gamma> \<turnstile> (\<sigma>,c)  \<Down>! (\<sigma>',r)) \<and> (\<sigma>',s') \<in> srel \<and> val_rel r r')))"

definition corres_shallow_C_strong where
  "corres_shallow_C_strong
     (rename' :: funtyp \<times> type list \<Rightarrow> funtyp)
     (srel :: ((funtyp, abstyp, ptrtyp) store \<times> 's) set)
     (v\<^sub>s :: 'sv)
     (prog\<^sub>m :: funtyp expr)
     (prog\<^sub>C :: ('s, 'cv :: cogent_C_val) nondet_monad)
     (\<xi>\<^sub>u\<^sub>m :: (funtyp, abstyp, ptrtyp) uabsfuns)
     (\<xi>\<^sub>v\<^sub>m :: (funtyp, vabstyp) vabsfuns)
     (\<xi>\<^sub>v\<^sub>p :: (funtyp, vabstyp) vabsfuns)
     (\<gamma>\<^sub>u\<^sub>m :: (funtyp, abstyp, ptrtyp) uval env)
     (\<gamma>\<^sub>v\<^sub>m :: (funtyp, vabstyp) vval env)
     (\<Xi>\<^sub>m :: funtyp \<Rightarrow> poly_type)
     (\<Gamma>\<^sub>m :: ctx)
     (\<sigma> :: (funtyp, abstyp, ptrtyp) store)
     (s :: 's) \<equiv>
   upd.proc_env_matches_ptrs \<xi>\<^sub>u\<^sub>m \<Xi>\<^sub>m \<longrightarrow>
   (\<sigma>, s) \<in> srel \<longrightarrow>
   (\<exists>r w. u_v_matches \<Xi>\<^sub>m \<sigma> \<gamma>\<^sub>u\<^sub>m \<gamma>\<^sub>v\<^sub>m \<Gamma>\<^sub>m r w) \<longrightarrow>
   (\<not> prod.snd (prog\<^sub>C s) \<and>
   (\<forall>r' s'. (r', s') \<in> prod.fst (prog\<^sub>C s) \<longrightarrow>
     (\<exists>\<sigma>' v\<^sub>u\<^sub>m v\<^sub>p.
      (\<xi>\<^sub>u\<^sub>m, \<gamma>\<^sub>u\<^sub>m \<turnstile> (\<sigma>, prog\<^sub>m) \<Down>! (\<sigma>', v\<^sub>u\<^sub>m)) \<and>
       (\<xi>\<^sub>v\<^sub>m, \<gamma>\<^sub>v\<^sub>m \<turnstile> prog\<^sub>m \<Down> val.rename_val rename' (val.monoval v\<^sub>p)) \<and>
       (\<sigma>', s') \<in> srel \<and>
       val_rel_shallow_C rename v\<^sub>s r' v\<^sub>p v\<^sub>u\<^sub>m \<xi>\<^sub>v\<^sub>p \<sigma>' \<Xi>\<^sub>m)))"

section "Stronger Correspondence Lemmas/Theorems"

lemma upd_C_wordarray_put2_corres_strong:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd wordarray_put2_0_type))\<rbrakk>
    \<Longrightarrow> corres_strong  (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_put2_0'' []) (Var i))
         (do x <- wordarray_put2_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma>
         (assoc_lookup
           [(''wordarray_put2_0'', wordarray_put2_0_type), (''wordarray_put2_u32'', Generated_TypeProof.wordarray_put2_u32_type)]
           ([], TUnit, TUnit))
         \<Gamma>' \<sigma> st"
  apply (insert proc_ctx_wellformed_\<Xi> upd_proc_env_matches_ptrs_\<xi>0_\<Xi>)
  apply (unfold corres_strong_def)
  apply (drule_tac i  = i  and 
                   \<gamma>  = \<gamma>  and 
                   v' = v' and
                   \<Gamma>' = \<Gamma>' and
                   \<sigma>  = \<sigma>  and
                   st = st in upd_C_wordarray_put2_corres; clarsimp simp: corres_def \<Xi>_def)
  
  done

theorem shallow_C_wordarray_put2_corres_strong:
"\<lbrakk>vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C abs_repr_u abs_upd_val' rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>; 
 value_sem.matches abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C abs_repr_u abs_typing_u abs_upd_val' rename (Generated.state_rel abs_repr_u)
     (Generated_Shallow_Desugar.wordarray_put2_u32 vv\<^sub>s) Generated_TypeProof.wordarray_put2_u32 (wordarray_put2_u32' uv\<^sub>C) \<xi>0 \<xi>m \<xi>p
     [uv\<^sub>m] [vv\<^sub>m] \<Xi> [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))] \<sigma> s"
  apply (insert value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m_\<xi>p 
                val_proc_env_matches_\<xi>m_\<Xi> 
                proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>
                proc_ctx_wellformed_\<Xi>
                upd_C_wordarray_put2_corres
                upd_proc_env_matches_ptrs_\<xi>0_\<Xi>)
  apply (rule shallow_C_wordarray_put2_corres; simp)
  done

end (* of context *)
end