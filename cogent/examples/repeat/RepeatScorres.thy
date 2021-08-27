theory RepeatScorres
  imports
    RepeatShallow
    RepeatMono
    "build/Generated_SCorres_Normal"
begin

section "Shallow repeat loop definition"

overloading repeat' \<equiv> repeat
begin
definition repeat' :: "(64 word, ('a, 'b) StepParam \<Rightarrow> bool, ('a, 'b) StepParam \<Rightarrow> 'a, 'a, 'b) RepParam \<Rightarrow> 'a"
  where
"repeat x =
  repeatatl (unat (RepParam.n\<^sub>f x))
            (\<lambda>(a :: 'a) (b :: 'b). (RepParam.stop\<^sub>f x) \<lparr>StepParam.acc\<^sub>f = a, obsv\<^sub>f = b\<rparr>)
            (\<lambda>(a :: 'a) (b :: 'b). (RepParam.step\<^sub>f x) \<lparr>StepParam.acc\<^sub>f = a, obsv\<^sub>f = b\<rparr>)
            (RepParam.acc\<^sub>f x)
            (RepParam.obsv\<^sub>f x)"
end (* of overloading *)

section "Repeat loop scorres"

context shallow begin

lemma vrepeat_bod_scorres:
  "\<lbrakk>\<xi>vle \<xi>' \<xi>'';
    valRel \<xi>'' (x ::(64 word, ('b, 'c) StepParam \<Rightarrow> bool,  ('b, 'c) StepParam \<Rightarrow> 'b, 'b, 'c) RepParam)
      (VRecord [VPrim (LU64 n), f, g, acc, obsv]); is_vvalfun f; is_vvalfun g;
    vrepeat_bod \<xi>' (unat n) (vvalfun_to_expr f) (vvalfun_to_expr g) acc obsv v'\<rbrakk>
   \<Longrightarrow> valRel \<xi>''
              (repeatatl (unat (n\<^sub>f x)) (\<lambda>a b. stop\<^sub>f x \<lparr>StepParam.acc\<^sub>f = a, obsv\<^sub>f = b\<rparr>)
                (\<lambda>a b. step\<^sub>f x \<lparr>StepParam.acc\<^sub>f = a, obsv\<^sub>f = b\<rparr>) (RepParam.acc\<^sub>f x) (RepParam.obsv\<^sub>f x))
              v'"
  apply (induct n arbitrary: acc x)
   apply (clarsimp simp: valRel_RepParam)
   apply (subst repeatatl.simps)
   apply simp
  apply (drule unatSuc; clarsimp)
  apply (rename_tac n acc x b)
  apply (case_tac b; clarsimp)
   apply (clarsimp simp: valRel_RepParam)
   apply (subst repeatatl.simps; clarsimp)
   apply (erule notE)
   apply (erule disjE; clarsimp)
    apply (elim v_sem_appE v_sem_funE v_sem_varE; clarsimp)
    apply (erule_tac x = "\<lparr>StepParam.acc\<^sub>f = RepParam.acc\<^sub>f x, obsv\<^sub>f = RepParam.obsv\<^sub>f x\<rparr>" in allE)
    apply (erule_tac x = "VRecord [v', obsv]" in allE)
    apply (erule impE, simp add: valRel_StepParam)
    apply (erule_tac x = "VPrim (LBool True)" in allE)
    apply (drule_tac \<xi>b = \<xi>'' in  v_sem_v_sem_all_\<xi>vle(1); simp)
   apply (elim v_sem_appE v_sem_afunE v_sem_varE; clarsimp)
   apply (erule_tac x = "\<lparr>StepParam.acc\<^sub>f = RepParam.acc\<^sub>f x, obsv\<^sub>f = RepParam.obsv\<^sub>f x\<rparr>" in allE)
   apply (erule_tac x = "VRecord [v', obsv]" in allE)
   apply (erule impE, simp add: valRel_StepParam)
   apply (erule_tac x = "VPrim (LBool True)" in allE)
   apply (erule impE; simp?)
   apply (rule \<xi>vleD; assumption)
  apply (rename_tac acc')
  apply (drule_tac x = acc' in meta_spec)
  apply clarsimp
  apply (drule_tac
      x = "\<lparr>RepParam.n\<^sub>f = n, stop\<^sub>f = stop\<^sub>f x, step\<^sub>f = step\<^sub>f x,
            acc\<^sub>f = step\<^sub>f x \<lparr>StepParam.acc\<^sub>f = RepParam.acc\<^sub>f x, obsv\<^sub>f = RepParam.obsv\<^sub>f x\<rparr>,
            obsv\<^sub>f = RepParam.obsv\<^sub>f x \<rparr>" in meta_spec)
  apply (elim meta_allE meta_impE; assumption?)
   apply (clarsimp simp: valRel_RepParam)
   apply (thin_tac "_ \<or> _")
   apply (thin_tac "_, _ \<turnstile> _ \<Down> _")
   apply (elim disjE v_sem_appE v_sem_varE; clarsimp; elim v_sem_funE v_sem_afunE; clarsimp)
    apply (erule_tac x = "\<lparr>StepParam.acc\<^sub>f = RepParam.acc\<^sub>f x, obsv\<^sub>f = RepParam.obsv\<^sub>f x\<rparr>" in allE)
    apply (erule_tac x = "VRecord [acc, obsv]" in allE)
    apply (erule impE, simp add: valRel_StepParam)
    apply (erule_tac x = acc' in allE)
    apply (drule_tac \<xi>b = \<xi>'' in  v_sem_v_sem_all_\<xi>vle(1); simp)
   apply (erule_tac x = "\<lparr>StepParam.acc\<^sub>f = RepParam.acc\<^sub>f x, obsv\<^sub>f = RepParam.obsv\<^sub>f x\<rparr>" in allE)
   apply (erule_tac x = "VRecord [acc, obsv]" in allE)
   apply (erule impE, simp add: valRel_StepParam)
   apply (erule_tac x = acc' in allE)
   apply (erule impE; simp?)
   apply (rule \<xi>vleD; assumption)
  apply clarsimp
  apply (subst (asm) valRel_RepParam; clarsimp)
  apply (erule v_sem_appE; erule disjE; clarsimp; elim v_sem_funE v_sem_afunE v_sem_varE; clarsimp)
   apply (erule_tac x = "\<lparr>StepParam.acc\<^sub>f = RepParam.acc\<^sub>f x, obsv\<^sub>f = RepParam.obsv\<^sub>f x\<rparr>" in allE)
   apply (erule_tac x = "VRecord [acc, obsv]" in allE)
   apply (erule impE, simp add: valRel_StepParam)
   apply (erule_tac x = "VPrim (LBool False)" in allE)
   apply (erule impE; simp?)
   apply (rule \<xi>vleD; assumption)
   apply (subst repeatatl.simps; clarsimp)
  apply (erule_tac x = "\<lparr>StepParam.acc\<^sub>f = RepParam.acc\<^sub>f x, obsv\<^sub>f = RepParam.obsv\<^sub>f x\<rparr>" in allE)
  apply (erule_tac x = "VRecord [acc, obsv]" in allE)
  apply (erule impE, simp add: valRel_StepParam)
  apply (erule_tac x = "VPrim (LBool False)" in allE)
  apply (erule impE, rule v_sem_v_sem_all_\<xi>vle(1); simp)
  apply (subst repeatatl.simps; clarsimp)
  done

lemma repeat_scorres: 
  "\<lbrakk>\<xi>vle \<xi>' \<xi>''; \<xi>'' ''repeat'' = prepeat \<xi>'\<rbrakk> \<Longrightarrow> scorres repeat (AFun ''repeat'' ts) \<gamma> \<xi>''"
  unfolding scorres_def
  apply clarsimp
  apply (erule v_sem_afunE; clarsimp)
  apply (erule notE)
  unfolding repeat'_def prepeat_def
  apply clarsimp
  apply (rule vrepeat_bod_scorres; simp?)
  done

end (* of context *)

end