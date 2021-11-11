(*
This file is generated by Cogent

*)

theory Generated_SCorres_Normal
imports "Generated_Shallow_Normal"
"Generated_Deep_Normal"
"CogentShallow.Shallow_Tac"
begin

overloading
  valRel_R \<equiv> valRel
begin
  definition valRel_R: "\<And>\<xi> x v. valRel_R \<xi> (x :: ('t_f1, 't_f2, 't_f3) R) v \<equiv> \<exists>f_f1 f_f2 f_f3. v = VRecord [f_f1, f_f2, f_f3] \<and> valRel \<xi> (R.f1\<^sub>f x) f_f1 \<and> valRel \<xi> (R.f2\<^sub>f x) f_f2 \<and> valRel \<xi> (R.f3\<^sub>f x) f_f3"
end

lemmas valRel_records =
  valRel_R
  R.defs

context shallow begin

lemma scorres_struct_R :
  "\<And>\<gamma> \<xi> s_f1 s_f2 s_f3 d_f1 d_f2 d_f3.
  scorres s_f1 d_f1 \<gamma> \<xi> \<Longrightarrow>
  scorres s_f2 d_f2 \<gamma> \<xi> \<Longrightarrow>
  scorres s_f3 d_f3 \<gamma> \<xi> \<Longrightarrow>
  scorres (R.make s_f1 s_f2 s_f3) (Struct ts [d_f1, d_f2, d_f3]) \<gamma> \<xi>"
  apply (clarsimp simp: scorres_def valRel_R R.defs elim!: v_sem_elims)
  done

lemmas scorres_structs =
  scorres_struct_R

lemma shallow_tac_rec_field_R__f1 :
  "shallow_tac_rec_field \<xi> (R.f1\<^sub>f :: ('t_f1, 't_f2, 't_f3) R \<Rightarrow> 't_f1) R.f1\<^sub>f_update 0"
  apply (fastforce intro!: shallow_tac_rec_fieldI simp: valRel_R)
  done

lemma shallow_tac_rec_field_R__f2 :
  "shallow_tac_rec_field \<xi> (R.f2\<^sub>f :: ('t_f1, 't_f2, 't_f3) R \<Rightarrow> 't_f2) R.f2\<^sub>f_update 1"
  apply (fastforce intro!: shallow_tac_rec_fieldI simp: valRel_R)
  done

lemma shallow_tac_rec_field_R__f3 :
  "shallow_tac_rec_field \<xi> (R.f3\<^sub>f :: ('t_f1, 't_f2, 't_f3) R \<Rightarrow> 't_f3) R.f3\<^sub>f_update 2"
  apply (fastforce intro!: shallow_tac_rec_fieldI simp: valRel_R)
  done

lemmas scorres_rec_fields =
  shallow_tac_rec_field_R__f1
  shallow_tac_rec_field_R__f2
  shallow_tac_rec_field_R__f3

local_setup \<open>
gen_scorres_lemmas "Generated_ShallowShared" "Generated_Shallow_Normal" "Generated_Deep_Normal" Cogent_abstract_functions Cogent_functions
\<close>


end

end
