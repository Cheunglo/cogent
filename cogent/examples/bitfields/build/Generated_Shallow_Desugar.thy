(*
This file is generated by Cogent

*)

theory Generated_Shallow_Desugar
imports "Generated_ShallowShared"
begin

definition
  id4 :: " U4 \<Rightarrow>  U4"
where
  "id4 ds\<^sub>0 \<equiv> HOL.Let ds\<^sub>0 (\<lambda>x. x)"

definition
  id2 :: " U2 \<Rightarrow>  U2"
where
  "id2 ds\<^sub>0 \<equiv> HOL.Let ds\<^sub>0 (\<lambda>x. x)"

definition
  foo :: " RL\<^sub>T \<Rightarrow>  RL\<^sub>T"
where
  "foo ds\<^sub>0 \<equiv> HOL.Let ds\<^sub>0 (\<lambda>r. Let\<^sub>d\<^sub>s (R.f1\<^sub>f r) (\<lambda>ds\<^sub>1. HOL.If ds\<^sub>1 (HOL.Let (u8_to_u4 ((AND) (u4_to_u8 (R.f3\<^sub>f r)) (12 :: 8 word))) (\<lambda>v. R.f3\<^sub>f_update (\<lambda>_. v) r)) (HOL.Let (u8_to_u2 ((+) (u2_to_u8 (R.f2\<^sub>f r)) (1 :: 8 word))) (\<lambda>v. R.f2\<^sub>f_update (\<lambda>_. v) r))))"

end
