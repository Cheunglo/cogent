(*
This file is generated by Cogent

*)

theory Generated_ShallowTuplesProof
imports "Generated_Shallow_Desugar"
"Generated_Shallow_Desugar_Tuples"
"CogentShallow.ShallowTuples"
begin

ML \<open>
structure ShallowTuplesRules_Generated =
  Named_Thms (
    val name = Binding.name "ShallowTuplesRules_Generated"
    val description = ""
  )
\<close>
setup \<open> ShallowTuplesRules_Generated.setup \<close>


ML \<open>
structure ShallowTuplesThms_Generated =
  Named_Thms (
    val name = Binding.name "ShallowTuplesThms_Generated"
    val description = ""
  )
\<close>
setup \<open> ShallowTuplesThms_Generated.setup \<close>


overloading shallow_tuples_rel_WordArrayMapNoBreakP \<equiv> shallow_tuples_rel begin
  definition "shallow_tuples_rel_WordArrayMapNoBreakP (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6) Generated_ShallowShared.WordArrayMapNoBreakP) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6) Generated_ShallowShared_Tuples.WordArrayMapNoBreakP) \<equiv>
    shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.arr\<^sub>f x) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.arr\<^sub>f xt) \<and>
    shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.frm\<^sub>f x) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.frm\<^sub>f xt) \<and>
    shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.to\<^sub>f x) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.to\<^sub>f xt) \<and>
    shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.f\<^sub>f x) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.f\<^sub>f xt) \<and>
    shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.acc\<^sub>f x) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.acc\<^sub>f xt) \<and>
    shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.obsv\<^sub>f x) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.obsv\<^sub>f xt)"
end
lemma shallow_tuples_rule_make__WordArrayMapNoBreakP [ShallowTuplesRules_Generated]:
  "\<lbrakk>
     shallow_tuples_rel x1 xt1;
     shallow_tuples_rel x2 xt2;
     shallow_tuples_rel x3 xt3;
     shallow_tuples_rel x4 xt4;
     shallow_tuples_rel x5 xt5;
     shallow_tuples_rel x6 xt6
  \<rbrakk> \<Longrightarrow> shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.make x1 x2 x3 x4 x5 x6) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.make xt1 xt2 xt3 xt4 xt5 xt6)"
  by (simp add: shallow_tuples_rel_WordArrayMapNoBreakP_def Generated_ShallowShared.WordArrayMapNoBreakP.defs Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.defs)
lemma shallow_tuples_rule__WordArrayMapNoBreakP__arr\<^sub>f [ShallowTuplesRules_Generated]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6) Generated_ShallowShared.WordArrayMapNoBreakP) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6) Generated_ShallowShared_Tuples.WordArrayMapNoBreakP) \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.arr\<^sub>f x) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.arr\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_WordArrayMapNoBreakP_def)
lemma shallow_tuples_rule__WordArrayMapNoBreakP__frm\<^sub>f [ShallowTuplesRules_Generated]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6) Generated_ShallowShared.WordArrayMapNoBreakP) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6) Generated_ShallowShared_Tuples.WordArrayMapNoBreakP) \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.frm\<^sub>f x) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.frm\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_WordArrayMapNoBreakP_def)
lemma shallow_tuples_rule__WordArrayMapNoBreakP__to\<^sub>f [ShallowTuplesRules_Generated]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6) Generated_ShallowShared.WordArrayMapNoBreakP) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6) Generated_ShallowShared_Tuples.WordArrayMapNoBreakP) \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.to\<^sub>f x) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.to\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_WordArrayMapNoBreakP_def)
lemma shallow_tuples_rule__WordArrayMapNoBreakP__f\<^sub>f [ShallowTuplesRules_Generated]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6) Generated_ShallowShared.WordArrayMapNoBreakP) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6) Generated_ShallowShared_Tuples.WordArrayMapNoBreakP) \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.f\<^sub>f x) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.f\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_WordArrayMapNoBreakP_def)
lemma shallow_tuples_rule__WordArrayMapNoBreakP__acc\<^sub>f [ShallowTuplesRules_Generated]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6) Generated_ShallowShared.WordArrayMapNoBreakP) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6) Generated_ShallowShared_Tuples.WordArrayMapNoBreakP) \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.acc\<^sub>f x) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.acc\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_WordArrayMapNoBreakP_def)
lemma shallow_tuples_rule__WordArrayMapNoBreakP__obsv\<^sub>f [ShallowTuplesRules_Generated]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6) Generated_ShallowShared.WordArrayMapNoBreakP) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6) Generated_ShallowShared_Tuples.WordArrayMapNoBreakP) \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.obsv\<^sub>f x) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.obsv\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_WordArrayMapNoBreakP_def)
lemma shallow_tuples_rule__WordArrayMapNoBreakP__arr\<^sub>f__update [ShallowTuplesRules_Generated]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6) Generated_ShallowShared.WordArrayMapNoBreakP) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6) Generated_ShallowShared_Tuples.WordArrayMapNoBreakP);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.arr\<^sub>f_update (\<lambda>_. v) x) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.arr\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_WordArrayMapNoBreakP_def)
lemma shallow_tuples_rule__WordArrayMapNoBreakP__frm\<^sub>f__update [ShallowTuplesRules_Generated]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6) Generated_ShallowShared.WordArrayMapNoBreakP) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6) Generated_ShallowShared_Tuples.WordArrayMapNoBreakP);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.frm\<^sub>f_update (\<lambda>_. v) x) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.frm\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_WordArrayMapNoBreakP_def)
lemma shallow_tuples_rule__WordArrayMapNoBreakP__to\<^sub>f__update [ShallowTuplesRules_Generated]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6) Generated_ShallowShared.WordArrayMapNoBreakP) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6) Generated_ShallowShared_Tuples.WordArrayMapNoBreakP);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.to\<^sub>f_update (\<lambda>_. v) x) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.to\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_WordArrayMapNoBreakP_def)
lemma shallow_tuples_rule__WordArrayMapNoBreakP__f\<^sub>f__update [ShallowTuplesRules_Generated]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6) Generated_ShallowShared.WordArrayMapNoBreakP) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6) Generated_ShallowShared_Tuples.WordArrayMapNoBreakP);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.f\<^sub>f_update (\<lambda>_. v) x) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.f\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_WordArrayMapNoBreakP_def)
lemma shallow_tuples_rule__WordArrayMapNoBreakP__acc\<^sub>f__update [ShallowTuplesRules_Generated]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6) Generated_ShallowShared.WordArrayMapNoBreakP) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6) Generated_ShallowShared_Tuples.WordArrayMapNoBreakP);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.acc\<^sub>f_update (\<lambda>_. v) x) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.acc\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_WordArrayMapNoBreakP_def)
lemma shallow_tuples_rule__WordArrayMapNoBreakP__obsv\<^sub>f__update [ShallowTuplesRules_Generated]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3, 'x4, 'x5, 'x6) Generated_ShallowShared.WordArrayMapNoBreakP) (xt :: ('xt1, 'xt2, 'xt3, 'xt4, 'xt5, 'xt6) Generated_ShallowShared_Tuples.WordArrayMapNoBreakP);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.WordArrayMapNoBreakP.obsv\<^sub>f_update (\<lambda>_. v) x) (Generated_ShallowShared_Tuples.WordArrayMapNoBreakP.obsv\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_WordArrayMapNoBreakP_def)


overloading shallow_tuples_rel_WordArrayPutP \<equiv> shallow_tuples_rel begin
  definition "shallow_tuples_rel_WordArrayPutP (x :: ('x1, 'x2, 'x3) Generated_ShallowShared.WordArrayPutP) (xt :: ('xt1, 'xt2, 'xt3) Generated_ShallowShared_Tuples.WordArrayPutP) \<equiv>
    shallow_tuples_rel (Generated_ShallowShared.WordArrayPutP.arr\<^sub>f x) (Generated_ShallowShared_Tuples.WordArrayPutP.arr\<^sub>f xt) \<and>
    shallow_tuples_rel (Generated_ShallowShared.WordArrayPutP.idx\<^sub>f x) (Generated_ShallowShared_Tuples.WordArrayPutP.idx\<^sub>f xt) \<and>
    shallow_tuples_rel (Generated_ShallowShared.WordArrayPutP.val\<^sub>f x) (Generated_ShallowShared_Tuples.WordArrayPutP.val\<^sub>f xt)"
end
lemma shallow_tuples_rule_make__WordArrayPutP [ShallowTuplesRules_Generated]:
  "\<lbrakk>
     shallow_tuples_rel x1 xt1;
     shallow_tuples_rel x2 xt2;
     shallow_tuples_rel x3 xt3
  \<rbrakk> \<Longrightarrow> shallow_tuples_rel (Generated_ShallowShared.WordArrayPutP.make x1 x2 x3) (Generated_ShallowShared_Tuples.WordArrayPutP.make xt1 xt2 xt3)"
  by (simp add: shallow_tuples_rel_WordArrayPutP_def Generated_ShallowShared.WordArrayPutP.defs Generated_ShallowShared_Tuples.WordArrayPutP.defs)
lemma shallow_tuples_rule__WordArrayPutP__arr\<^sub>f [ShallowTuplesRules_Generated]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3) Generated_ShallowShared.WordArrayPutP) (xt :: ('xt1, 'xt2, 'xt3) Generated_ShallowShared_Tuples.WordArrayPutP) \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.WordArrayPutP.arr\<^sub>f x) (Generated_ShallowShared_Tuples.WordArrayPutP.arr\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_WordArrayPutP_def)
lemma shallow_tuples_rule__WordArrayPutP__idx\<^sub>f [ShallowTuplesRules_Generated]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3) Generated_ShallowShared.WordArrayPutP) (xt :: ('xt1, 'xt2, 'xt3) Generated_ShallowShared_Tuples.WordArrayPutP) \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.WordArrayPutP.idx\<^sub>f x) (Generated_ShallowShared_Tuples.WordArrayPutP.idx\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_WordArrayPutP_def)
lemma shallow_tuples_rule__WordArrayPutP__val\<^sub>f [ShallowTuplesRules_Generated]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3) Generated_ShallowShared.WordArrayPutP) (xt :: ('xt1, 'xt2, 'xt3) Generated_ShallowShared_Tuples.WordArrayPutP) \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.WordArrayPutP.val\<^sub>f x) (Generated_ShallowShared_Tuples.WordArrayPutP.val\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_WordArrayPutP_def)
lemma shallow_tuples_rule__WordArrayPutP__arr\<^sub>f__update [ShallowTuplesRules_Generated]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3) Generated_ShallowShared.WordArrayPutP) (xt :: ('xt1, 'xt2, 'xt3) Generated_ShallowShared_Tuples.WordArrayPutP);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.WordArrayPutP.arr\<^sub>f_update (\<lambda>_. v) x) (Generated_ShallowShared_Tuples.WordArrayPutP.arr\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_WordArrayPutP_def)
lemma shallow_tuples_rule__WordArrayPutP__idx\<^sub>f__update [ShallowTuplesRules_Generated]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3) Generated_ShallowShared.WordArrayPutP) (xt :: ('xt1, 'xt2, 'xt3) Generated_ShallowShared_Tuples.WordArrayPutP);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.WordArrayPutP.idx\<^sub>f_update (\<lambda>_. v) x) (Generated_ShallowShared_Tuples.WordArrayPutP.idx\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_WordArrayPutP_def)
lemma shallow_tuples_rule__WordArrayPutP__val\<^sub>f__update [ShallowTuplesRules_Generated]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3) Generated_ShallowShared.WordArrayPutP) (xt :: ('xt1, 'xt2, 'xt3) Generated_ShallowShared_Tuples.WordArrayPutP);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.WordArrayPutP.val\<^sub>f_update (\<lambda>_. v) x) (Generated_ShallowShared_Tuples.WordArrayPutP.val\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_WordArrayPutP_def)


overloading shallow_tuples_rel_ElemAO \<equiv> shallow_tuples_rel begin
  definition "shallow_tuples_rel_ElemAO (x :: ('x1, 'x2, 'x3) Generated_ShallowShared.ElemAO) (xt :: ('xt1, 'xt2, 'xt3) Generated_ShallowShared_Tuples.ElemAO) \<equiv>
    shallow_tuples_rel (Generated_ShallowShared.ElemAO.elem\<^sub>f x) (Generated_ShallowShared_Tuples.ElemAO.elem\<^sub>f xt) \<and>
    shallow_tuples_rel (Generated_ShallowShared.ElemAO.acc\<^sub>f x) (Generated_ShallowShared_Tuples.ElemAO.acc\<^sub>f xt) \<and>
    shallow_tuples_rel (Generated_ShallowShared.ElemAO.obsv\<^sub>f x) (Generated_ShallowShared_Tuples.ElemAO.obsv\<^sub>f xt)"
end
lemma shallow_tuples_rule_make__ElemAO [ShallowTuplesRules_Generated]:
  "\<lbrakk>
     shallow_tuples_rel x1 xt1;
     shallow_tuples_rel x2 xt2;
     shallow_tuples_rel x3 xt3
  \<rbrakk> \<Longrightarrow> shallow_tuples_rel (Generated_ShallowShared.ElemAO.make x1 x2 x3) (Generated_ShallowShared_Tuples.ElemAO.make xt1 xt2 xt3)"
  by (simp add: shallow_tuples_rel_ElemAO_def Generated_ShallowShared.ElemAO.defs Generated_ShallowShared_Tuples.ElemAO.defs)
lemma shallow_tuples_rule__ElemAO__elem\<^sub>f [ShallowTuplesRules_Generated]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3) Generated_ShallowShared.ElemAO) (xt :: ('xt1, 'xt2, 'xt3) Generated_ShallowShared_Tuples.ElemAO) \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.ElemAO.elem\<^sub>f x) (Generated_ShallowShared_Tuples.ElemAO.elem\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_ElemAO_def)
lemma shallow_tuples_rule__ElemAO__acc\<^sub>f [ShallowTuplesRules_Generated]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3) Generated_ShallowShared.ElemAO) (xt :: ('xt1, 'xt2, 'xt3) Generated_ShallowShared_Tuples.ElemAO) \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.ElemAO.acc\<^sub>f x) (Generated_ShallowShared_Tuples.ElemAO.acc\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_ElemAO_def)
lemma shallow_tuples_rule__ElemAO__obsv\<^sub>f [ShallowTuplesRules_Generated]:
  "shallow_tuples_rel (x :: ('x1, 'x2, 'x3) Generated_ShallowShared.ElemAO) (xt :: ('xt1, 'xt2, 'xt3) Generated_ShallowShared_Tuples.ElemAO) \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.ElemAO.obsv\<^sub>f x) (Generated_ShallowShared_Tuples.ElemAO.obsv\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_ElemAO_def)
lemma shallow_tuples_rule__ElemAO__elem\<^sub>f__update [ShallowTuplesRules_Generated]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3) Generated_ShallowShared.ElemAO) (xt :: ('xt1, 'xt2, 'xt3) Generated_ShallowShared_Tuples.ElemAO);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.ElemAO.elem\<^sub>f_update (\<lambda>_. v) x) (Generated_ShallowShared_Tuples.ElemAO.elem\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_ElemAO_def)
lemma shallow_tuples_rule__ElemAO__acc\<^sub>f__update [ShallowTuplesRules_Generated]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3) Generated_ShallowShared.ElemAO) (xt :: ('xt1, 'xt2, 'xt3) Generated_ShallowShared_Tuples.ElemAO);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.ElemAO.acc\<^sub>f_update (\<lambda>_. v) x) (Generated_ShallowShared_Tuples.ElemAO.acc\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_ElemAO_def)
lemma shallow_tuples_rule__ElemAO__obsv\<^sub>f__update [ShallowTuplesRules_Generated]:
  "\<lbrakk> shallow_tuples_rel (x :: ('x1, 'x2, 'x3) Generated_ShallowShared.ElemAO) (xt :: ('xt1, 'xt2, 'xt3) Generated_ShallowShared_Tuples.ElemAO);
     shallow_tuples_rel v vt
   \<rbrakk> \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.ElemAO.obsv\<^sub>f_update (\<lambda>_. v) x) (Generated_ShallowShared_Tuples.ElemAO.obsv\<^sub>f_update (\<lambda>_. vt) xt)"
  by (simp add: shallow_tuples_rel_ElemAO_def)


overloading shallow_tuples_rel_T0 \<equiv> shallow_tuples_rel begin
  definition "shallow_tuples_rel_T0 (x :: ('x1, 'x2) Generated_ShallowShared.T0) (xt :: 'xt1 \<times> 'xt2) \<equiv>
    shallow_tuples_rel (Generated_ShallowShared.T0.p1\<^sub>f x) (P2_p1\<^sub>f xt) \<and>
    shallow_tuples_rel (Generated_ShallowShared.T0.p2\<^sub>f x) (P2_p2\<^sub>f xt)"
end
lemma shallow_tuples_rule__T0_make [ShallowTuplesRules_Generated]:
  "\<lbrakk>
     shallow_tuples_rel x1 xt1;
     shallow_tuples_rel x2 xt2
  \<rbrakk> \<Longrightarrow> shallow_tuples_rel (Generated_ShallowShared.T0.make x1 x2) (xt1, xt2)"
  by (simp add: shallow_tuples_rel_T0_def Generated_ShallowShared.T0.defs Px_px)
lemma shallow_tuples_rule__T0__p1\<^sub>f [ShallowTuplesRules_Generated]:
  "shallow_tuples_rel (x :: ('x1, 'x2) Generated_ShallowShared.T0) (xt :: 'xt1 \<times> 'xt2) \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.T0.p1\<^sub>f x) (P2_p1\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_T0_def)
lemma shallow_tuples_rule__T0__p2\<^sub>f [ShallowTuplesRules_Generated]:
  "shallow_tuples_rel (x :: ('x1, 'x2) Generated_ShallowShared.T0) (xt :: 'xt1 \<times> 'xt2) \<Longrightarrow>
   shallow_tuples_rel (Generated_ShallowShared.T0.p2\<^sub>f x) (P2_p2\<^sub>f xt)"
  by (simp add: shallow_tuples_rel_T0_def)


lemma shallow_tuples__wordarray_get [ShallowTuplesThms_Generated]:
  "shallow_tuples_rel Generated_ShallowShared.wordarray_get Generated_ShallowShared_Tuples.wordarray_get"
  sorry


lemma shallow_tuples__wordarray_length [ShallowTuplesThms_Generated]:
  "shallow_tuples_rel Generated_ShallowShared.wordarray_length Generated_ShallowShared_Tuples.wordarray_length"
  sorry


lemma shallow_tuples__wordarray_put2 [ShallowTuplesThms_Generated]:
  "shallow_tuples_rel Generated_ShallowShared.wordarray_put2 Generated_ShallowShared_Tuples.wordarray_put2"
  sorry


lemma shallow_tuples__wordarray_fold_no_break [ShallowTuplesThms_Generated]:
  "shallow_tuples_rel Generated_ShallowShared.wordarray_fold_no_break Generated_ShallowShared_Tuples.wordarray_fold_no_break"
  sorry


lemma shallow_tuples__wordarray_map_no_break [ShallowTuplesThms_Generated]:
  "shallow_tuples_rel Generated_ShallowShared.wordarray_map_no_break Generated_ShallowShared_Tuples.wordarray_map_no_break"
  sorry


lemma shallow_tuples__wordarray_get_u32 [ShallowTuplesThms_Generated]:
  "shallow_tuples_rel Generated_Shallow_Desugar.wordarray_get_u32 Generated_Shallow_Desugar_Tuples.wordarray_get_u32"
  apply (rule shallow_tuples_rel_funI)
  apply (unfold Generated_Shallow_Desugar.wordarray_get_u32_def Generated_Shallow_Desugar_Tuples.wordarray_get_u32_def id_def)
  by (assumption |
      rule shallow_tuples_basic_bucket ShallowTuplesRules_Generated
           ShallowTuplesThms_Generated ShallowTuplesThms_Generated[THEN shallow_tuples_rel_funD])+


lemma shallow_tuples__wordarray_length_u32 [ShallowTuplesThms_Generated]:
  "shallow_tuples_rel Generated_Shallow_Desugar.wordarray_length_u32 Generated_Shallow_Desugar_Tuples.wordarray_length_u32"
  apply (rule shallow_tuples_rel_funI)
  apply (unfold Generated_Shallow_Desugar.wordarray_length_u32_def Generated_Shallow_Desugar_Tuples.wordarray_length_u32_def id_def)
  by (assumption |
      rule shallow_tuples_basic_bucket ShallowTuplesRules_Generated
           ShallowTuplesThms_Generated ShallowTuplesThms_Generated[THEN shallow_tuples_rel_funD])+


lemma shallow_tuples__wordarray_put2_u32 [ShallowTuplesThms_Generated]:
  "shallow_tuples_rel Generated_Shallow_Desugar.wordarray_put2_u32 Generated_Shallow_Desugar_Tuples.wordarray_put2_u32"
  apply (rule shallow_tuples_rel_funI)
  apply (unfold Generated_Shallow_Desugar.wordarray_put2_u32_def Generated_Shallow_Desugar_Tuples.wordarray_put2_u32_def id_def)
  by (assumption |
      rule shallow_tuples_basic_bucket ShallowTuplesRules_Generated
           ShallowTuplesThms_Generated ShallowTuplesThms_Generated[THEN shallow_tuples_rel_funD])+


lemma shallow_tuples__add [ShallowTuplesThms_Generated]:
  "shallow_tuples_rel Generated_Shallow_Desugar.add Generated_Shallow_Desugar_Tuples.add"
  apply (rule shallow_tuples_rel_funI)
  apply (unfold Generated_Shallow_Desugar.add_def Generated_Shallow_Desugar_Tuples.add_def id_def)
  by (assumption |
      rule shallow_tuples_basic_bucket ShallowTuplesRules_Generated
           ShallowTuplesThms_Generated ShallowTuplesThms_Generated[THEN shallow_tuples_rel_funD])+


lemma shallow_tuples__sum_arr [ShallowTuplesThms_Generated]:
  "shallow_tuples_rel Generated_Shallow_Desugar.sum_arr Generated_Shallow_Desugar_Tuples.sum_arr"
  apply (rule shallow_tuples_rel_funI)
  apply (unfold Generated_Shallow_Desugar.sum_arr_def Generated_Shallow_Desugar_Tuples.sum_arr_def id_def)
  by (assumption |
      rule shallow_tuples_basic_bucket ShallowTuplesRules_Generated
           ShallowTuplesThms_Generated ShallowTuplesThms_Generated[THEN shallow_tuples_rel_funD])+


lemma shallow_tuples__dec [ShallowTuplesThms_Generated]:
  "shallow_tuples_rel Generated_Shallow_Desugar.dec Generated_Shallow_Desugar_Tuples.dec"
  apply (rule shallow_tuples_rel_funI)
  apply (unfold Generated_Shallow_Desugar.dec_def Generated_Shallow_Desugar_Tuples.dec_def id_def)
  by (assumption |
      rule shallow_tuples_basic_bucket ShallowTuplesRules_Generated
           ShallowTuplesThms_Generated ShallowTuplesThms_Generated[THEN shallow_tuples_rel_funD])+


lemma shallow_tuples__dec_arr [ShallowTuplesThms_Generated]:
  "shallow_tuples_rel Generated_Shallow_Desugar.dec_arr Generated_Shallow_Desugar_Tuples.dec_arr"
  apply (rule shallow_tuples_rel_funI)
  apply (unfold Generated_Shallow_Desugar.dec_arr_def Generated_Shallow_Desugar_Tuples.dec_arr_def id_def)
  by (assumption |
      rule shallow_tuples_basic_bucket ShallowTuplesRules_Generated
           ShallowTuplesThms_Generated ShallowTuplesThms_Generated[THEN shallow_tuples_rel_funD])+


lemma shallow_tuples__inc [ShallowTuplesThms_Generated]:
  "shallow_tuples_rel Generated_Shallow_Desugar.inc Generated_Shallow_Desugar_Tuples.inc"
  apply (rule shallow_tuples_rel_funI)
  apply (unfold Generated_Shallow_Desugar.inc_def Generated_Shallow_Desugar_Tuples.inc_def id_def)
  by (assumption |
      rule shallow_tuples_basic_bucket ShallowTuplesRules_Generated
           ShallowTuplesThms_Generated ShallowTuplesThms_Generated[THEN shallow_tuples_rel_funD])+


lemma shallow_tuples__inc_arr [ShallowTuplesThms_Generated]:
  "shallow_tuples_rel Generated_Shallow_Desugar.inc_arr Generated_Shallow_Desugar_Tuples.inc_arr"
  apply (rule shallow_tuples_rel_funI)
  apply (unfold Generated_Shallow_Desugar.inc_arr_def Generated_Shallow_Desugar_Tuples.inc_arr_def id_def)
  by (assumption |
      rule shallow_tuples_basic_bucket ShallowTuplesRules_Generated
           ShallowTuplesThms_Generated ShallowTuplesThms_Generated[THEN shallow_tuples_rel_funD])+


lemma shallow_tuples__mul [ShallowTuplesThms_Generated]:
  "shallow_tuples_rel Generated_Shallow_Desugar.mul Generated_Shallow_Desugar_Tuples.mul"
  apply (rule shallow_tuples_rel_funI)
  apply (unfold Generated_Shallow_Desugar.mul_def Generated_Shallow_Desugar_Tuples.mul_def id_def)
  by (assumption |
      rule shallow_tuples_basic_bucket ShallowTuplesRules_Generated
           ShallowTuplesThms_Generated ShallowTuplesThms_Generated[THEN shallow_tuples_rel_funD])+


lemma shallow_tuples__mul_arr [ShallowTuplesThms_Generated]:
  "shallow_tuples_rel Generated_Shallow_Desugar.mul_arr Generated_Shallow_Desugar_Tuples.mul_arr"
  apply (rule shallow_tuples_rel_funI)
  apply (unfold Generated_Shallow_Desugar.mul_arr_def Generated_Shallow_Desugar_Tuples.mul_arr_def id_def)
  by (assumption |
      rule shallow_tuples_basic_bucket ShallowTuplesRules_Generated
           ShallowTuplesThms_Generated ShallowTuplesThms_Generated[THEN shallow_tuples_rel_funD])+


end