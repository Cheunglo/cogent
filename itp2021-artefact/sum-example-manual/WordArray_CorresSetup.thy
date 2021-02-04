(*
This file is generated by Cogent and 
manually editted to provide a proper definition for 
heap_rel

*)

theory Generated_CorresSetup
imports "CogentCRefinement.Deep_Embedding_Auto"
"CogentCRefinement.Cogent_Corres"
"CogentCRefinement.Tidy"
"CogentCRefinement.Heap_Relation_Generation"
"CogentCRefinement.Type_Relation_Generation"
"Generated_ACInstall"
"Generated_TypeProof"
begin

(* Abstract function environment *)
consts user_\<xi>_0 :: "(funtyp, abstyp, ptrtyp) uabsfuns"
consts user_\<xi>_1 :: "(funtyp, abstyp, ptrtyp) uabsfuns"

(* C type and value relations *)

instantiation unit_t_C :: cogent_C_val
begin
  definition type_rel_unit_t_C_def: "\<And> r. type_rel r (_ :: unit_t_C itself) \<equiv> r = RUnit"
  definition val_rel_unit_t_C_def: "\<And> uv. val_rel uv (_ :: unit_t_C) \<equiv> uv = UUnit"
  instance ..
end

instantiation bool_t_C :: cogent_C_val
begin
definition type_rel_bool_t_C_def: "\<And> typ. type_rel typ (_ :: bool_t_C itself) \<equiv> (typ = RPrim Bool)"
definition val_rel_bool_t_C_def:
   "\<And> uv x. val_rel uv (x :: bool_t_C) \<equiv> (boolean_C x = 0 \<or> boolean_C x = 1) \<and>
     uv = UPrim (LBool (boolean_C x \<noteq> 0))"
instance ..
end
context update_sem_init begin
lemmas corres_if = corres_if_base[where bool_val' = boolean_C,
                     OF _ _ val_rel_bool_t_C_def[THEN meta_eq_to_obj_eq, THEN iffD1]]
end
(* C heap type class *)
class cogent_C_heap = cogent_C_val +
  fixes is_valid    :: "lifted_globals \<Rightarrow> 'a ptr \<Rightarrow> bool"
  fixes heap        :: "lifted_globals \<Rightarrow> 'a ptr \<Rightarrow> 'a"

(* ------------------- *)
(*This is where the manual editing is taking place. 
  Manually defining the type relation and value relation for word arrays *)

instantiation WordArray_u32_C :: cogent_C_val
begin
definition type_rel_WordArray_u32_C_def: 
  "type_rel typ (_ :: WordArray_u32_C itself) \<equiv> typ = RCon ''WordArray'' [RPrim (Num U32)]"
definition val_rel_WordArray_u32_C_def:
  "val_rel uv (x :: WordArray_u32_C) \<equiv> (\<exists>len arr. uv = UAbstract (UWA (TPrim (Num U32)) len arr) \<and> 
                                                  len = (SCAST(32 signed \<rightarrow> 32)(len_C x)) \<and>
                                                  arr = ptr_val (values_C x))"
instance ..
end

(*----------*)

local_setup \<open> local_setup_val_rel_type_rel_put_them_in_buckets "main_pp_inferred.c" \<close>
local_setup \<open> local_setup_instantiate_cogent_C_heaps_store_them_in_buckets "main_pp_inferred.c" \<close>
locale Generated = "main_pp_inferred" + update_sem_init
begin

(* Relation between program heaps *)
definition
  heap_rel_ptr ::
  "(funtyp, abstyp, ptrtyp) store \<Rightarrow> lifted_globals \<Rightarrow>
   ('a :: cogent_C_heap) ptr \<Rightarrow> bool"
where
  "\<And> \<sigma> h p.
    heap_rel_ptr \<sigma> h p \<equiv>
   (\<forall> uv.
     \<sigma> (ptr_val p) = Some uv \<longrightarrow>
     type_rel (uval_repr uv) TYPE('a) \<longrightarrow>
     is_valid h p \<and> val_rel uv (heap h p))"

lemma heap_rel_ptr_meta:
  "heap_rel_ptr = heap_rel_meta is_valid heap"
  by (simp add: heap_rel_ptr_def[abs_def] heap_rel_meta_def[abs_def])

(* ------------------- *)
(*This is where the manual editing is taking place. 
  Commenting out the automatic generation of heap_rel 
  and defining it manually *)

(*local_setup \<open> local_setup_heap_rel "main_pp_inferred.c" \<close>*)

definition
  heap_rel_ptr_w32 ::
  "(funtyp, abstyp, ptrtyp) store \<Rightarrow> lifted_globals \<Rightarrow>
   (32 word) ptr \<Rightarrow> bool"
where
  "\<And> \<sigma> h p.
    heap_rel_ptr_w32 \<sigma> h p \<equiv>
   (\<forall> uv.
     \<sigma> (ptr_val p) = Some uv \<longrightarrow>
     type_rel (uval_repr uv) TYPE(32 word) \<longrightarrow>
     is_valid_w32 h p \<and> val_rel uv (heap_w32 h p))"

lemma heap_rel_ptr_w32_meta:
  "heap_rel_ptr_w32 = heap_rel_meta is_valid_w32 heap_w32"
  by (simp add: heap_rel_ptr_w32_def[abs_def] heap_rel_meta_def[abs_def])

definition heap_rel
  where
  "heap_rel \<sigma> h \<equiv> (\<forall>(p :: WordArray_u32_C ptr). heap_rel_ptr \<sigma> h p) \<and> 
                    (\<forall>(p' :: 32 word ptr). heap_rel_ptr_w32 \<sigma> h p')"


(* ------------------- *)

definition state_rel :: "((funtyp, abstyp, ptrtyp) store \<times> lifted_globals) set"
where
  "state_rel  = {(\<sigma>, h). heap_rel \<sigma> h}"

lemmas val_rel_simps[ValRelSimp] =
  val_rel_word
  val_rel_ptr_def
  val_rel_unit_def
  val_rel_unit_t_C_def
  val_rel_bool_t_C_def
  val_rel_fun_tag
  val_rel_WordArray_u32_C_def

lemmas type_rel_simps[TypeRelSimp] =
  type_rel_word
  type_rel_ptr_def
  type_rel_unit_def
  type_rel_unit_t_C_def
  type_rel_bool_t_C_def
  type_rel_WordArray_u32_C_def

(* Generating the specialised take and put lemmas *)

local_setup \<open> local_setup_take_put_member_case_esac_specialised_lemmas "main_pp_inferred.c" \<close>
local_setup \<open> fold tidy_C_fun_def' Cogent_functions \<close>

end (* of locale *)


end
