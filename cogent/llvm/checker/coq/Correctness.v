From Coq Require Import List String ZArith.

From ITree Require Import ITree ITreeFacts.
From Vellvm Require Import LLVMAst LLVMEvents TopLevel Handlers InterpreterMCFG TopLevelRefinements
  DynamicTypes CFG TypToDtyp InterpretationStack SymbolicInterpreter DenotationTheory ScopeTheory
  DynamicValues ExpLemmas Coqlib NoFailure AListFacts.

From Checker Require Import Denotation DenotationTheory Cogent Compiler Utils.Tactics Invariants
  HelixLib.Correctness_Prelude HelixLib.BidBound HelixLib.IdLemmas.

Import ListNotations.
Import AlistNotations.

Import ExpTactics.
Import ProofMode.

Section Expressions.

  Definition ocfg_res : Type := (block_id * block_id) + uvalue. 

  (* From Helix *)
  Definition branches (to : block_id) : Rel_cfg_T uval ocfg_res :=
    fun _ '(m, (l, (g, res))) => exists from, res ≡ inl (from, to).

  Definition compile_expr_post (i : im) (γ : ctx) (s1 s2 : IRState) (to : block_id)
                               (l : local_env) : Rel_cfg_T uval ocfg_res :=
    lift_Rel_cfg (state_invariant γ s2) ⩕
    correct_result_T γ s1 s2 i ⩕
    branches to ⩕
    (fun _ '(_, (l', _)) => local_scope_modif s1 s2 l l').

  Lemma compile_expr_correct :
    forall (e : expr) (γ : ctx) (s1 s2 : IRState)
           (v : im) (next_bid entry_bid prev_bid : block_id) (blks : ocfg typ)
           (memC : memoryC) (g : global_env) (l : local_env) (memV : memoryV),
      compile_expr e next_bid s1 ≡ inr (s2, (v, entry_bid, blks)) ->
      no_failure (interp_expr (E := E_cfg) (denote_expr γ e) memC) ->
      bid_bound s1 next_bid ->
      state_invariant γ s1 memC (memV, (l, g)) ->
      eutt
        (succ_cfg (compile_expr_post v γ s1 s2 next_bid l))
        (interp_expr (denote_expr γ e) memC)
        (interp_cfg (denote_ocfg (convert_typ [] blks) (prev_bid, entry_bid)) g l memV).
  Proof.
    induction e using expr_ind'; intros * COMPILE NOFAIL NEXT PRE.
    - (* Unit *)
      cbn* in *; simp.
      cbn*.
      rewrite denote_ocfg_unfold_not_in.
      cvred.
      apply eutt_Ret; split; [ | split; [ | split]]; cbn; eauto.
      intros.
      typ_to_dtyp_simplify.
      unfold denote_exp; cbn.
      go; reflexivity.
      apply local_scope_modif_refl.
      apply find_block_nil.
    - (* Lit l *)
      cbn* in *; simp.
      cbn*.
      rewrite denote_ocfg_unfold_not_in.
      cvred.
      apply eutt_Ret; split; [ | split; [ | split]]; cbn; eauto.
      intros.
      destruct l;
        simpl; typ_to_dtyp_simplify;
        unfold denote_exp; cbn;
        go; reflexivity.
      apply local_scope_modif_refl.
      apply find_block_nil.
    - (* LVar i *)
      cbn* in *; simp.
      rewrite denote_ocfg_unfold_not_in.
      cvred.
      unfold option_throw in *. simp.
      cbn; cred.
      apply eutt_Ret; split; [ | split; [ | split]]; cbn; eauto.
      intros.
      unfold id in *.
      cbn* in *.
      destruct PRE as [MEM WF].
      unfold memory_invariant in MEM.
      specialize (MEM _ _ _ Heqo0 Heqo).
      unfold correct_result in MEM.
      specialize (MEM l' H H0).
      assumption.
      apply local_scope_modif_refl.
      apply failure_expr_throw in NOFAIL.
      contradiction.
      apply find_block_nil.
    - (* Let e1 e2 *)
      pose proof COMPILE as COMPILE'.
      cbn* in COMPILE'; simp.
      rename s1 into pre_state, i into mid_state, i1 into post_state.
      rename Heqs into COMPILE_e1, Heqs1 into COMPILE_e2.
      
      specialize (IHe1 γ _ _ _ _ _ entry_bid _ memC g l memV COMPILE_e1).
      forward IHe1.
      eapply no_failure_expr_bind_prefix; exact NOFAIL.
      forward IHe1.
      (* don't like manual instantiation here *)
      apply bid_bound_incBlockNamed with (name := "Let") (s1 := pre_state).
      solve_prefix.
      reflexivity.
      forward IHe1.
      apply state_invariant_new_block. (* unproven lemma *)
      assumption.
      
      rewrite convert_typ_ocfg_app.
      rewrite denote_ocfg_app.
      (* 2 : {
        idtac.
        unfold no_reentrance.
        rewrite convert_typ_outputs, inputs_convert_typ, outputs_cons.
        unfold successors, terminator_outputs, blk_term.
        simpl.
        apply list_disjoint_cons_l.
        admit.
      } *)
      admit.
      admit.
    - (* Prim op os *)
      cbn* in *; simp.
      admit.
    - (* If e1 e2 e3 *)
      admit.
    - (* Cast t e*)
      admit.
    - (* Struct ts es *)
      admit.
    - (* Member e f *)
      admit.
    - (* Take e1 f e2 *)
      admit.
    - (* Put e1 f e2 *)
      admit.
    - (* Con ts n e *)
      admit.
    - (* Promote t e *)
      admit.
    - (* Esac ts e *)
      admit.
    - (* Case ts e1 n e2 e3 *)
      admit.
    - (* Fun e *)
      admit.
    - (* App e1 e2 *)
      admit.
  Admitted.

End Expressions.

Section TopLevel.

  Definition vellvm_prog : Type := toplevel_entities typ (LLVMAst.block typ * list (LLVMAst.block typ)).
  Definition semantics_cogent (p : cogent_prog) : failT (itree E_mcfg) (memoryC * uval) := 
    interp_cogent (denote_program p) "main" UUnit empty_memory.

  (* placeholder *)
  Definition TT {A B} (x: A) (y: B):= True.

  Lemma compiler_correct :
    forall (c : cogent_prog) (ll : vellvm_prog),
      compile_cogent c ≡ inr ll ->
      eutt TT (semantics_cogent c) (semantics_llvm ll).
  Proof.
  Abort.

End TopLevel.
