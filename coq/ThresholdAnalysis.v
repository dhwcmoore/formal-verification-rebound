From Coq Require Import Reals Lra.
Open Scope R_scope.

(* Core threshold condition for backfire *)
Definition backfire_condition (sigma eta g : R) : Prop :=
  (sigma - 1) * ln g + eta * (1 - 1/g) > 0.

Theorem small_gain_threshold_approximation :
  forall (sigma eta epsilon : R),
    epsilon > 0 -> epsilon < 0.1 ->
    (sigma - 1) * epsilon + eta * epsilon > 0 <->
    sigma + eta > 1.
Proof.
  intros sigma eta epsilon Heps_pos Heps_small.
  rewrite <- Rmult_plus_distr_r.
  replace ((sigma - 1) + eta) with (sigma + eta - 1) by lra.
  split.
  - intro H.
    (* H: (sigma + eta - 1) * epsilon > 0, which means 0 < (sigma + eta - 1) * epsilon *)
    assert (Hrewrite : 0 * epsilon < (sigma + eta - 1) * epsilon).
    { rewrite Rmult_0_l. exact H. }
    apply (Rmult_lt_reg_r epsilon 0 (sigma + eta - 1)) in Hrewrite; [| exact Heps_pos].
    lra.
  - intro H.
    (* H: sigma + eta > 1, so sigma + eta - 1 > 0 *)
    assert (Hpos : sigma + eta - 1 > 0) by lra.
    apply Rmult_lt_0_compat; [exact Hpos | exact Heps_pos].
Qed.
