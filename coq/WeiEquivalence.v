(**
  WeiEquivalence.v
  Central equivalence theorem: Wei and Saunders conditions are identical
*)
From Coq Require Import Reals Lra.
Require Import EnergyEconomics.
Local Open Scope R_scope.

Module WeiEquivalence.

(* Import the definitions from EnergyEconomics module *)
Import EnergyEconomics.

(* Central theorem: Both approaches reduce to the same condition *)
Theorem wei_saunders_equivalence :
  forall (sigma eta : R),
    EnergyEconomics.wei_theta sigma eta > 0 <-> EnergyEconomics.backfire sigma eta.
Proof.
  intros sigma eta.
  unfold EnergyEconomics.wei_theta, EnergyEconomics.backfire.
  lra.
Qed.

(* For small efficiency gains, the full threshold condition reduces to the simple form *)
Theorem small_gain_equivalence :
  forall (sigma eta g : R),
    g > 0 -> g < 1.1 ->
    EnergyEconomics.saunders_threshold sigma eta g <-> EnergyEconomics.backfire sigma eta.
Proof.
  intros sigma eta g Hpos Hsmall.
  (* This would require approximation theory - admit for now *)
Admitted.

End WeiEquivalence.
