(**
  EnergyEconomics.v
  Core definitions for formal verification of rebound debate
*)
From Coq Require Import Reals.
Local Open Scope R_scope.

Module EnergyEconomics.

(* Market context types *)
Inductive CompetitionType := PerfectCompetition | ImperfectCompetition.
Inductive PriceMethod := MarginalCost | NationalAverage.

(* Market context record *)
Record MarketContext := {
  competition_level  : CompetitionType;
  arbitrage_possible : bool;
  transaction_costs  : R
}.

(* Price method validity conditions *)
Definition price_method_valid (pm:PriceMethod) (mc:MarketContext) : Prop :=
  match pm with
  | MarginalCost =>
      mc.(competition_level) = PerfectCompetition
      /\ mc.(arbitrage_possible) = true
      /\ mc.(transaction_costs) < 0.1
  | NationalAverage =>
      mc.(competition_level) = ImperfectCompetition
  end.

(* Core elasticity parameters *)
Parameter substitution_elasticity : R.
Parameter income_elasticity : R.

(* Saunders threshold condition *)
Definition saunders_threshold (sigma eta g : R) : Prop :=
  (sigma - 1) * ln g + eta * (1 - 1/g) > 0.

(* Wei's theta parameter *)
Definition wei_theta (sigma eta : R) : R := 
  sigma + eta - 1.

(* Backfire condition *)
Definition backfire (sigma eta : R) : Prop := 
  sigma + eta > 1.

End EnergyEconomics.
