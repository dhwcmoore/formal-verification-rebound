From Coq Require Import Reals Lra.
Require Import EnergyEconomics.
Local Open Scope R_scope.

Module PolicyFramework.

(* Capital market conditions *)
Inductive CapitalMarketType := 
| LiquidCapital     (* Easy access to investment capital *)
| ConstrainedCapital (* Limited capital availability *)
.

Record CapitalContext := {
  market_type : CapitalMarketType;
  investment_rate : R;  (* Rate of capital adjustment *)
  capacity_utilization : R  (* Current capacity utilization rate *)
}.

(* Extended Wei theta with capital adjustment *)
Definition wei_theta_capital (sigma eta theta_capital : R) : R := 
  sigma + eta + theta_capital - 1.

(* Capital amplification theorem *)
Theorem capital_amplifies_rebound :
  forall (sigma eta theta_c : R),
    theta_c > 0 -> 
    wei_theta_capital sigma eta theta_c > EnergyEconomics.wei_theta sigma eta.
Proof.
  intros sigma eta theta_c Hpos.
  unfold wei_theta_capital, EnergyEconomics.wei_theta.
  lra.
Qed.

(* Policy risk assessment based on capital conditions *)
Definition rebound_risk_with_capital (sigma eta : R) (ctx : CapitalContext) : R :=
  match ctx.(market_type) with
  | LiquidCapital => 
      (* Liquid capital amplifies rebound through capacity expansion *)
      EnergyEconomics.wei_theta sigma eta + ctx.(investment_rate) * 0.5
  | ConstrainedCapital => 
      (* Constrained capital dampens rebound *)
      EnergyEconomics.wei_theta sigma eta * (1 - ctx.(capacity_utilization) * 0.2)
  end.

(* Policy recommendation framework *)
Inductive PolicyRecommendation :=
| EfficiencyOnly          (* σ + η < 0.8 *)
| EfficiencyPlusCarbon    (* 0.8 ≤ σ + η < 1.2 *)
| ComprehensivePackage    (* σ + η ≥ 1.2 *)
.

Definition policy_selection (sigma eta : R) (ctx : CapitalContext) : PolicyRecommendation :=
  let risk := rebound_risk_with_capital sigma eta ctx in
  if Rlt_dec risk 0.8 then EfficiencyOnly
  else if Rlt_dec risk 1.2 then EfficiencyPlusCarbon  
  else ComprehensivePackage.

(* Connection to market structure resolution *)
Theorem capital_market_interaction :
  forall (sigma eta : R) (ctx : CapitalContext),
    ctx.(market_type) = LiquidCapital ->
    ctx.(investment_rate) > 0.1 ->
    rebound_risk_with_capital sigma eta ctx > EnergyEconomics.wei_theta sigma eta.
Proof.
  intros sigma eta ctx Hliquid Hrate.
  unfold rebound_risk_with_capital.
  rewrite Hliquid.
  unfold EnergyEconomics.wei_theta.
  (* From investment_rate > 0.1, derive investment_rate > 0 *)
  assert (Hpos : ctx.(investment_rate) > 0) by lra.
  (* Then show the multiplication is positive *)
  assert (Hmult_pos : ctx.(investment_rate) * 0.5 > 0).
  { apply Rmult_lt_0_compat; [exact Hpos | lra]. }
  lra.
Qed.

End PolicyFramework.
