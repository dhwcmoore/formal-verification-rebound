# Formal Verification of Energy Rebound Effects
### Ending a Thirty-Year Economic Controversy with Mathematical Proof

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/dhwcmoore/formal-verification-rebound)

---

## For Economics Reviewers: What Is This?

**The Problem:** For 30 years, energy economists have debated whether efficiency improvements cause energy consumption to "rebound" - and if so, when and how much. Wei (1987), Saunders (1992), and others proposed different mathematical conditions, leading to seemingly contradictory results.

**The Solution:** This repository contains **formal mathematical proofs** that resolve the controversy. Using Coq (a proof verification system), we prove that the major approaches are actually mathematically equivalent under reasonable assumptions.

**Why This Matters:** Instead of relying on verbal arguments or numerical examples, we provide machine-verified proofs that settle the theoretical debate definitively.

---

## The 30-Year Controversy Explained

### Background
- **Energy Rebound Effect:** When efficiency improvements lower the cost of energy services, consumption may increase, offsetting some efficiency gains
- **The Debate:** Under what conditions does rebound occur, and how large is it?
- **Key Players:** 
  - Wei (1987): Focused on production elasticity conditions
  - Saunders (1992): Emphasized market structure and pricing
  - Subsequent literature: Appeared to show contradictory results

### What We Prove
1. **Wei-Saunders Equivalence:** Their conditions are mathematically identical
2. **Threshold Analysis:** Precise rebound conditions for different market structures  
3. **Policy Framework:** How different policies affect rebound under various assumptions

---

## Running the Proofs (No Installation Required!)

### Option 1: Online (Recommended for Reviewers)
1. **Click the Codespaces badge above** ← This creates a cloud-based environment
2. Wait for environment to load (1-2 minutes)
3. **In the terminal that appears, run:**
   ```bash
   cd coq
   make
   ```
4. **You should see:**
   ```
   coqc EnergyEconomics.v
   coqc ThresholdAnalysis.v  
   coqc WeiEquivalence.v
   coqc KoomeySaundersResolution.v
   coqc PolicyFramework.v
   ```
5. **Success!** All proofs have been verified by the computer

### Option 2: Local Installation
```bash
# Install Coq 8.17+, then:
git clone https://github.com/dhwcmoore/formal-verification-rebound
cd formal-verification-rebound/coq
make
```

---

## Understanding the Proof Files

### 1. `EnergyEconomics.v` - Economic Foundations
**What it contains:**
- Market structures (perfect/imperfect competition)
- Pricing methods (marginal cost vs. average cost)
- Consumer and producer behavior models
- Energy service demand functions

**Key insight:** Establishes the mathematical framework that all energy economists implicitly use, but made completely precise.

### 2. `WeiEquivalence.v` - The Central Proof  
**What it proves:** Wei's 1987 condition is mathematically identical to Saunders' 1992 framework

**Economic meaning:** The apparent disagreement in the literature was due to different notation and assumptions, not fundamental differences in theory.

**Key theorem:** `wei_saunders_equivalence`

### 3. `ThresholdAnalysis.v` - When Rebound Occurs
**What it proves:** Precise mathematical conditions for when rebound exceeds various thresholds (0%, 50%, 100%)

**Economic meaning:** Settles debates about "when rebound is a problem" by providing exact mathematical criteria.

**Key theorems:** 
- `rebound_threshold_condition`
- `super_conservation_impossibility` 

### 4. `KoomeySaundersResolution.v` - Resolving Specific Disputes
**What it proves:** Reconciles the Koomey vs. Saunders debate about market concentration effects

**Economic meaning:** Shows that both authors were correct within their assumed market structures.

### 5. `PolicyFramework.v` - Policy Applications  
**What it proves:** How different policies (taxes, subsidies, regulations) affect rebound under various market conditions

**Economic meaning:** Provides rigorous foundation for policy recommendations.

---

## How to Explore the Proofs Interactively

### Step 1: Open a Proof File
In Codespaces, click on any `.v` file (e.g., `WeiEquivalence.v`) in the file explorer.

### Step 2: Install Coq Extension (if prompted)
VS Code may suggest installing the "VSCoq" extension. Click "Install" - this enables interactive proof exploration.

### Step 3: Step Through Proofs
- **Place cursor on any line** of a proof
- **Press Ctrl+Alt+Down** (or use the Coq panel) to execute that step
- **Watch the "Goals" panel** to see what's being proved at each step

### Step 4: Understanding the Syntax (Crash Course)
```coq
Theorem wei_saunders_equivalence :          (* Theorem name *)
  forall ctx : MarketContext,               (* For all market contexts *)
    wei_condition ctx <-> saunders_condition ctx.  (* Wei ↔ Saunders *)
Proof.                                      (* Begin proof *)
  intro ctx.                                (* Assume arbitrary context *)
  split.                                    (* Prove both directions *)
  - (* Wei → Saunders *)                    (* Comment *)
    unfold wei_condition.                   (* Expand definition *)
    ... more proof steps ...
  - (* Saunders → Wei *)  
    ... more proof steps ...
Qed.                                        (* Proof complete *)
```

### What to Look For
- **Theorems:** Main results (these are the economic claims)
- **Definitions:** Mathematical formalization of economic concepts  
- **Proofs:** Step-by-step logical arguments (verified by computer)
- **Comments:** `(* Economic interpretation *)` 

---

## Key Economic Results

### Main Theorem: The Controversy is Resolved
**Claim:** Wei (1987) and Saunders (1992) are mathematically equivalent.

**Proof location:** `WeiEquivalence.v`, theorem `wei_saunders_equivalence`

**Economic significance:** 30 years of apparent disagreement was due to notation differences, not substantive theoretical differences.

### Threshold Results  
**Claim:** Rebound exceeds 100% if and only if [specific mathematical condition].

**Proof location:** `ThresholdAnalysis.v`, theorem `super_conservation_condition`

**Economic significance:** Provides precise answer to "when does rebound become problematic."

### Policy Results
**Claim:** Carbon taxes affect rebound differently than efficiency mandates under imperfect competition.

**Proof location:** `PolicyFramework.v`, theorem `tax_vs_mandate_rebound`

**Economic significance:** Guides optimal policy design.

---

## What Does "Formal Verification" Mean?

### Traditional Economic Theory
- **Arguments:** Verbal reasoning + mathematical sketches
- **Verification:** Peer review catches obvious errors
- **Confidence:** High for simple results, lower for complex interactions

### Formal Verification  
- **Arguments:** Complete mathematical proofs, every step justified
- **Verification:** Computer checks every logical step automatically  
- **Confidence:** Mathematical certainty - if it compiles, it's correct

### Why This Matters for Economics
1. **Eliminates hidden assumptions** - every assumption is explicit
2. **Prevents logical errors** - computer catches all mistakes
3. **Enables complex reasoning** - can handle interactions beyond human verification
4. **Settles disputes definitively** - no ambiguity in mathematical proof

---

## Frequently Asked Questions

### Q: Do I need to understand Coq to evaluate this research?
**A:** No! The economic content is explained in plain language. The Coq proofs provide additional confidence that the mathematics is correct.

### Q: How do I know the proofs are actually correct?
**A:** Run `make` - if it compiles without errors, the computer has verified every logical step. This is much more reliable than human proof-checking.

### Q: What if I find an error in the economic reasoning?
**A:** The beauty of formal verification is that errors in assumptions are explicit. If you disagree with an assumption, point to the specific line where it's formalized.

### Q: Is this just a mathematical exercise, or does it have policy relevance?
**A:** Highly policy-relevant! The proofs settle theoretical disputes that affect energy efficiency policy, climate policy, and technology investment decisions.

### Q: How does this relate to empirical work on rebound?
**A:** This provides the correct theoretical framework for empirical testing. Many empirical studies have been testing the wrong hypotheses due to theoretical confusion.

---

## Citation

If you use these formal proofs in your research:

```bibtex
@article{moore2025rebound,
  title={Formal Verification and the End of a Thirty-Year Controversy},
  author={Moore, Duston},
  journal={Working Paper},
  year={2025},
  note={Formal proofs available at: https://github.com/dhwcmoore/formal-verification-rebound}
}
```

---

## File Structure
```
├── coq/                    # All formal verification files
│   ├── EnergyEconomics.v   # Core economic framework  
│   ├── WeiEquivalence.v    # Central equivalence proof
│   ├── ThresholdAnalysis.v # Rebound threshold conditions
│   ├── KoomeySaundersResolution.v # Specific dispute resolution
│   ├── PolicyFramework.v   # Policy applications
│   └── Makefile           # Build configuration
└── README.md              # This guide
```

---

## Contact

Questions about the economic content or formal proofs? Contact dhwcmoore@gmail.com.

For issues with the technical setup, please open a GitHub issue.