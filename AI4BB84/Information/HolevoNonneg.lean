import QuantumInfo.Finite.Entropy.Relative
import QuantumInfo.Finite.Entanglement
import AI4BB84.Information.Holevo

/-!
# Nonnegativity of the Holevo information

  `holevoChi_nonneg : 0 ≤ holevoChi e`  (under positivity of `e.distr`)

i.e., the concavity statement `Σᵢ pᵢ Sᵥₙ(ρᵢ) ≤ Sᵥₙ(mix e)`. The proof
goes via Klein's inequality applied componentwise, using PhysLib's
`qRelativeEnt_eq_neg_Sᵥₙ_add` plus linearity of the Hilbert–Schmidt inner
product to push the sum past the inner.

The hypothesis `∀ i, 0 < (e.distr i : ℝ)` is sufficient for BB84's
uniform-Bool distribution. Removing it (handling zero-probability
components) is a separate generalization.
-/

open MState
open Ensemble
open scoped InnerProductSpace RealInnerProductSpace

namespace AI4BB84

variable {d α : Type*} [Fintype d] [DecidableEq d] [Fintype α] [DecidableEq α]

/-! ### Infrastructure for the Klein-inequality proof of `holevoChi_nonneg`

The full proof of `holevoChi_nonneg` (concavity of `Sᵥₙ`) goes by Klein's
inequality applied componentwise:

```
   Sᵥₙ ρᵢ ≤ -⟪ρᵢ.M, (mix e).M.log⟫              (Klein, support cond.)
⇒  pᵢ Sᵥₙ ρᵢ ≤ -pᵢ ⟪ρᵢ.M, (mix e).M.log⟫       (× pᵢ ≥ 0)
⇒  ∑ᵢ pᵢ Sᵥₙ ρᵢ ≤ -⟪∑ᵢ pᵢ • ρᵢ.M, (mix e).M.log⟫   (linearity of inner)
                = -⟪(mix e).M, (mix e).M.log⟫   (mix_M_eq_sum)
                = Sᵥₙ (mix e)                     (Sᵥₙ_eq_neg_trace_log + comm)
```

The HermitianMat-level mix decomposition (`mix_M_eq_sum`) and the
support-condition lemma (`mix_ker_le_states_ker`) below are the
load-bearing pieces. The remaining steps require careful EReal/ℝ
conversion of `qRelativeEnt` (an `ENNReal`) and chained linearity of
`HermitianMat.inner`. Tracked as the next step in
`PROOF_LOG/holevo-chi.md`.
-/

/-! ### HermitianMat-level decomposition of the mixture -/

/-- The mixture's HermitianMat is the convex combination of components'
HermitianMats. Lifts the matrix-level `Ensemble.mix_of` to HermitianMat. -/
theorem mix_M_eq_sum (e : MEnsemble d α) :
    (mix e).M = ∑ i : α, (e.distr i : ℝ) • (e.states i).M := by
  apply HermitianMat.ext
  rw [HermitianMat.mat_finset_sum]
  show (mix e).m = _
  rw [mix_of]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rfl

/-! ### Each component is dominated by the mixture -/

/-- Each weighted component is ≤ the mixture in the PSD order. -/
private theorem smul_states_le_mix (e : MEnsemble d α) (i : α) :
    (e.distr i : ℝ) • (e.states i).M ≤ (mix e).M := by
  rw [mix_M_eq_sum e]
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ (e.distr j : ℝ) • (e.states j).M :=
    fun j _ => smul_nonneg (e.distr j).zero_le_coe (e.states j).nonneg
  exact Finset.single_le_sum hnn (Finset.mem_univ i)

/-- Helper: when `pᵢ > 0`, the mixture's kernel is contained in `ρᵢ`'s kernel. -/
theorem mix_ker_le_states_ker (e : MEnsemble d α)
    (i : α) (h : 0 < (e.distr i : ℝ)) :
    (mix e).M.ker ≤ (e.states i).M.ker := by
  have hpi_smul_le := smul_states_le_mix e i
  have hsmul_nonneg : 0 ≤ (e.distr i : ℝ) • (e.states i).M :=
    smul_nonneg h.le (e.states i).nonneg
  have hker_le := HermitianMat.ker_antitone hsmul_nonneg hpi_smul_le
  calc (mix e).M.ker
      ≤ ((e.distr i : ℝ) • (e.states i).M).ker := hker_le
    _ = (e.states i).M.ker :=
        HermitianMat.ker_pos_smul (A := (e.states i).M) (ne_of_gt h)

/-! ### Klein's inequality reformulated for our use -/

/-- Klein's inequality: for density operators with `σ.M.ker ≤ ρ.M.ker`,
`Sᵥₙ ρ ≤ −⟪ρ.M, σ.M.log⟫`. Reformulation of `qRelativeEnt_ker` plus
nonnegativity of `qRelativeEnt`, plus `Sᵥₙ_eq_neg_trace_log`. -/
private theorem klein_real (ρ σ : MState d) (h : σ.M.ker ≤ ρ.M.ker) :
    Sᵥₙ ρ ≤ -(⟪ρ.M, (σ.M).log⟫ : ℝ) := by
  -- (qRelativeEnt ρ σ).toEReal = ⟪ρ.M, ρ.M.log - σ.M.log⟫  (qRelativeEnt_ker)
  have h_eq := qRelativeEnt_ker h
  -- ENNReal.toReal is nonneg; thus (.toEReal).toReal is nonneg
  have h_toReal_nonneg : (0 : ℝ) ≤ (qRelativeEnt ρ σ).toReal :=
    ENNReal.toReal_nonneg
  -- Connect (qRelativeEnt ρ σ).toReal to the inner product expression.
  -- We have h_eq : (qRelativeEnt ρ σ).toEReal = (⟪ρ.M, ρ.M.log - σ.M.log⟫ : EReal)
  -- Both sides applied via `.toReal`:
  --   LHS: ((qRelativeEnt ρ σ).toEReal).toReal = (qRelativeEnt ρ σ).toReal.
  --   RHS: ((⟪…⟫ : ℝ) : EReal).toReal = ⟪…⟫.
  have h_real_eq : (qRelativeEnt ρ σ).toReal = ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
    have := congrArg EReal.toReal h_eq
    simpa [EReal.toReal_coe_ennreal, EReal.toReal_coe] using this
  rw [h_real_eq] at h_toReal_nonneg
  -- 0 ≤ ⟪ρ.M, ρ.M.log - σ.M.log⟫ = ⟪ρ.M, ρ.M.log⟫ - ⟪ρ.M, σ.M.log⟫.
  rw [HermitianMat.inner_sub_left] at h_toReal_nonneg
  -- ⟪ρ.M, σ.M.log⟫ ≤ ⟪ρ.M, ρ.M.log⟫.
  have h_swap : ⟪ρ.M, σ.M.log⟫ ≤ ⟪ρ.M, ρ.M.log⟫ := by linarith
  -- Sᵥₙ ρ = -⟪ρ.M.log, ρ.M⟫ = -⟪ρ.M, ρ.M.log⟫.
  have h_S : Sᵥₙ ρ = -⟪ρ.M, ρ.M.log⟫ := by
    rw [Sᵥₙ_eq_neg_trace_log, neg_inj, HermitianMat.inner_comm]
  linarith

/-! ### Finset linearity helper for the inner product -/

/-- Finset-sum form of the inner product's linearity in the first argument. -/
theorem inner_finset_sum_left
    (s : Finset α) (f : α → HermitianMat d ℂ) (B : HermitianMat d ℂ) :
    ⟪∑ i ∈ s, f i, B⟫ = ∑ i ∈ s, ⟪f i, B⟫ := by
  induction s using Finset.induction_on with
  | empty => simp [HermitianMat.inner_eq_re_trace]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
          HermitianMat.inner_add_left, ih]

/-! ### Main result: nonnegativity of Holevo `χ` -/

/-- **Concavity of von Neumann entropy / nonnegativity of Holevo `χ`**:
for any mixed-state ensemble with strictly positive index distribution,
`0 ≤ holevoChi e`.

The proof is Klein's inequality applied componentwise (`klein_real`),
combined by the linearity of `HermitianMat.inner`, with the mixture's
HermitianMat decomposition (`mix_M_eq_sum`) used to recognize the sum as
the mixture itself, and `Sᵥₙ_eq_neg_trace_log` for the final identification. -/
theorem holevoChi_nonneg (e : MEnsemble d α)
    (h_pos : ∀ i, 0 < (e.distr i : ℝ)) :
    0 ≤ holevoChi e := by
  unfold holevoChi
  rw [sub_nonneg]
  -- Goal: ∑ i, (e.distr i : ℝ) * Sᵥₙ (e.states i) ≤ Sᵥₙ (mix e)
  -- Step 1: pointwise Klein.
  have h_each : ∀ i, (e.distr i : ℝ) * Sᵥₙ (e.states i) ≤
      -((e.distr i : ℝ) * ⟪(e.states i).M, (mix e).M.log⟫) := by
    intro i
    have hKlein := klein_real (e.states i) (mix e) (mix_ker_le_states_ker e i (h_pos i))
    have hpi := (h_pos i).le
    nlinarith
  -- Step 2: sum the pointwise inequalities.
  have h_sum : ∑ i, (e.distr i : ℝ) * Sᵥₙ (e.states i) ≤
      ∑ i, -((e.distr i : ℝ) * ⟪(e.states i).M, (mix e).M.log⟫) :=
    Finset.sum_le_sum (fun i _ => h_each i)
  -- Step 3: simplify the right-hand side to Sᵥₙ (mix e).
  have h_rhs : ∑ i, -((e.distr i : ℝ) * ⟪(e.states i).M, (mix e).M.log⟫) =
      Sᵥₙ (mix e) := by
    simp only [Finset.sum_neg_distrib]
    -- ∑ i, ((e.distr i : ℝ) * ⟪(e.states i).M, (mix e).M.log⟫) =
    --   ⟪∑ i, (e.distr i : ℝ) • (e.states i).M, (mix e).M.log⟫
    have h_lin : ∑ i, ((e.distr i : ℝ) * ⟪(e.states i).M, (mix e).M.log⟫) =
        ⟪∑ i, (e.distr i : ℝ) • (e.states i).M, (mix e).M.log⟫ := by
      rw [inner_finset_sum_left]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [HermitianMat.inner_smul_left]
    rw [h_lin, ← mix_M_eq_sum]
    -- -⟪(mix e).M, (mix e).M.log⟫ = Sᵥₙ (mix e)
    rw [Sᵥₙ_eq_neg_trace_log, HermitianMat.inner_comm]
  linarith

end AI4BB84
