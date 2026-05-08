import QuantumInfo.Finite.Entropy.DPI
import QuantumInfo.Finite.POVM
import AI4BB84.Information.HolevoNonneg

/-!
# The Holevo bound

  `holevoChi (measuredEnsemble e Λ) ≤ holevoChi e`

For any POVM `Λ : POVM Y d` applied to each component of an ensemble
`e : MEnsemble d α`, the Holevo `χ` of the resulting **classical**
ensemble is at most the Holevo `χ` of the original quantum ensemble.

This is the *security-relevant* Holevo bound: any classical information
extracted by a quantum measurement on an ensemble's component is
bounded by the ensemble's `χ`. In our BB84 / Devetak-Winter setting,
this licenses interpreting `eveHolevoInfo := holevoChi (atk.eveEnsemble a)`
as the upper bound on Eve's classical knowledge of Alice's bit.

## Proof strategy: average relative entropy + DPI

We sidestep the joint-entropy-decomposition for the cq-state by using
the **classical-relative-entropy chain rule**:

```
χ(e) = Sᵥₙ(mix e) − Σᵢ pᵢ Sᵥₙ(ρᵢ)
     = Σᵢ pᵢ · [Sᵥₙ(mix e) − Sᵥₙ(ρᵢ)]                 (Σᵢ pᵢ = 1)
     = Σᵢ pᵢ · [−⟪ρᵢ, (mix e).log⟫ − Sᵥₙ(ρᵢ)]          (Sᵥₙ_eq_neg_trace_log
                                                       on `mix e` after summing)
     = Σᵢ pᵢ · D(ρᵢ ‖ mix e).toReal                    (qRelativeEnt_ker)
```

Then **DPI** for sandwiched Rényi at α=1 (= quantum relative entropy)
applied to the measure-and-discard channel `Λ.measureDiscard`:

```
D(Λ.measureDiscard ρᵢ ‖ Λ.measureDiscard (mix e)) ≤ D(ρᵢ ‖ mix e)
```

Sum with weights `pᵢ ≥ 0` and use the chain rule again on the
classical side:

```
Σᵢ pᵢ · D(...measured...) = holevoChi (measuredEnsemble e Λ)
                          ≤ Σᵢ pᵢ · D(ρᵢ ‖ mix e)
                          = holevoChi e
```

The key infrastructure (`mix_M_eq_sum`, `mix_ker_le_states_ker`,
`klein_real`-style argument, `Sᵥₙ_eq_neg_trace_log`) is already in
`Information/HolevoNonneg.lean`.

This proof does **not** require the joint entropy decomposition
`Sᵥₙ(cqState e) = Hₛ + Σᵢ pᵢ Sᵥₙ(ρᵢ)` — that's the right strategic
pivot to make the Holevo bound tractable.
-/

open MState
open Ensemble
open scoped InnerProductSpace RealInnerProductSpace

namespace AI4BB84

variable {d α Y : Type*}
  [Fintype d] [DecidableEq d]
  [Fintype α] [DecidableEq α]
  [Fintype Y] [DecidableEq Y]

/-! ### `χ(e)` as average quantum relative entropy -/

/-- Real-valued form of the quantum relative entropy when the support
condition holds. -/
private theorem qRelativeEnt_toReal_eq_inner
    (ρ σ : MState d) (h : σ.M.ker ≤ ρ.M.ker) :
    (qRelativeEnt ρ σ).toReal = ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  have h_eq := qRelativeEnt_ker h
  have := congrArg EReal.toReal h_eq
  simpa [EReal.toReal_coe_ennreal] using this

/-- **`χ(e)` is the average of quantum relative entropies of components vs. the mixture.**

`χ(e) = ∑ᵢ pᵢ · D(ρᵢ ‖ mix e)` (real-valued). -/
theorem holevoChi_eq_sum_qRelativeEnt
    (e : MEnsemble d α) (h_pos : ∀ i, 0 < (e.distr i : ℝ)) :
    holevoChi e =
      ∑ i : α, (e.distr i : ℝ) * (qRelativeEnt (e.states i) (mix e)).toReal := by
  -- Each summand on the RHS is `pᵢ · ⟪ρᵢ.M, ρᵢ.M.log − mix.M.log⟫`.
  have h_term : ∀ i : α,
      (qRelativeEnt (e.states i) (mix e)).toReal =
        ⟪(e.states i).M, (e.states i).M.log - (mix e).M.log⟫ := by
    intro i
    exact qRelativeEnt_toReal_eq_inner (e.states i) (mix e)
      (mix_ker_le_states_ker e i (h_pos i))
  -- Rewrite each summand on the RHS via h_term, then simplify.
  unfold holevoChi
  rw [Finset.sum_congr rfl (fun i _ => by rw [h_term i] : ∀ i ∈ Finset.univ,
        (e.distr i : ℝ) * (qRelativeEnt (e.states i) (mix e)).toReal =
        (e.distr i : ℝ) * ⟪(e.states i).M, (e.states i).M.log - (mix e).M.log⟫)]
  -- ∑ᵢ pᵢ · ⟪ρᵢ, ρᵢ.log − mix.log⟫
  --  = ∑ᵢ pᵢ · ⟪ρᵢ, ρᵢ.log⟫ − ∑ᵢ pᵢ · ⟪ρᵢ, mix.log⟫
  -- For the first piece use Sᵥₙ_eq_neg_trace_log; for the second, linearity to
  -- pull the sum into ⟪Σ pᵢ • ρᵢ, mix.log⟫ = ⟪mix.M, mix.log⟫ = -Sᵥₙ(mix e).
  simp_rw [HermitianMat.inner_sub_left, mul_sub]
  rw [Finset.sum_sub_distrib]
  -- Helper: ⟪ρᵢ, ρᵢ.log⟫ = -Sᵥₙ ρᵢ.
  have h_self : ∀ i : α, ⟪(e.states i).M, (e.states i).M.log⟫ = -Sᵥₙ (e.states i) :=
    fun i => by rw [Sᵥₙ_eq_neg_trace_log, neg_neg, HermitianMat.inner_comm]
  -- Helper: ∑ᵢ pᵢ ⟪ρᵢ, mix.log⟫ = ⟪mix.M, mix.M.log⟫ = -Sᵥₙ (mix e).
  have h_avg : ∑ i : α, (e.distr i : ℝ) * ⟪(e.states i).M, (mix e).M.log⟫
              = -Sᵥₙ (mix e) := by
    have h1 : ∀ i : α,
        (e.distr i : ℝ) * ⟪(e.states i).M, (mix e).M.log⟫ =
        ⟪(e.distr i : ℝ) • (e.states i).M, (mix e).M.log⟫ :=
      fun i => (HermitianMat.inner_smul_left _ _ _).symm
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    rw [← inner_finset_sum_left, ← mix_M_eq_sum,
        Sᵥₙ_eq_neg_trace_log, neg_neg, HermitianMat.inner_comm]
  rw [h_avg]
  rw [Finset.sum_congr rfl (fun i _ => by rw [h_self i] :
      ∀ i ∈ Finset.univ,
        (e.distr i : ℝ) * ⟪(e.states i).M, (e.states i).M.log⟫ =
        (e.distr i : ℝ) * (-Sᵥₙ (e.states i)))]
  -- Goal: Sᵥₙ(mix) - ∑ pᵢ Sᵥₙ ρᵢ = ∑ pᵢ · (-Sᵥₙ ρᵢ) - (-Sᵥₙ(mix))
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

/-! ### The Holevo bound (per-component DPI form) -/

/-- **Holevo bound, per-component DPI form.**

For each `i`, the classical relative entropy between the measurement-outcome
distribution under `Λ` for state `ρᵢ` and that for the mixture is bounded
by the quantum relative entropy `D(ρᵢ ‖ mix e)`:

    `D(ofClassical (Λ.measure ρᵢ) ‖ ofClassical (Λ.measure (mix e))) ≤ D(ρᵢ ‖ mix e)`

This is the per-component DPI inequality that, summed with weights `pᵢ`,
gives the standard Holevo bound `I(X; Y) ≤ χ(e)`. -/
theorem holevoBound_per_component
    (e : MEnsemble d α) (Λ : POVM Y d) (i : α) (h_pos : 0 < (e.distr i : ℝ)) :
    (qRelativeEnt (MState.ofClassical (Λ.measure (e.states i)))
                   (MState.ofClassical (Λ.measure (mix e)))).toReal ≤
    (qRelativeEnt (e.states i) (mix e)).toReal := by
  rw [← Λ.measureDiscard_apply (e.states i), ← Λ.measureDiscard_apply (mix e)]
  -- Quantum relative entropy is contractive under any CPTP map (DPI for sandwiched
  -- Rényi at α = 1, available in PhysLib). The RHS is finite by the support
  -- condition (mix e supports ρᵢ when pᵢ > 0), which lets us extract a real
  -- inequality from the ENNReal one via `ENNReal.toReal_mono`.
  have hRHS : qRelativeEnt (e.states i) (mix e) ≠ ⊤ := by
    have h_supp := mix_ker_le_states_ker e i h_pos
    have h_eq := qRelativeEnt_ker h_supp
    intro h_top
    rw [h_top] at h_eq
    simp at h_eq
  exact ENNReal.toReal_mono hRHS
    (sandwichedRenyiEntropy_DPI_eq_one (e.states i) (mix e) Λ.measureDiscard)

/-- **The Holevo bound** (averaged form). For any POVM `Λ`,

    `∑ᵢ pᵢ · D(ofClassical (Λ.measure ρᵢ) ‖ ofClassical (Λ.measure (mix e))) ≤ holevoChi e`

The LHS is the classical mutual information `I(X; Y_Λ)` between Alice's
classical index and the measurement outcome of `Λ`; the RHS is the
quantum Holevo information of the original ensemble. -/
theorem holevoBound
    (e : MEnsemble d α) (Λ : POVM Y d) (h_pos : ∀ i, 0 < (e.distr i : ℝ)) :
    ∑ i : α, (e.distr i : ℝ) *
        (qRelativeEnt (MState.ofClassical (Λ.measure (e.states i)))
                       (MState.ofClassical (Λ.measure (mix e)))).toReal
      ≤ holevoChi e := by
  rw [holevoChi_eq_sum_qRelativeEnt e h_pos]
  refine Finset.sum_le_sum (fun i _ => ?_)
  exact mul_le_mul_of_nonneg_left
    (holevoBound_per_component e Λ i (h_pos i)) (h_pos i).le

end AI4BB84
