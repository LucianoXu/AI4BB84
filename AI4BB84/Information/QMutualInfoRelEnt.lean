import QuantumInfo.Finite.Entropy.Relative
import AI4BB84.Information.PartialTraceInner

/-!
# `qMutualInfo` as quantum relative entropy

  `qMutualInfo ρ = D(ρ ‖ ρ_A ⊗ ρ_B)`

PhysLib's `qMutualInfo_as_qRelativeEnt` is currently stated as a `sorry`
(see `QuantumInfo/Finite/Entropy/Relative.lean:2138`). We prove a
**nonsingular** version here — sufficient for our BB84 / Holevo bound
application — building on the partial-trace inner identities from
`PartialTraceInner.lean` plus PhysLib's `log_kron`.

The proof is a textbook calculation:

```
D(ρ ‖ ρ_A ⊗ ρ_B) = -Sᵥₙ ρ - ⟪ρ.M, log(ρ_A ⊗ ρ_B)⟫       [qRelativeEnt_eq_neg_Sᵥₙ_add]
                 = -Sᵥₙ ρ - ⟪ρ.M, log ρ_A ⊗ 1 + 1 ⊗ log ρ_B⟫   [log_kron, NonSingular]
                 = -Sᵥₙ ρ - ⟪ρ.M, log ρ_A ⊗ 1⟫ - ⟪ρ.M, 1 ⊗ log ρ_B⟫   [linearity]
                 = -Sᵥₙ ρ - ⟪ρ.traceRight, log ρ_A⟫ - ⟪ρ.traceLeft, log ρ_B⟫   [partial trace]
                 = -Sᵥₙ ρ + Sᵥₙ ρ_A + Sᵥₙ ρ_B           [Sᵥₙ_eq_neg_trace_log + comm]
                 = qMutualInfo ρ                         [definition]
```

Where `ρ_A := ρ.traceRight`, `ρ_B := ρ.traceLeft`. The `[NonSingular]`
instances on the marginals ensure the relative entropy is finite and
the support condition for `qRelativeEnt_eq_neg_Sᵥₙ_add` holds vacuously.
-/

open scoped InnerProductSpace RealInnerProductSpace HermitianMat
open MState

namespace AI4BB84

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Nonempty dA] [Nonempty dB]

/-- `qMutualInfo` as quantum relative entropy, in the case both marginals
are nonsingular. -/
theorem qMutualInfo_eq_qRelativeEnt_marginals
    (ρ : MState (dA × dB))
    [hA : ρ.traceRight.M.NonSingular] [hB : ρ.traceLeft.M.NonSingular] :
    qMutualInfo ρ =
      ((qRelativeEnt ρ (ρ.traceRight ⊗ᴹ ρ.traceLeft)).toReal : ℝ) := by
  -- Notation
  set ρ_A := ρ.traceRight with hρA
  set ρ_B := ρ.traceLeft with hρB
  set σ := ρ_A ⊗ᴹ ρ_B with hσ
  -- The product σ is nonsingular as a kronecker of nonsingular HermitianMats.
  have hσ_ns : σ.M.NonSingular := by
    show (ρ_A.M ⊗ₖ ρ_B.M).NonSingular  -- by MState.prod definition
    exact HermitianMat.nonSingular_kron
  -- The support condition holds because σ is nonsingular: ker σ.M = ⊥ ≤ anything.
  have h_ker : σ.M.ker ≤ ρ.M.ker := by
    rw [HermitianMat.nonSingular_ker_bot]
    exact bot_le
  -- Step 1: extract the real-valued form of qRelativeEnt via qRelativeEnt_ker.
  have h_RE := qRelativeEnt_ker (ρ := ρ) (σ := σ) h_ker
  -- h_RE : (qRelativeEnt ρ σ).toEReal = ⟪ρ.M, ρ.M.log - σ.M.log⟫ (coerced to EReal)
  have h_real_RE : (qRelativeEnt ρ σ).toReal = ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
    have := congrArg EReal.toReal h_RE
    simpa [EReal.toReal_coe_ennreal] using this
  -- Step 2: expand inner_sub and σ.M.log via log_kron.
  rw [HermitianMat.inner_sub_left] at h_real_RE
  -- h_real_RE : (qRelativeEnt ρ σ).toReal = ⟪ρ.M, ρ.M.log⟫ - ⟪ρ.M, σ.M.log⟫
  -- Step 3: σ.M.log = ρ_A.M.log ⊗ 1 + 1 ⊗ ρ_B.M.log.
  have h_log : σ.M.log = ρ_A.M.log ⊗ₖ (1 : HermitianMat dB ℂ)
                          + (1 : HermitianMat dA ℂ) ⊗ₖ ρ_B.M.log := by
    show (ρ_A.M ⊗ₖ ρ_B.M).log = _
    exact HermitianMat.log_kron
  -- Step 4: pull the inner-product through.
  have h_inner_log : ⟪ρ.M, σ.M.log⟫ = -Sᵥₙ ρ_A - Sᵥₙ ρ_B := by
    rw [h_log, HermitianMat.inner_add_right,
        inner_kron_one_eq_inner_traceRight, inner_one_kron_eq_inner_traceLeft]
    show ⟪(ρ.M).traceRight, ρ_A.M.log⟫ + ⟪(ρ.M).traceLeft, ρ_B.M.log⟫ = _
    rw [show (ρ.M).traceRight = ρ_A.M from rfl,
        show (ρ.M).traceLeft = ρ_B.M from rfl]
    have h_SA : Sᵥₙ ρ_A = -⟪ρ_A.M, ρ_A.M.log⟫ := by
      rw [Sᵥₙ_eq_neg_trace_log, neg_inj, HermitianMat.inner_comm]
    have h_SB : Sᵥₙ ρ_B = -⟪ρ_B.M, ρ_B.M.log⟫ := by
      rw [Sᵥₙ_eq_neg_trace_log, neg_inj, HermitianMat.inner_comm]
    linarith
  -- Step 5: ⟪ρ.M, ρ.M.log⟫ = -Sᵥₙ ρ.
  have h_inner_self : ⟪ρ.M, ρ.M.log⟫ = -Sᵥₙ ρ := by
    rw [Sᵥₙ_eq_neg_trace_log, HermitianMat.inner_comm]; ring
  -- Step 6: assemble.
  rw [h_inner_log, h_inner_self] at h_real_RE
  -- h_real_RE : (qRelativeEnt ρ σ).toReal = -Sᵥₙ ρ - (-Sᵥₙ ρ_A - Sᵥₙ ρ_B)
  unfold qMutualInfo
  linarith

end AI4BB84
