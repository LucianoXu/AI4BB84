import QuantumInfo.Finite.MState
import QuantumInfo.Finite.Ensemble

/-!
# Partial-trace identities for the Hilbert–Schmidt inner product

PhysLib supplies traces, partial traces, and the Hilbert–Schmidt inner
product `⟪·,·⟫` on `HermitianMat`, but does not directly state the
**partial-trace contraction lemmas**

  `⟪ρ, X ⊗ 1⟫ = ⟪ρ.traceRight, X⟫`,
  `⟪ρ, 1 ⊗ Y⟫ = ⟪ρ.traceLeft,  Y⟫`,

which contract the Hilbert–Schmidt inner against a `X ⊗ I` or `I ⊗ Y`
operator into a Hilbert–Schmidt inner with the appropriate marginal.

These are essential for the Holevo bound / `qMutualInfo_as_qRelativeEnt`
chain. Fortunately PhysLib's matrix-level `trace_mul_kron_one_right` and
`trace_mul_one_kron_right` (from `ForMathlib/Matrix.lean`) do most of the
work; we just lift to HermitianMat via `inner_eq_re_trace` and
`kronecker_mat`/`traceRight_mat`/`traceLeft_mat`.

Good upstream candidates for PhysLib's `ForMathlib/HermitianMat/Inner.lean`.
-/

open scoped InnerProductSpace RealInnerProductSpace HermitianMat
open MState

namespace AI4BB84

variable {α d : Type*} [Fintype α] [DecidableEq α] [Fintype d] [DecidableEq d]

/-- The partial-trace contraction in the second factor:
`⟪ρ, X ⊗ 1⟫ = ⟪ρ.traceRight, X⟫`. -/
theorem inner_kron_one_eq_inner_traceRight
    (ρ : HermitianMat (α × d) ℂ) (X : HermitianMat α ℂ) :
    ⟪ρ, X ⊗ₖ (1 : HermitianMat d ℂ)⟫ = ⟪ρ.traceRight, X⟫ := by
  rw [HermitianMat.inner_eq_re_trace, HermitianMat.inner_eq_re_trace]
  congr 1
  rw [HermitianMat.kronecker_mat, HermitianMat.traceRight_mat,
      show ((1 : HermitianMat d ℂ).mat) = (1 : Matrix d d ℂ) from rfl,
      Matrix.trace_mul_kron_one_right]

/-- The partial-trace contraction in the first factor:
`⟪ρ, 1 ⊗ Y⟫ = ⟪ρ.traceLeft, Y⟫`. -/
theorem inner_one_kron_eq_inner_traceLeft
    (ρ : HermitianMat (α × d) ℂ) (Y : HermitianMat d ℂ) :
    ⟪ρ, (1 : HermitianMat α ℂ) ⊗ₖ Y⟫ = ⟪ρ.traceLeft, Y⟫ := by
  rw [HermitianMat.inner_eq_re_trace, HermitianMat.inner_eq_re_trace]
  congr 1
  rw [HermitianMat.kronecker_mat, HermitianMat.traceLeft_mat,
      show ((1 : HermitianMat α ℂ).mat) = (1 : Matrix α α ℂ) from rfl,
      Matrix.trace_mul_one_kron_right]

end AI4BB84
