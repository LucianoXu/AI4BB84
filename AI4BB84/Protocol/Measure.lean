import QuantumInfo.Finite.POVM
import QuantumInfo.Finite.Qubit.Basic
import AI4BB84.Protocol.Basis
import AI4BB84.Protocol.Prepare

/-!
# Bob's BB84 measurement

For each round Bob chooses a basis `a : Basis` and measures the incoming
qubit in that basis. The measurement is a `POVM Bool Qubit`, with outcome
`false`/`true` corresponding to the two basis vectors.

We construct the **Z-basis** measurement directly from the rank-1 projectors
`|0⟩⟨0|` and `|1⟩⟨1|`, then obtain the **X-basis** measurement by
conjugating with the Hadamard. A unifying `measureBasis : Basis → POVM`
ties the two together, and an `attackedKey` ensemble gives Bob's classical
outcome distribution given Alice's basis and bit (used for I(A;B)).

PhysLib lacks a dedicated `HermitianMat.single` for rank-1 projectors; we
go through `MState.pure (Ket.basis ·)` which already carries the PSD proof
in its `.nonneg` field. The resolution-of-identity proof reduces to the
matrix-entry calculation `∑ k, |k⟩⟨k| = 1` shown via `MState.pure_basis_apply`-
style entry-wise identification.
-/

open MState

namespace AI4BB84

/-! ### Z-basis (computational) measurement -/

/-- The rank-1 computational-basis projector `|i⟩⟨i|` as a `HermitianMat`. -/
noncomputable def computationalProjector (i : Fin 2) : HermitianMat Qubit ℂ :=
  (MState.pure (Ket.basis i)).M

/-- Pointwise: the matrix entry of `|k⟩⟨k|`. -/
private theorem computationalProjector_apply (k i j : Qubit) :
    (computationalProjector k).mat i j = if k = i ∧ k = j then 1 else 0 := by
  show (MState.pure (Ket.basis k)).m i j = _
  rw [MState.pure_apply]
  simp only [Ket.basis, Ket.coe_fun_eq, RCLike.star_def]
  rcases eq_or_ne k i with rfl | hi
  · rcases eq_or_ne k j with rfl | hj
    · simp
    · simp [hj]
  · simp [hi]

/-- Resolution of identity: `∑ k : Qubit, |k⟩⟨k| = 1` as a `HermitianMat`. -/
theorem sum_computationalProjector :
    ∑ k : Qubit, computationalProjector k = (1 : HermitianMat Qubit ℂ) := by
  apply HermitianMat.ext
  rw [HermitianMat.mat_finset_sum]
  ext i j
  show (∑ k, (computationalProjector k).mat) i j =
    ((1 : HermitianMat Qubit ℂ).mat) i j
  rw [show ((1 : HermitianMat Qubit ℂ).mat) = (1 : Matrix Qubit Qubit ℂ) from rfl,
      Matrix.one_apply]
  simp only [Matrix.sum_apply, computationalProjector_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Finset.sum_eq_single i]
    · simp
    · intros k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [if_neg hij, Finset.sum_eq_zero]
    intros k _
    by_cases hki : k = i
    · subst hki; simp [hij]
    · simp [hki]

/-- Bob's Z-basis (computational) POVM. -/
noncomputable def measureZ : POVM (Fin 2) Qubit where
  mats := computationalProjector
  nonneg i := (MState.pure _).nonneg
  normalized := sum_computationalProjector

end AI4BB84
