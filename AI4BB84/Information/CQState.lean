import QuantumInfo.Finite.Ensemble
import AI4BB84.Information.Holevo

/-!
# Classical–quantum state of an ensemble

For a mixed-state ensemble `e = {(p_i, ρ_i)}` indexed by a finite type `α`,
the **classical-quantum (cq) state** is

  `ρ_XB(e) := ∑ᵢ pᵢ (|i⟩⟨i|_X ⊗ ρᵢ_B) ∈ MState (α × d)`.

The X-register is classical (a diagonal density operator); the B-register
is the quantum side held by the mixture's components. This object is the
bridge that lets us identify Holevo `χ` with `qMutualInfo`:

  `qMutualInfo (cqState e) = χ(e)`,

which in turn gives nonnegativity of `χ` for free via PhysLib's
`Sᵥₙ_subadditivity` (`SSA.lean:1203`).

The construction uses `MState.prod` to tensor each `|i⟩⟨i|` with `ρᵢ`,
and `Ensemble.mix` to take the convex combination. The latter is already
in PhysLib; the former is just `MState.prod (MState.pure (Ket.basis i)) ρᵢ`.

This module supplies the **definition** of `cqState`. The identity
`qMutualInfo_cqState_eq_holevoChi` will be proved in a follow-up file once
the marginals (`traceLeft`, `traceRight`) and entropy of the cq-state have
been computed; that work depends on traceLeft / traceRight push-through
lemmas for `Ensemble.mix` that are not yet shaped as we need them.

See also `PROOF_LOG/holevo-chi.md` and `PROOF_LOG/proof-framework.md`
§ "Intermediate lemmas" #1.
-/

open MState
open Ensemble
open scoped Kronecker

namespace AI4BB84

variable {d α : Type*} [Fintype d] [DecidableEq d] [Fintype α] [DecidableEq α]

/-- The classical-quantum state of a mixed-state ensemble.

For each index `i`, this places the rank-1 classical projector `|i⟩⟨i|` on
the `X` register and `ρᵢ` on the `B` register, then averages over the
ensemble distribution. -/
noncomputable def cqState (e : MEnsemble d α) : MState (α × d) :=
  Ensemble.mix
    (⟨fun i => (MState.pure (Ket.basis i)).prod (e.states i), e.distr⟩
      : MEnsemble (α × d) α)

/-! ### Helpers missing from PhysLib (TODOs to upstream)

PhysLib does not yet ship `Matrix.traceLeft (∑ x, _) = ∑ x, Matrix.traceLeft _`
(see the explicit TODO in `QuantumInfo/Finite/POVM.lean:139`) nor a
matrix-level `Matrix.traceLeft (A ⊗ₖ B) = A.trace • B`. Both are stated
and proved here locally. -/

private theorem Matrix.traceLeft_finset_sum
    {ι m n α : Type*} [AddCommGroup α] [Fintype m] [DecidableEq n] [DecidableEq ι]
    (s : Finset ι) (f : ι → Matrix (m × n) (m × n) α) :
    (∑ i ∈ s, f i).traceLeft = ∑ i ∈ s, (f i).traceLeft := by
  induction s using Finset.induction_on with
  | empty => ext i j; simp [Matrix.traceLeft]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.traceLeft_add, ih]

private theorem Matrix.traceLeft_kron
    {m n R : Type*} [CommSemiring R] [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m m R) (B : Matrix n n R) :
    (A ⊗ₖ B).traceLeft = A.trace • B := by
  ext i j
  simp only [Matrix.traceLeft, Matrix.kroneckerMap_apply, Matrix.trace,
             Matrix.diag, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [Finset.sum_mul]

/-! ### Marginals of the cq-state -/

/-- The B-marginal of the cq-state is the mixture of the component states.

Pointwise matrix-level statement. The `MState` form is `cqState_traceLeft`. -/
theorem cqState_traceLeft_m (e : MEnsemble d α) :
    (cqState e).traceLeft.m = (mix e).m := by
  show ((cqState e).M.traceLeft).mat = (mix e).m
  rw [HermitianMat.traceLeft_mat]
  show (cqState e).m.traceLeft = (mix e).m
  unfold cqState
  rw [mix_of, mix_of]
  -- LHS: (∑ i, (e.distr i : ℝ) • (pure (basis i) ⊗ᴹ e.states i).m).traceLeft
  -- RHS: ∑ i, (e.distr i : ℝ) • (e.states i).m
  rw [Matrix.traceLeft_finset_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.traceLeft_smul]
  congr 1
  -- Reduce to: ((pure (basis i)) ⊗ᴹ (e.states i)).m.traceLeft = (e.states i).m
  show ((MState.pure (Ket.basis i)).prod (e.states i)).m.traceLeft = (e.states i).m
  -- `.m` of a prod is the kronecker product; traceLeft of a kron is
  -- (trace of left factor) • (right factor); pure states have trace 1.
  show ((MState.pure (Ket.basis i)).m ⊗ₖ (e.states i).m).traceLeft = (e.states i).m
  rw [Matrix.traceLeft_kron, MState.tr', one_smul]

/-- The B-marginal of the cq-state is the mixture of the component states. -/
theorem cqState_traceLeft (e : MEnsemble d α) :
    (cqState e).traceLeft = mix e :=
  MState.m_inj (cqState_traceLeft_m e)

/-! ### traceRight -/

private theorem Matrix.traceRight_finset_sum
    {ι m n α : Type*} [AddCommGroup α] [Fintype n] [DecidableEq m] [DecidableEq ι]
    (s : Finset ι) (f : ι → Matrix (m × n) (m × n) α) :
    (∑ i ∈ s, f i).traceRight = ∑ i ∈ s, (f i).traceRight := by
  induction s using Finset.induction_on with
  | empty => ext i j; simp [Matrix.traceRight]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.traceRight_add, ih]

private theorem Matrix.traceRight_kron
    {m n R : Type*} [CommSemiring R] [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m m R) (B : Matrix n n R) :
    (A ⊗ₖ B).traceRight = B.trace • A := by
  ext i j
  simp only [Matrix.traceRight, Matrix.kroneckerMap_apply, Matrix.trace,
             Matrix.diag, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [← Finset.mul_sum, mul_comm]

/-- The X-marginal of the cq-state, pointwise as a sum of basis projectors. -/
theorem cqState_traceRight_m (e : MEnsemble d α) :
    (cqState e).traceRight.m =
      ∑ i : α, (e.distr i : ℝ) • (MState.pure (Ket.basis i)).m := by
  show ((cqState e).M.traceRight).mat = _
  rw [HermitianMat.traceRight_mat]
  show (cqState e).m.traceRight = _
  unfold cqState
  rw [mix_of, Matrix.traceRight_finset_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.traceRight_smul]
  congr 1
  show ((MState.pure (Ket.basis i)).m ⊗ₖ (e.states i).m).traceRight =
      (MState.pure (Ket.basis i)).m
  rw [Matrix.traceRight_kron, MState.tr', one_smul]

/- The full identification `(cqState e).traceRight = MState.ofClassical e.distr`
follows by recognizing `∑ᵢ pᵢ • |i⟩⟨i|` as the diagonal matrix `diag(p)` —
an entry-wise argument using `Ket.basis` unfolding plus `Finset.sum_ite_eq`.
Recorded as a TODO; the `_m` form above is what downstream proofs need
in any case. -/

end AI4BB84
