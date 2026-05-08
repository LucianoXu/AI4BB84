import QuantumInfo.Finite.Ensemble
import QuantumInfo.Finite.Entanglement
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
  change ((cqState e).M.traceLeft).mat = (mix e).m
  rw [HermitianMat.traceLeft_mat]
  change (cqState e).m.traceLeft = (mix e).m
  unfold cqState
  rw [mix_of, mix_of]
  -- LHS: (∑ i, (e.distr i : ℝ) • (pure (basis i) ⊗ᴹ e.states i).m).traceLeft
  -- RHS: ∑ i, (e.distr i : ℝ) • (e.states i).m
  rw [Matrix.traceLeft_finset_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.traceLeft_smul]
  congr 1
  -- Reduce to: ((pure (basis i)) ⊗ᴹ (e.states i)).m.traceLeft = (e.states i).m
  -- `.m` of a prod is the kronecker product; traceLeft of a kron is
  -- (trace of left factor) • (right factor); pure states have trace 1.
  change ((MState.pure (Ket.basis i)).m ⊗ₖ (e.states i).m).traceLeft = (e.states i).m
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
  change ((cqState e).M.traceRight).mat = _
  rw [HermitianMat.traceRight_mat]
  change (cqState e).m.traceRight = _
  unfold cqState
  rw [mix_of, Matrix.traceRight_finset_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.traceRight_smul]
  congr 1
  change ((MState.pure (Ket.basis i)).m ⊗ₖ (e.states i).m).traceRight =
      (MState.pure (Ket.basis i)).m
  rw [Matrix.traceRight_kron, MState.tr', one_smul]

/-- Entry-wise: a basis projector `|k⟩⟨k|` has `(i, j)` entry `1` exactly
when `k = i = j`, else `0`. -/
private theorem MState.pure_basis_apply (k i j : α) :
    (MState.pure (Ket.basis k : Ket α)).m i j =
      if k = i ∧ k = j then 1 else 0 := by
  rw [MState.pure_apply]
  simp only [Ket.basis, Ket.coe_fun_eq, RCLike.star_def]
  rcases eq_or_ne k i with rfl | hi
  · rcases eq_or_ne k j with rfl | hj
    · simp
    · simp [hj]
  · simp [hi]

/-- The X-marginal of the cq-state is the classical embedding of `e.distr`. -/
theorem cqState_traceRight (e : MEnsemble d α) :
    (cqState e).traceRight = MState.ofClassical e.distr := by
  apply MState.m_inj
  rw [cqState_traceRight_m]
  change _ = (MState.ofClassical e.distr).M.mat
  rw [MState.coe_ofClassical, HermitianMat.diagonal_mat]
  ext i j
  -- LHS: (∑ k, (e.distr k : ℝ) • (pure (basis k)).m) i j
  -- RHS: (Matrix.diagonal (e.distr ·) : Matrix α α ℂ) i j
  -- Push indexing through the sum and the smul; apply basis-projector formula.
  simp only [Matrix.sum_apply, Matrix.smul_apply,
             MState.pure_basis_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
             Matrix.diagonal_apply]
  -- Goal: ∑ k, (if k = i ∧ k = j then ↑(e.distr k) else 0) = if i = j then ↑(e.distr i) else 0
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Finset.sum_eq_single i]
    · simp
    · intros k _ hk
      simp [hk]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [if_neg hij, Finset.sum_eq_zero]
    intros k _
    by_cases hki : k = i
    · subst hki; simp [hij]
    · simp [hki]

/-! ### Marginal entropies of the cq-state -/

/-- The von Neumann entropy of the B-marginal equals that of the mixture. -/
@[simp] theorem Sᵥₙ_cqState_traceLeft (e : MEnsemble d α) :
    Sᵥₙ (cqState e).traceLeft = Sᵥₙ (mix e) := by
  rw [cqState_traceLeft]

/-- The von Neumann entropy of the X-marginal equals the Shannon entropy of the
ensemble's index distribution. -/
@[simp] theorem Sᵥₙ_cqState_traceRight (e : MEnsemble d α) :
    Sᵥₙ (cqState e).traceRight = Hₛ e.distr := by
  rw [cqState_traceRight, Sᵥₙ_ofClassical]

end AI4BB84
