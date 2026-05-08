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

end AI4BB84
