import QuantumInfo.Finite.Ensemble
import QuantumInfo.Finite.Entropy.VonNeumann

/-!
# Holevo information `χ` of a mixed-state ensemble

The Holevo quantity `χ(e)` of an ensemble `e = {(p_i, ρ_i)}` is defined as the
gap between the entropy of the average state and the average of the entropies:

  `χ(e) := Sᵥₙ(∑ᵢ pᵢ ρᵢ) − ∑ᵢ pᵢ Sᵥₙ(ρᵢ)`

It is the cornerstone of the Devetak–Winter security argument we are building
toward (`PROOF_LOG/proof-framework.md`): the quantity that bounds Eve's
accessible information about a classical register correlated with her quantum
side-information.

PhysLib provides the building blocks:
* `MState d` — finite-dimensional density operators
* `MEnsemble d α` — `α`-indexed probabilistic mixture of `MState d`
* `Ensemble.mix : MEnsemble d α → MState d` — the convex combination
* `Sᵥₙ : MState d → ℝ` — von Neumann entropy

PhysLib does **not** yet provide a named `χ`/Holevo definition (only mentioned
in `Capacity.lean` docstrings); this module supplies it.

We avoid `Ensemble.average` and write the average explicitly as a `Finset.sum`,
because `Ensemble.average` is parametrized by a `Mixable` instance whose
universe constraints currently force the dimension type into `Type 0` for our
use; the explicit sum bypasses the issue.

## Properties recorded here

* `holevoChi_trivial`: a trivial (single-state) ensemble has `χ = 0`.

## Properties deferred (for later modules)

* `0 ≤ χ(e)` (Holevo nonnegativity / sub-additivity). Standard proof: build
  the classical-quantum state `ρ_XB := ∑ᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ` and observe
  `χ(e) = qMutualInfo ρ_XB`, which is `≥ 0` by `Sᵥₙ_subadditivity`. Requires a
  `MEnsemble.cqState : MEnsemble d α → MState (α × d)` bridge that PhysLib does
  not yet ship — see `PROOF_LOG/holevo-chi.md`.
* The Holevo bound `I_acc(X; ρ) ≤ χ(e)`. Same cq-state bridge plus the DPI
  available as `sandwichedRenyiEntropy_DPI_eq_one`.

See also `material/SURVEY.md` (Lewis et al. § Holevo bound) and
`PROOF_LOG/proof-framework.md` § "Intermediate lemmas" entries (1) and (2).
-/

open Ensemble

namespace AI4BB84

variable {d α : Type*} [Fintype d] [DecidableEq d] [Fintype α]

/-- Holevo information `χ` of a mixed-state ensemble.

Equals `Sᵥₙ` of the mixture minus the probability-weighted average of `Sᵥₙ`
over the components. By `Sᵥₙ_subadditivity` on the cq-state, this quantity
is always nonnegative; the proof of nonnegativity is deferred (see file
docstring). -/
noncomputable def holevoChi (e : MEnsemble d α) : ℝ :=
  Sᵥₙ (mix e) - ∑ i : α, (e.distr i : ℝ) * Sᵥₙ (e.states i)

@[inherit_doc]
scoped notation "χ" => holevoChi

/-- A trivial (constant) ensemble — the same state with probability 1 on a
single index — has zero Holevo information.

Computes both ends:
* `Sᵥₙ (mix (trivial_mEnsemble ρ i)) = Sᵥₙ ρ` by `trivial_mEnsemble_mix`.
* The weighted-sum part collapses to `Sᵥₙ ρ` because all states are `ρ`
  and the distribution sums to 1.
-/
theorem holevoChi_trivial (ρ : MState d) (i : α) :
    holevoChi (trivial_mEnsemble ρ i) = 0 := by
  unfold holevoChi
  rw [trivial_mEnsemble_mix ρ i]
  -- All states in the trivial ensemble are ρ, so factor `Sᵥₙ ρ` out of the sum
  -- and use that the distribution is normalized.
  have h_states : ∀ j, (trivial_mEnsemble ρ i).states j = ρ := by
    intro j; rfl
  simp_rw [h_states]
  rw [← Finset.sum_mul, ProbDistribution.normalized (trivial_mEnsemble ρ i).distr]
  ring

end AI4BB84
