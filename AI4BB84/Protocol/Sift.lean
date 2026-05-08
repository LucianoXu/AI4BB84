import AI4BB84.Protocol.Basis

/-!
# BB84 sifting

After Alice transmits and Bob measures, both publicly announce their basis
choice for each round. **Sifting** keeps only those rounds where the two
choices agree; in the other rounds Bob's measurement is in the wrong basis
and the result is uncorrelated with Alice's bit.

This module is purely classical — no quantum state appears here. The
rounds-kept predicate is just basis equality. Per-round bit reconciliation
(after error-correction) is handled in a later module.
-/

namespace AI4BB84

/-- A round is kept after sifting iff Alice's and Bob's bases agree. -/
@[reducible] def keepRound (aAlice aBob : Basis) : Prop := aAlice = aBob

instance (a b : Basis) : Decidable (keepRound a b) := by
  unfold keepRound; infer_instance

/-- Boolean form of `keepRound`, useful in computations and in indexing
sifted strings. -/
def keepRoundB (aAlice aBob : Basis) : Bool := decide (aAlice = aBob)

@[simp] theorem keepRoundB_refl (a : Basis) : keepRoundB a a = true := by
  simp [keepRoundB]

@[simp] theorem keepRoundB_eq_iff {a b : Basis} :
    keepRoundB a b = true ↔ a = b := by
  simp [keepRoundB]

end AI4BB84
