import AI4BB84.Adversary.Collective
import AI4BB84.Protocol.Measure

/-!
# Quantum Bit Error Rate (QBER)

For BB84 against a collective attack, the **Quantum Bit Error Rate** at a
fixed basis `a` is the probability — averaged over Alice's uniform bit —
that Bob's measurement of the post-attack qubit disagrees with Alice's bit.

The protocol uses QBER as its parameter-estimation observable: if it
exceeds a threshold (≈ 11%, the unique root of `2 h(δ) = 1` on `[0, 1/2]`),
the protocol aborts and produces no key. Restricting attention to attacks
with QBER below threshold is what makes BB84 secure; see
`PROOF_LOG/parameter-estimation.md` (subtask #1 — this file).

## Caveat: Z-basis only for now

The current `Protocol/Measure.lean` ships only `measureZ` — the X-basis POVM
(`measureX = H · measureZ · H†`) is recorded as deferred in
`PROOF_LOG/INDEX.md`. We use `measureZ` regardless of the basis argument `a`,
mirroring the existing convention in `bobClassicalState`/`bobEnsemble`. Once
`measureBasis : Basis → POVM (Fin 2) Qubit` lands, every consumer (including
this file) should switch in lockstep.
-/

namespace AI4BB84

namespace CollectiveAttack

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Probability that Bob's Z-basis measurement of the post-attack qubit
disagrees with Alice's bit `b`, at fixed basis `a`. The "wrong" outcome is
indexed by `bitIdx (!b)` — the unique element of `Fin 2` other than the
encoding of `b`. -/
noncomputable def bobMistakeProb (atk : CollectiveAttack E)
    (a : Basis) (b : Bool) : ℝ :=
  ((measureZ.measure ((atk.attackedState a b).traceRight))
    (bitIdx (!b)) : ℝ)

/-- The **Quantum Bit Error Rate** at fixed basis `a`: probability that
Bob's Z-measurement disagrees with Alice's bit, averaged over Alice's
uniform bit. -/
noncomputable def QBER (atk : CollectiveAttack E) (a : Basis) : ℝ :=
  (1 / 2 : ℝ) * ∑ b : Bool, atk.bobMistakeProb a b

/-! ### Elementary bounds -/

theorem bobMistakeProb_nonneg (atk : CollectiveAttack E)
    (a : Basis) (b : Bool) : 0 ≤ atk.bobMistakeProb a b :=
  Prob.zero_le_coe

theorem bobMistakeProb_le_one (atk : CollectiveAttack E)
    (a : Basis) (b : Bool) : atk.bobMistakeProb a b ≤ 1 :=
  Prob.coe_le_one

theorem QBER_nonneg (atk : CollectiveAttack E) (a : Basis) :
    0 ≤ atk.QBER a := by
  unfold QBER
  exact mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun b _ => atk.bobMistakeProb_nonneg a b)

theorem QBER_le_one (atk : CollectiveAttack E) (a : Basis) :
    atk.QBER a ≤ 1 := by
  unfold QBER
  have h_sum_le : ∑ b : Bool, atk.bobMistakeProb a b ≤ 2 := by
    calc ∑ b : Bool, atk.bobMistakeProb a b
        ≤ ∑ _b : Bool, (1 : ℝ) :=
          Finset.sum_le_sum fun b _ => atk.bobMistakeProb_le_one a b
      _ = 2 := by simp
  linarith

end CollectiveAttack

end AI4BB84
