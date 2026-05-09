import AI4BB84.Adversary.Collective
import AI4BB84.Information.Holevo
import AI4BB84.Information.HolevoNonneg
import AI4BB84.Protocol.Measure

/-!
# Devetak–Winter asymptotic key rate (v1)

For BB84 against a collective-attack adversary, fixed basis `a`, the v1
asymptotic secret-key rate per sifted round is

  `r ≥ I(A; B) − χ(A; E)`

where `A` is Alice's classical bit, `B` is Bob's classical measurement
outcome, and `E` is Eve's quantum register. Both quantities are
expressible as `holevoChi` of an appropriate ensemble:

  * `I(A; B) = holevoChi (bobEnsemble atk a)` — Bob's outcome is classical,
    so the χ of the (Alice → Bob's classicalized state) ensemble reduces
    to the classical Shannon mutual information.
  * `χ(A; E) = holevoChi (atk.eveEnsemble a)` — Eve holds quantum
    side-information.

This module defines the **rate value** `keyRate`. Whether `0 ≤ keyRate`
holds for a given `(atk, a)` is **not** a universal information-theoretic
inequality and is **not** what `holevoBound` (already proved) establishes.
A measure-Z-resend-`|+⟩` collective attack gives `χ(A; E) = 1` and
`I(A; B) = 0`, hence `keyRate = -1` for that attack. BB84 rejects such
attacks via *parameter estimation* (high QBER ⇒ abort), a step our
current `CollectiveAttack` model does not represent.

The Devetak–Winter theorem is *operational*: a one-way LOCC key-distillation
protocol achieving rate `I(A; B) - χ(A; E)` exists when that quantity is
positive, with security against collective attacks verified by the
parameter-estimation step. Mechanizing this is the Bar-2 sprint — see
`PROOF_LOG/parameter-estimation.md`.

See `PROOF_LOG/proof-framework.md` for context.
-/

namespace AI4BB84

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Bob's classical measurement outcome (as a quantum state on `Fin 2`,
diagonal in the Z basis) given Alice's basis `a` and bit `b`. -/
noncomputable def bobClassicalState (atk : CollectiveAttack E)
    (a : Basis) (b : Bool) : MState (Fin 2) :=
  MState.ofClassical (measureZ.measure (atk.attackedState a b).traceRight)

/-- The ensemble of Bob's classicalized outcome states, indexed by Alice's
uniformly-random bit, at fixed basis `a`. -/
noncomputable def bobEnsemble (atk : CollectiveAttack E) (a : Basis) :
    MEnsemble (Fin 2) Bool where
  var := bobClassicalState atk a
  distr := ProbDistribution.uniform

/-- The Alice–Bob mutual information at fixed basis. Since Bob's register
is classical, this `holevoChi` is the classical Shannon mutual
information `I(A; B)`. -/
noncomputable def aliceBobMutualInfo (atk : CollectiveAttack E)
    (a : Basis) : ℝ :=
  holevoChi (bobEnsemble atk a)

/-- The Holevo information that Eve has about Alice's bit at fixed basis. -/
noncomputable def eveHolevoInfo (atk : CollectiveAttack E)
    (a : Basis) : ℝ :=
  holevoChi (atk.eveEnsemble a)

/-- The Devetak–Winter asymptotic key rate per sifted round, at fixed basis.

  `r(a) := I(A; B; a) − χ(A; E; a)`

By the Devetak–Winter theorem this lower-bounds the achievable secret-key
rate against any collective attack with that basis. -/
noncomputable def keyRate (atk : CollectiveAttack E) (a : Basis) : ℝ :=
  aliceBobMutualInfo atk a - eveHolevoInfo atk a

/-! ### Information-theoretic positivity facts (immediate from `holevoChi_nonneg`) -/

/-- Helper: the uniform distribution on `Bool` is positive at every index. -/
private theorem uniform_bool_pos (b : Bool) :
    (0 : ℝ) < ((ProbDistribution.uniform : ProbDistribution Bool) b : ℝ) := by
  show (0 : ℝ) < (ProbDistribution.uniform b).val
  simp only [ProbDistribution.uniform]
  norm_num

/-- The Alice-Bob mutual information is nonnegative. -/
theorem aliceBobMutualInfo_nonneg (atk : CollectiveAttack E) (a : Basis) :
    0 ≤ aliceBobMutualInfo atk a :=
  holevoChi_nonneg (bobEnsemble atk a) uniform_bool_pos

/-- Eve's Holevo information about Alice's bit is nonnegative. -/
theorem eveHolevoInfo_nonneg (atk : CollectiveAttack E) (a : Basis) :
    0 ≤ eveHolevoInfo atk a :=
  holevoChi_nonneg (atk.eveEnsemble a) uniform_bool_pos

/-! ### Conditional positivity (placeholder — NOT a security theorem)

The universal statement `∀ atk a, 0 ≤ keyRate atk a` is **false**: a
measure-Z-resend-`|+⟩` collective attack gives `χ(A; E) = 1` and
`I(A; B) = 0`, hence `keyRate = -1`. BB84 rejects such attacks at
parameter estimation, but our current model does not encode that step.
The path from `0 ≤ keyRate` to a real security claim is the Bar-2
sprint described in `PROOF_LOG/parameter-estimation.md`:

1. Add a `QBER : CollectiveAttack E → Basis → ℝ` observable.
2. Restrict to symmetric / parameter-estimation-passing attacks.
3. Prove `χ(A; E) ≤ h(QBER)` for those (binary-entropy bound).
4. Prove `I(A; B) = 1 - h(QBER)` (classical channel capacity).
5. Conclude `keyRate ≥ 1 - 2 h(QBER)`, positive when QBER < ~11%.

The `linarith`-trivial conditional below promotes a (hypothetically
obtained) entropic ordering to the typed predicate `0 ≤ keyRate atk a`
for downstream code; it is **not** itself a security claim. -/

theorem keyRate_nonneg_of_eve_le_bob
    (atk : CollectiveAttack E) (a : Basis)
    (h : eveHolevoInfo atk a ≤ aliceBobMutualInfo atk a) :
    0 ≤ keyRate atk a := by
  unfold keyRate
  linarith

end AI4BB84
