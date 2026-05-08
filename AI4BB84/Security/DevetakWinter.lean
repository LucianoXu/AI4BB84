import AI4BB84.Adversary.Collective
import AI4BB84.Information.Holevo
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

This module defines the **rate value** `keyRate`. Its **lower-bound**
character (the security claim `0 ≤ keyRate`, equivalently
`χ(A; E) ≤ I(A; B)`) is what Devetak–Winter establishes; the proof
depends on `holevoChi_nonneg` (joint-entropy decomposition, in flight)
plus the data-processing inequality. Stated here as a future theorem;
not yet proved.

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

/-! ### Security claim (target, not yet proved)

The v1 security theorem we are building toward is:

```
theorem keyRate_nonneg
    (atk : CollectiveAttack E) (a : Basis) :
    0 ≤ keyRate atk a
```

Its proof is the Devetak–Winter inequality `χ(A; E) ≤ I(A; B)` applied
in the BB84 setting. The chain of dependencies (recorded in
`PROOF_LOG/holevo-chi.md` and `PROOF_LOG/proof-framework.md`):

1. Joint entropy decomposition `Sᵥₙ (cqState e) = Hₛ e.distr + ∑ᵢ pᵢ Sᵥₙ ρᵢ`.
2. From #1 + already-proved cq-state marginals → `holevoChi_nonneg`.
3. The Holevo bound + DPI on a measurement channel → bound `χ(A; E) ≤ I(A; B)`
   for any cq-source ensemble that has been processed by a quantum channel.
4. Apply to the BB84 collective-attack setting to get `keyRate_nonneg`.

Step 1 is the open piece. Step 3 needs the Holevo bound machinery. The
present module supplies the *statement infrastructure* — `keyRate` is a
real-valued definition that can be `#eval`-d/`#check`-d once concrete
attack channels are plugged in.
-/

end AI4BB84
