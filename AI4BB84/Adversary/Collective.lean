import QuantumInfo.Finite.Qubit.Basic
import QuantumInfo.Finite.CPTPMap
import QuantumInfo.Finite.Ensemble
import AI4BB84.Protocol.Prepare

/-!
# Collective-attack adversary

A *collective* attack against BB84 fixes a single per-pulse quantum channel
that Eve applies independently to every qubit Alice transmits. The output
of that channel is bipartite: one part forwarded to Bob, the other kept by
Eve as her side-information. Eve's eventual key recovery may use a joint
measurement across her stored registers — but the per-pulse channel itself
is i.i.d.

This is the v1 adversary model for our Devetak–Winter security theorem
(see `PROOF_LOG/proof-framework.md`). Coherent attacks (a single global
operation across all pulses) are punted to a later milestone via a
de Finetti reduction.

We deliberately do **not** require the `Bob`-side output to live in
`Qubit` itself. In some formulations Eve's channel emits any quantum
register `B'`, and Bob's detector takes `B'` as input; this allows for
detector models with internal degrees of freedom. For the v1 statement we
fix `B' = Qubit` (Bob receives a qubit) since that is the standard
prepare-and-measure picture; later modules may relax this.

The `E` register holds Eve's quantum side-information; we do not yet
constrain its dimension. Concrete Devetak–Winter calculations will fix
`E` to something specific (e.g., the channel's environment dimension).
-/

namespace AI4BB84

/-- A collective-attack adversary parametrized by Eve's register type `E`.
Eve commits to a single CPTP map, which is then applied independently to
each transmitted qubit. -/
structure CollectiveAttack (E : Type*) [Fintype E] [DecidableEq E] where
  /-- The per-pulse channel from Alice's qubit to (Bob's qubit, Eve's register). -/
  channel : CPTPMap Qubit (Qubit × E)

namespace CollectiveAttack

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The joint state on `(Bob's qubit) × (Eve's register)` produced by Alice's
preparation `prepare a b` flowing through the attacker's channel. Alice's
classical inputs `(a, b)` (basis and bit) are not part of this state — they
remain classical, separate, and known to Alice. -/
noncomputable def attackedState (atk : CollectiveAttack E)
    (a : Basis) (b : Bool) : MState (Qubit × E) :=
  atk.channel (prepare a b)

/- A "trivial / no-eavesdropper" attack — Eve's channel forwards the qubit
unchanged to Bob and outputs a default constant state on her side — would
be a useful sanity-check baseline (under it, Eve's side-information should
be uncorrelated with Alice's bit). Constructing it requires PhysLib's
`prep ∘ append` Stinespring pattern (see `QuantumInfo/Finite/CPTPMap/CPTP.lean`)
and is left as a follow-up; not load-bearing for the security theorem. -/

/-! ### Eve's per-round side-information

For a fixed basis `a`, Alice's bit is uniformly random; Eve's reduced state
on her register `E` therefore comes from an ensemble indexed by `Bool`. We
package this for direct use with `holevoChi` — the asymptotic key rate
`r ≥ I(A;B) − χ(A;E)` evaluates `χ` on this very ensemble. -/

/-- Eve's reduced quantum state given Alice's basis `a` and bit `b`. -/
noncomputable def eveStateGivenBit (atk : CollectiveAttack E)
    (a : Basis) (b : Bool) : MState E :=
  (atk.attackedState a b).traceLeft

/-- Eve's per-round ensemble (uniform over Alice's bit), at fixed basis `a`. -/
noncomputable def eveEnsemble (atk : CollectiveAttack E) (a : Basis) :
    MEnsemble E Bool where
  var := atk.eveStateGivenBit a
  distr := ProbDistribution.uniform

end CollectiveAttack

end AI4BB84
