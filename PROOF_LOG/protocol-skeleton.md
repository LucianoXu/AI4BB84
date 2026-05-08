# BB84 protocol — skeleton modules

**Status:** 🟢 skeleton in place (Basis, Prepare, Sift); 🟡 Measure deferred
**Last updated:** 2026-05-08

## Context

Per `proof-framework.md`, we plan the v1 BB84 protocol model under `AI4BB84.Protocol.{Basis, Prepare, Measure, Sift}`. This entry records what the skeleton provides today, the design choices that were locked in, and what is deliberately deferred.

## Modules added

### `AI4BB84.Protocol.Basis`

```lean
inductive Basis : Type where
  | Z : Basis    -- computational basis
  | X : Basis    -- Hadamard basis
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Basis  -- explicit; deriving Fintype not enabled
def Basis.flip : Basis → Basis
```

Design choice: an inductive type rather than `Bool`. Self-documenting in the protocol code at the cost of a few extra instances (`Fintype` written by hand). `Basis.flip : Z ↔ X` is included because the Hadamard transform pairs the two bases and `flip_flip = id` is a one-line `rfl` proof.

### `AI4BB84.Protocol.Prepare`

```lean
def computationalState (b : Bool) : MState Qubit
def prepare (a : Basis) (b : Bool) : MState Qubit
@[simp] theorem prepare_Z, prepare_X
```

Alice's preparation is at the **density-matrix level** (`MState Qubit`), not the ket level. The X-basis preparation is `H ◃ computationalState b` using PhysLib's `MState.U_conj` notation; this exposes the unitary structure that downstream proofs will exploit. `prepare_Z` and `prepare_X` are `rfl`-marked simp lemmas so the protocol unfolds cleanly during reasoning.

Why density-matrix and not ket: every subsequent calculation (post-channel, ensembles, χ, qMutualInfo) is in the density-matrix world. Starting at the ket level would require going through `MState.pure` everywhere downstream.

### `AI4BB84.Protocol.Sift`

```lean
def keepRound (a b : Basis) : Prop := a = b
instance : Decidable (keepRound a b)
def keepRoundB (a b : Basis) : Bool
@[simp] theorem keepRoundB_refl, keepRoundB_eq_iff
```

Pure classical predicate: a round survives sifting iff Alice's basis = Bob's basis. No quantum state appears. The `Bool` form is for indexing/computation; the `Prop` form is for proofs.

### Umbrella

`AI4BB84.lean` now `import`s `Basic`, `Information.Holevo`, `Protocol.{Basis, Prepare, Sift}`. `lake build` exits 0 over the full library. `#print axioms` on the new theorems shows only the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`); no `sorry` anywhere in `AI4BB84/`.

## Deferred: `AI4BB84.Protocol.Measure`

Bob's measurement should be a `POVM Bool Qubit` (or `POVM (Fin 2) Qubit`) per basis. Constructing it requires writing the rank-1 projector matrices `|0⟩⟨0|, |1⟩⟨1|` as `HermitianMat Qubit ℂ`, supplying their `nonneg` proofs, and discharging the `normalized : ∑ x, mats x = 1` obligation by explicit matrix computation. This is bounded but non-trivial work (~30–60 lines per basis); it is not on the critical path for the next big step (which is the cq-state bridge in `Information/`), so it is queued for a focused session of its own.

## Next concrete tasks (not yet acted on)

1. **`AI4BB84/Information/CQState.lean`** — define `MEnsemble.cqState : MEnsemble d α → MState (α × d)`, the block-diagonal classical-quantum state `Σᵢ pᵢ |i⟩⟨i| ⊗ ρᵢ`. Prove `χ e = qMutualInfo (cqState e)` and derive `holevoChi_nonneg` as a one-liner from `Sᵥₙ_subadditivity`. **This is the key unblocking piece** for everything else in the χ chain.
2. `AI4BB84/Information/HolevoBound.lean` — `I_acc(X; ρ) ≤ χ(e)` via DPI on the cqState.
3. `AI4BB84/Protocol/Measure.lean` — Bob's basis-measurement POVMs. Defer until a Devetak-Winter step actually requires it (the protocol's joint state can be defined without it for some intermediate statements).
4. `AI4BB84/Adversary/Collective.lean` — collective-attack adversary model. Probably a `CPTPMap Qubit (Qubit × E)` capturing the per-pulse channel + Eve's ancilla.
5. `AI4BB84/Security/DevetakWinter.lean` — the headline rate theorem.

## References

- `AI4BB84/Protocol/Basis.lean`, `Prepare.lean`, `Sift.lean`
- `AI4BB84.lean` — umbrella
- PhysLib: `QuantumInfo/Finite/Qubit/Basic.lean` (`H`), `QuantumInfo/Finite/Unitary.lean` (`U_conj` / `◃` notation), `QuantumInfo/Finite/MState.lean` (`pure`), `QuantumInfo/Finite/Braket.lean` (`Ket.basis`)
- `PROOF_LOG/proof-framework.md`, `PROOF_LOG/holevo-chi.md`, `PROOF_LOG/physlib-coverage.md`
