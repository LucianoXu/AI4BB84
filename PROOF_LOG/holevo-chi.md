# Holevo information `χ` definition

**Status:** 🟢 defined (`AI4BB84.holevoChi`) with one elementary fact proved; nonnegativity and the Holevo bound deferred
**Last updated:** 2026-05-08

## Context

Per `PROOF_LOG/proof-framework.md`, the v1 security theorem is `r ≥ I(A;B) − χ(A;E)`. The Holevo information `χ` is therefore a first-class quantity we need. PhysLib's `QuantumInfo` namespace provides every primitive (Sᵥₙ, MEnsemble, mix, MState, …) but does not name `χ` itself.

## What was added

`AI4BB84/Information/Holevo.lean` (new module, namespace `AI4BB84`):

```lean
noncomputable def holevoChi (e : MEnsemble d α) : ℝ :=
  Sᵥₙ (Ensemble.mix e) - ∑ i : α, (e.distr i : ℝ) * Sᵥₙ (e.states i)

scoped notation "χ" => holevoChi

theorem holevoChi_trivial (ρ : MState d) (i : α) :
    holevoChi (trivial_mEnsemble ρ i) = 0
```

`#print axioms AI4BB84.holevoChi_trivial` reports only `propext`, `Classical.choice`, `Quot.sound` — no `sorryAx`.

## Why a direct sum, not `Ensemble.average`

PhysLib offers `Ensemble.average : (MState d → T) → MEnsemble d α → T` parametrized by a `Mixable U T` instance. When `T = ℝ` and `e : MEnsemble.{u₁, u₂} d α` (with `d` and `α` polymorphic in their universes), Lean's elaborator is unable to unify the universes — it forces `d : Type 0`, breaking calls from any module that takes `d` polymorphically. The error reported was:

```
Application type mismatch: ... e has type MEnsemble.{u_1, u_2} d α
but is expected to have type MEnsemble.{0, max u_1 u_2} ?m.22 ?m.12
```

We sidestep by writing the average as `∑ i : α, (e.distr i : ℝ) * Sᵥₙ (e.states i)` directly. This is also more transparent and does not require a `Mixable ℝ ℝ` lookup at every use-site. If we ever want to upstream `χ` to PhysLib, the cleaner thing would be to fix `average` so that the `T` universe is fully polymorphic, then redefine `χ` in terms of `average`.

## What is still deferred

### χ is nonnegative — `0 ≤ χ(e)`

The textbook proof goes through the **classical-quantum state**

  `ρ_XB(e) := ∑ᵢ pᵢ |i⟩⟨i|_X ⊗ ρᵢ ∈ MState (α × d)`

and the identity `χ(e) = qMutualInfo (ρ_XB(e))`. Then `qMutualInfo ≥ 0` follows from `Sᵥₙ_subadditivity` (already proved in PhysLib `SSA.lean:1203`).

**Blocker for now:** PhysLib does not provide a `MEnsemble.cqState : MEnsemble d α → MState (α × d)` constructor. Building it requires writing the explicit block-diagonal density operator using PhysLib's `kroneckerMap`/`MState.prod` API and discharging the PSD + trace-1 obligations. Roughly 30–80 lines of careful tensor-product code. Plus `χ_eq_qMutualInfo_cqState` to identify the two quantities.

This is bounded, well-understood work — but it is its own task. Recorded as a separate to-do rather than blocking other progress; meanwhile `χ` is fully usable as a *defined quantity* in subsequent modules.

### The Holevo bound — `I_acc(X; ρ) ≤ χ(e)`

For any POVM measurement `Λ` on the quantum register `B` of the cq-state, the resulting classical-classical mutual information is at most `χ(e)`. Proof: apply DPI (`sandwichedRenyiEntropy_DPI_eq_one`, available) with the classical-readout channel `id_X ⊗ Λ`, using `qMutualInfo_as_qRelativeEnt` to put `qMutualInfo` in DPI-applicable form. Depends on the cq-state bridge above.

## Status of the cq-state bridge

`AI4BB84/Information/CQState.lean` (added 2026-05-08) supplies:

```lean
noncomputable def cqState (e : MEnsemble d α) : MState (α × d)

theorem cqState_traceLeft (e : MEnsemble d α) :
    (cqState e).traceLeft = mix e

theorem cqState_traceRight_m (e : MEnsemble d α) :
    (cqState e).traceRight.m = ∑ i : α, (e.distr i : ℝ) • (MState.pure (Ket.basis i)).m
```

**Both marginals are proved.** `cqState_traceLeft = mix e` is the full
MState-level statement; `cqState_traceRight_m` is the matrix-level
sum-of-projectors form. Both use only `propext`, `Classical.choice`,
`Quot.sound` (no `sorryAx`).

Two private helpers were added (PhysLib has these as TODOs):
- `Matrix.traceLeft_finset_sum` and `Matrix.traceRight_finset_sum`
- `Matrix.traceLeft_kron : (A ⊗ₖ B).traceLeft = A.trace • B`
- `Matrix.traceRight_kron : (A ⊗ₖ B).traceRight = B.trace • A`

These are good upstream candidates for PhysLib's `ForMathlib/Matrix.lean`.

The full `cqState_traceRight = MState.ofClassical e.distr` (identifying the
sum of basis projectors with the diagonal matrix) is the remaining algebraic
step — a `Finset.sum_ite_eq` argument over `Ket.basis` entries. Not yet
proved; not blocking the entropy decomposition (which can use the `_m` form).

## Next concrete tasks (recorded for the next session)

1. **Finish the X-marginal**: `cqState_traceRight = MState.ofClassical e.distr` — entry-wise identification of `∑ᵢ pᵢ • |i⟩⟨i|` with `diagonal e.distr`. Should be a focused `ext + Finset.sum_ite_eq` lemma. Optional for the next step: the `_m` form is sufficient for entropy reasoning.

2. **Joint entropy decomposition**: `Sᵥₙ (cqState e) = Hₛ e.distr + Σᵢ pᵢ Sᵥₙ (ρᵢ)` (standard cq-state identity using block-diagonality). PhysLib has `Sᵥₙ_of_partial_eq` and the spectral-decomposition machinery; this proof is the substantial next entropy step.

3. Combining #1/#2 with the proved marginals: `qMutualInfo (cqState e) = χ e` (the bridge), and immediately `holevoChi_nonneg : 0 ≤ χ e` via `Sᵥₙ_subadditivity` (PhysLib `SSA.lean:1203`).

4. The Holevo bound `I_acc(X; ρ) ≤ χ(e)` via DPI on `cqState` plus a measurement channel.

None of these are required to start on the BB84 protocol model itself, which proceeds independently.

## References

- `AI4BB84/Information/Holevo.lean`
- `PROOF_LOG/proof-framework.md` § "Intermediate lemmas" #1, #2
- `PROOF_LOG/physlib-coverage.md` — entropies, ensembles, DPI
- PhysLib: `QuantumInfo/Finite/Ensemble.lean` (mix, average, trivial_mEnsemble), `QuantumInfo/Finite/Entropy/SSA.lean:1203` (`Sᵥₙ_subadditivity`), `QuantumInfo/Finite/Entropy/DPI.lean:1385` (`sandwichedRenyiEntropy_DPI_eq_one`), `QuantumInfo/Finite/Entropy/Relative.lean:2137` (`qMutualInfo_as_qRelativeEnt`)
