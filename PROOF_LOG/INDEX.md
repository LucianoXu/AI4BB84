# PROOF_LOG Index

This file is the entry point to the project's durable proof memory. **Every session that touches modeling, proofs, or design choices should read this first.** See `CLAUDE.md` → "PROOF_LOG/" for the full convention.

Each entry below is one line: `[topic](file.md) — one-line hook`. Group by area; keep it scannable.

## Status legend

- 🟡 open question — under investigation
- 🟢 decided / proved
- 🔵 reference — survey or context, not a decision
- ⚪ superseded — kept for history

---

## Survey & background

- 🔵 [survey-of-prior-work](survey-of-prior-work.md) — landscape of QKD & quantum-protocol formal verification; identifies PhysLib as the substrate. 2026-05-08.
- 🔵 [physlib-coverage](physlib-coverage.md) — inventory of `QuantumInfo` namespace: what's there (Sᵥₙ, qMutualInfo, MEnsemble, POVM, Hadamard, …), what's missing (Holevo χ as a name, Holevo bound, DPI lemma). 2026-05-08.

## Framework / proof strategy

- 🟢 [proof-framework](proof-framework.md) — **v1 target locked: Devetak–Winter / collective attacks / asymptotic** (`r ≥ I(A;B) − χ(A;E)`). Upgrade path to coherent / composable / finite-key recorded. 2026-05-08.

## Modeling

- 🟢 [holevo-chi](holevo-chi.md) — `χ(e)` defined; `cqState : MEnsemble d α → MState (α × d)` defined; **both marginals fully proved** (`cqState_traceLeft = mix e`, `cqState_traceRight = MState.ofClassical e.distr`); marginal-entropy corollaries `Sᵥₙ_cqState_traceLeft/Right`. Next: joint-entropy decomposition → nonnegativity → Holevo bound. 2026-05-08.
- 🟢 [protocol-skeleton](protocol-skeleton.md) — `Basis` (Z/X inductive), `prepare : Basis → Bool → MState Qubit`, sifting predicate. Measure module deferred. 2026-05-08.
- 🟢 `CollectiveAttack` — `AI4BB84/Adversary/Collective.lean`: `structure CollectiveAttack (E : Type*) [...]` wrapping a per-pulse `CPTPMap Qubit (Qubit × E)`; `attackedState` composes Alice's preparation with Eve's channel. Sanity-baseline `trivial` attack deferred (needs PhysLib's `prep ∘ append` Stinespring pattern). 2026-05-08.

## Correctness proofs

*(no entries yet — sifting, key-agreement statements)*

## Security proofs

*(no entries yet — Eve information bounds, detection probability, composability)*

## Infrastructure / tooling

- 🟢 [physlib-dependency](physlib-dependency.md) — PhysLib pinned at commit `c8fa2271`; `import QuantumInfo.Finite.Entropy.VonNeumann` works; gotchas: `lake update` (no args, not `lake update Physlib`) and **PhysLib has no `QuantumInfo` Lean namespace** — definitions are at root or under `MState`/`Qubit`/etc. 2026-05-08.
