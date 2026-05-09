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

- 🟢 [holevo-chi](holevo-chi.md) — `χ(e)` defined; `cqState` + both marginals + marginal entropies proved; **`holevoChi_nonneg` PROVED** via Klein's inequality (assuming `∀ i, 0 < e.distr i`). All chained through `propext`/`Classical.choice`/`Quot.sound` only. Holevo bound (for `keyRate_nonneg`) still pending. 2026-05-08.
- 🟢 [protocol-skeleton](protocol-skeleton.md) — `Basis` (Z/X inductive), `prepare : Basis → Bool → MState Qubit`, sifting predicate. Measure module deferred. 2026-05-08.
- 🟢 `CollectiveAttack` — `AI4BB84/Adversary/Collective.lean`: `structure CollectiveAttack (E : Type*) [...]` wrapping a per-pulse `CPTPMap Qubit (Qubit × E)`; `attackedState`, `eveStateGivenBit`, `eveEnsemble : MEnsemble E Bool` (uniform over Alice's bit). Sanity-baseline `trivial` attack deferred. 2026-05-08.
- 🟢 `Measure` — `AI4BB84/Protocol/Measure.lean`: `computationalProjector i = |i⟩⟨i|` (HermitianMat), `sum_computationalProjector : ∑ k, |k⟩⟨k| = 1` proved by entry-wise calculation, `measureZ : POVM (Fin 2) Qubit`. X-basis POVM (via Hadamard conjugation) deferred. 2026-05-08.

## Security

- 🟢 [security/devetak-winter](../AI4BB84/Security/DevetakWinter.lean) (no PROOF_LOG entry yet) — `bobClassicalState`, `bobEnsemble`, `aliceBobMutualInfo := holevoChi (bobEnsemble atk a)`, `eveHolevoInfo := holevoChi (atk.eveEnsemble a)`, `keyRate atk a := aliceBobMutualInfo − eveHolevoInfo`. **`aliceBobMutualInfo_nonneg` and `eveHolevoInfo_nonneg` PROVED** as direct corollaries of `holevoChi_nonneg`. `keyRate_nonneg_of_eve_le_bob` (conditional, `linarith`) added as a typed placeholder — **not a security claim**; the universal `keyRate ≥ 0` is *false* in the current model (counterexample in file). 2026-05-09.
- 🟡 [parameter-estimation](parameter-estimation.md) — **Bar 2 in progress.** Why universal `keyRate_nonneg` fails (measure-Z-resend-`|+⟩` attack); the five subtasks needed to reach `keyRate ≥ 1 − 2 h(δ)`. **#1 (`QBER`) ✅ done** — `Adversary/QBER.lean` defines `bobMistakeProb`, `QBER`, with `0 ≤ QBER ≤ 1` proved. #2–#5 (SymmetricAttack subclass, `χ(A;E) ≤ h(δ)`, `I(A;B) = 1 − h(δ)`, assemble) still ahead. 2026-05-09.

## Correctness proofs

*(no entries yet — sifting, key-agreement statements)*

## Security proofs

*(no entries yet — Eve information bounds, detection probability, composability)*

## Infrastructure / tooling

- 🟢 [physlib-dependency](physlib-dependency.md) — PhysLib pinned at commit `c8fa2271`; `import QuantumInfo.Finite.Entropy.VonNeumann` works; gotchas: `lake update` (no args, not `lake update Physlib`) and **PhysLib has no `QuantumInfo` Lean namespace** — definitions are at root or under `MState`/`Qubit`/etc. 2026-05-08.
- 🟢 `Information/PartialTraceInner.lean` — `⟪ρ, X ⊗ 1⟫ = ⟪ρ.traceRight, X⟫` and the symmetric form. Built on PhysLib's `Matrix.trace_mul_kron_one_right`. Good upstream candidate. 2026-05-08.
- 🟢 `Information/QMutualInfoRelEnt.lean` — `qMutualInfo_eq_qRelativeEnt_marginals` (nonsingular version of PhysLib's sorry'd stub). Provable from partial-trace identities + `log_kron`. 2026-05-08.
- 🟢 `Information/HolevoBound.lean` — **`holevoBound` PROVED** via Klein-style chain + DPI; bypassed the joint entropy decomposition by using `χ(e) = Σᵢ pᵢ · D(ρᵢ ‖ mix e)` instead. 2026-05-08.
