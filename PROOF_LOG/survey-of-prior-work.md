# Survey of prior work — implications for modeling

**Status:** 🔵 reference (informs early modeling decisions; no proof yet)
**Last updated:** 2026-05-08

## Context

Before writing any definitions, we surveyed the landscape of (a) BB84 and its security proofs, (b) prior Lean / Coq / Isabelle formalizations of quantum systems and quantum cryptography, and (c) cryptographic-protocol verification methodology. Annotated bibliography lives in `material/SURVEY.md`. This entry records the **conclusions for our project** — the modeling stances and prioritization that follow from what we read.

## Findings that change our plan

### F1. **PhysLib (formerly Lean-QuantumInfo) already provides the quantum-information substrate we need.**

PhysLib (`leanprover-community/physlib`, merged March 2026, Lean 4.29.1, ~38k LOC, ~2143 theorems) defines finite-dim Hilbert spaces, density operators, **CPTP channels**, POVMs, **classical-quantum states**, von Neumann entropy, mutual information, trace distance, and the Generalized Quantum Stein's Lemma. Top-level namespaces: `ClassicalInfo`, `QuantumInfo`, `StatMech`.

**Implication:** Do **not** define `DensityMatrix`, `QuantumChannel`, `POVM`, etc. from scratch. The first concrete infrastructure task is to **add PhysLib as a Lake dependency** and import its `QuantumInfo` namespace where we need quantum primitives. If a definition we want is missing, prefer upstreaming a contribution to PhysLib over creating a parallel definition in our repo.

This is the dominant application of design principle #2 ("borrow before inventing") for the entire project.

### F2. **Shor–Preskill (2000) is the right proof scaffold for BB84 correctness + security.**

The Shor–Preskill proof reduces BB84 security in three stages:
1. Ideal Lo–Chau-style entanglement-distillation protocol (proven secure directly).
2. CSS-code-based protocol with classical post-processing only (security inherited via CSS structure).
3. Prepare-and-measure BB84 (security inherited from #2 because Alice's preparation can be deferred without changing observable statistics).

**Implication:** Plan the modeling around being able to state and prove all three protocols in the same framework, and to prove the two reduction theorems between them. The protocol model must therefore admit:
- An **entanglement-based view** (for stages 1–2)
- A **prepare-and-measure view** (for stage 3)
- A formal equivalence between them

This is exactly the kind of "supports both views" requirement that motivates design principle #1 (faithful enough not to fork the model). The decision of how to encode the protocol must be revisited once we read the proof in detail; do not commit to a representation before reading `material/shor-preskill-bb84-security.pdf` carefully.

### F3. **Composable security (Renner) is the *target statement*, not a corollary.**

Renner's thesis (`material/renner-thesis-qkd-security.pdf`) and Müller-Quade–Renner (`material/muller-quade-renner-composability.pdf`) make the case that the right top-level security theorem for QKD is **composable** — a bound on the trace distance between (real protocol output state) and (ideal key + adversary side-information). Not just "Eve's mutual information with the key is small."

**Implication:** When stating the top-level theorem, frame it as a trace-distance bound with explicit smooth-min-entropy / leftover-hash-lemma machinery, not as a Shannon-mutual-information bound. PhysLib has trace distance and entropies, so this is feasible. Open question whether PhysLib has the **leftover hash lemma** — needs investigation before committing.

### F4. **`Abraxas1010/hybrid-crypto-qkd-pqkem-lean` is not a proof foundation.**

Despite being the only Lean 4 repo named like a BB84 formalization, its security predicates are placeholder `True` (verified by inspection of the README, 2026-05-08). BB84 is on its Phase 3 roadmap. We will not build on it. We may, separately, look at its **type-level interface** for how it organizes "QKD as ideal key source" — purely as a packaging idea.

### F5. **Methodology for quantum-adversary security games comes from EasyPQC, not from quantum-program-verification frameworks.**

CoqQ / SQIR / Qbricks are about quantum *programs* (algorithms, circuits). They are not about cryptographic *games* with reductions and adversaries. EasyPQC (Barbosa et al., CCS 2021) is the most mature methodology for proving security against quantum adversaries via reductions — and SSProve is the methodological reference for foundational, modular crypto proofs in Coq.

**Implication:** When designing the *adversary* and *game* abstractions in Lean, look at EasyPQC's QROM modeling and SSProve's state-separating-proof packaging. Keep the program-logic frameworks (CoqQ, SQIR) in mind for inspiration on *state* and *channel* representations only, not for the proof-architecture.

### F6. **`quantum-steins-lemma-lean` is the closest stylistic precedent.**

The Hayashi–Yamasaki Stein's-lemma formalization in Lean (arXiv:2510.08672, Oct 2025) is built on Lean-QuantumInfo / PhysLib, uses finite-dim Hilbert spaces, and reports finding gaps in the published proof during formalization. It is the closest stylistic precedent for what we are doing: a *single information-theoretic theorem about a quantum protocol/process, mechanized in Lean 4 atop PhysLib*.

**Implication:** Read this paper alongside the PhysLib codebase to absorb conventions before introducing our own. When we make a stylistic choice that diverges from theirs, leave a comment.

## Reference-only findings (kept for record)

- **CoqQ** (POPL 2023, `material/coqq-quantum-programs.pdf`): mature Coq quantum Hoare logic with Dirac assertions. Worth reading for state/channel modeling style. Not a target ecosystem.
- **SQIR / VOQC** (`material/sqir-proving-quantum-programs.pdf`): circuit-oriented Coq, less directly applicable.
- **Qbricks** (Why3 + SMT, summarized in `material/chareton-fm-quantum-survey.pdf`): automated, circuit-oriented; far from our reduction-based proof.
- **Boender et al. 2015** (`material/boender-coq-quantum-protocols.pdf`): early Coq formalization of quantum protocols including BB84-shaped reasoning. Predates modern frameworks; useful for conceptual framing of "protocol" vs "algorithm."
- **Surveys** (`material/lewis-fv-quantum-survey.pdf`, `material/chareton-fm-quantum-survey.pdf`): orientation reading.
- **Lean-QuantumInfo's older state** (~14k LOC) reported in some sources — outdated; use the current ~38k-LOC PhysLib figure.

## Concrete next steps that follow from this survey

These are **not yet acted on** — recording so they can be picked up by the next session:

1. **Add PhysLib as a Lake dependency.** Inspect `leanprover-community/physlib`'s `lakefile.lean` to copy the right `[[require]]` block. Verify build succeeds. Open a new PROOF_LOG entry `physlib-dependency.md` documenting the choice.
2. **Read `material/shor-preskill-bb84-security.pdf` carefully** and write `PROOF_LOG/proof-strategy.md` recording the three-stage reduction in our own words, with a sketch of which Lean modules will host each stage.
3. **Inventory PhysLib's QuantumInfo namespace** for: density matrices, CPTP channels, POVMs, classical-quantum states, trace distance, von Neumann entropy, **leftover hash lemma** (open whether present). Record what's there in `PROOF_LOG/physlib-coverage.md`.
4. **Decide qubit / basis representation** only after #2 and #3 — the choice depends on what PhysLib gives us and what the Shor–Preskill proof needs concretely.

## References

- `material/SURVEY.md` — full annotated bibliography
- `material/shor-preskill-bb84-security.pdf`, `material/renner-thesis-qkd-security.pdf`, `material/muller-quade-renner-composability.pdf`
- `material/quantum-steins-lemma-lean.pdf`
- <https://github.com/leanprover-community/physlib> (current home of QuantumInfo)
- <https://github.com/Timeroot/Lean-QuantumInfo> (predecessor)
