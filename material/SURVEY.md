# Survey of prior work

Annotated index of references collected for the BB84 formalization. Group by what role the reference plays in our project. Each entry: author/title, what it is, **relevance** (★☆☆ low / ★★☆ medium / ★★★ high), and how we expect to use it.

Last updated: 2026-05-08.

---

## A. BB84 protocol & security proofs (the *target*)

### A1. Bennett & Brassard, "Quantum cryptography: Public key distribution and coin tossing" (1984) ★★★
*Not in this folder — original conference proceeding, hard to find canonically.* The BB84 protocol itself. Use only as historical anchor; the modern statement comes from later sources.

### A2. `shor-preskill-bb84-security.pdf` — Shor & Preskill, *Phys. Rev. Lett.* 85, 441 (2000), arXiv:quant-ph/0003004 ★★★
*"Simple Proof of Security of the BB84 Quantum Key Distribution Protocol."* Reduces BB84 security to an entanglement-purification protocol via CSS codes, building on Lo–Chau. Short (4 pages PRL). **This is likely the proof scaffold we formalize.** The reduction has three layers: (i) ideal entanglement-distillation protocol; (ii) CSS-code-based reduction that removes the need for quantum computation; (iii) prepare-and-measure equivalence to BB84.

### A3. `renner-thesis-qkd-security.pdf` — Renner, "Security of Quantum Key Distribution" (PhD thesis, ETH 2005), arXiv:quant-ph/0512258 ★★★
The canonical reference for **information-theoretic, composable** security of QKD. Introduces smooth min/max entropies and the framework that gets cited everywhere downstream. ~150 pages. Heavy. Use as the source for definitions of composable security and finite-key bounds.

### A4. `muller-quade-renner-composability.pdf` — Müller-Quade & Renner, "Composability in quantum cryptography" (2009), arXiv:1006.2215 ★★☆
Survey/exposition on what *composable* security means for QKD specifically. Use to nail down the right top-level theorem statement; shorter and more readable than A3 for that purpose alone.

---

## B. Direct prior art in Lean

### B1. Lean-QuantumInfo / PhysLib (Alex Meiburg / Timeroot, now community-maintained) ★★★
GitHub: <https://github.com/Timeroot/Lean-QuantumInfo> and <https://github.com/leanprover-community/physlib>. **Merged into PhysLib (leanprover-community) March 2026.** ~38k LOC, ~2143 theorems, ~423 definitions in Lean 4.29.1.

Provides finite-dimensional Hilbert spaces, density operators, **CPTP channels**, POVMs, **classical-quantum states**, von Neumann entropy, mutual information, trace distance, and the Generalized Quantum Stein's Lemma. Three top-level namespaces: `ClassicalInfo`, `QuantumInfo`, `StatMech`.

**Use as a dependency, do not reinvent.** Adding PhysLib as a Lake dependency should be one of the first concrete tasks.

### B2. `quantum-steins-lemma-lean.pdf` — Hayashi-Yamasaki-style Generalized Quantum Stein's Lemma in Lean (Oct 2025), arXiv:2510.08672 ★★★
The companion paper to B1. Read this for the *style* of doing quantum information proofs in Lean 4 — definitions, naming conventions, how classical-quantum states are represented, what tactics work. The paper also reports gaps found in the published proof during formalization, an example of the kind of rigor we should emulate.

### B3. `Abraxas1010/hybrid-crypto-qkd-pqkem-lean` (GitHub) ★☆☆
A Lean 4 sketch of *hybrid* (QKD + post-quantum KEM) key establishment. Inspected 2026-05-08: **security predicates are placeholder `True`**; BB84 security is listed as Phase-3 future work. Useful only as a structural reference for how someone organized the type-level interface (`KeySource`, `IdealKeyExchange`, `hybrid_security`). **Not** a proof foundation.

### B4. `duckki/lean-quantum` (GitHub) ★☆☆
Older `lean-quantum` library on top of Mathlib (likely Lean 3 / early Lean 4). Provides matrices and Kronecker product. Largely superseded by B1; check only if a specific lemma is missing from PhysLib.

---

## C. Quantum reasoning frameworks (for *proof-engineering* inspiration)

### C1. `coqq-quantum-programs.pdf` — Zhou, Yang, Hung, Hong, Ying, "CoqQ: Foundational Verification of Quantum Programs," POPL 2023, arXiv:2207.11350 ★★★
Coq framework with a **quantum Hoare logic** and Dirac-notation assertions. Sound w.r.t. denotational semantics. Most mature non-Lean ecosystem. Read for: how to structure a program logic for quantum programs, and how local/parallel reasoning is set up. Even if we don't write a Hoare logic, the *modeling* of states, channels, and projections is high-quality.

### C2. `sqir-proving-quantum-programs.pdf` — Hietala et al., "Proving Quantum Programs Correct" (2020 / extended TOPLAS 2023), arXiv:2010.01240. Repo: <https://github.com/inQWIRE/SQIR> ★★☆
A small quantum IR deeply embedded in Coq, with a verified optimizer (VOQC). More circuit-oriented than QKD-relevant, but the embedding and matrix semantics are clean. Compare with PhysLib's choices when modeling channels.

### C3. Qbricks (Why3 + SMT, Chareton et al., FoSSaCS 2021, also in `chareton-fm-quantum-survey.pdf`) ★☆☆
Path-sum based, automated, oriented at quantum *circuits* (Grover, Shor). Architecturally distant from a reduction-based crypto proof; useful mainly for *survey* awareness.

### C4. Liu, Zhan et al., "Formal verification of quantum algorithms using quantum Hoare logic," CAV 2019 (Isabelle, ~11.5k lines) ★☆☆
Mentioned in the surveys (D1/D2). Demonstrates feasibility of mechanizing quantum Hoare logic in Isabelle. Reference only.

### C5. `boender-coq-quantum-protocols.pdf` — Boender, Kammüller, Nagarajan, "Formalization of Quantum Protocols using Coq" (2015), arXiv:1511.01568 ★★☆
Early attempt at formalizing quantum *protocols* (not algorithms) including BB84-shaped reasoning in Coq. Pre-dates CoqQ and SQIR. Read for the **conceptual framing** of what a "protocol" formalization needs (state evolution, classical channel, measurements as random variables) — the actual Coq code is unlikely to be the foundation we extend.

---

## D. Surveys (for orientation)

### D1. `lewis-fv-quantum-survey.pdf` — Lewis, Soudjani, Zuliani, "Formal Verification of Quantum Programs: Theory, Tools, and Challenges," ACM TQC 2023, preprint arXiv:2110.01320 ★★★
Best single overview of the field. Read first if unfamiliar. Maps tools (CoqQ, SQIR, Qbricks, QHL-Isabelle, ...) against use cases.

### D2. `chareton-fm-quantum-survey.pdf` — Chareton, Bardin, Lee, Valiron, Vilmart, Xu, "Formal Methods for Quantum Programs: A Survey," arXiv:2109.06493 ★★☆
Complementary to D1, slightly more focus on circuit-building / Why3 perspective.

---

## E. Cryptographic-protocol verification (for *security-game* methodology)

### E1. `easypqc-post-quantum-verif.pdf` — Barbosa et al., "EasyPQC: Verifying Post-Quantum Cryptography," CCS 2021, eprint 2021/1253 ★★☆
Extends EasyCrypt to handle quantum adversaries (QROM). Closest mature methodology for **security games against quantum adversaries**. Borrow patterns: how reductions are written, how adversary types are quantified, how the QROM is modeled. We will not use EasyCrypt itself, but the *structure* of the proofs is what we want to mimic in Lean.

### E2. SSProve (Coq, foundational state-separating proofs) — *not in this folder; arXiv 2101.06541 if needed* ★★☆
Modular, code-based crypto proofs in Coq. Useful template for how to structure protocol vs. ideal-functionality games in a proof assistant.

### E3. FCF (Petcher–Morrisett, Coq Foundational Cryptography Framework) ★☆☆
Older, classical-adversary only. Reference for monad-based probabilistic computation modeling.

---

## How to use this folder

- When citing a paper from Lean code, quote the filename: e.g. `-- See material/shor-preskill-bb84-security.pdf §III for the CSS-code reduction.`
- If you add a new reference, append an entry here with the same fields (citation, what it is, ★ relevance, how we plan to use it). Don't just drop a PDF and forget.
- High-level *implications for our modeling* are not recorded here — they go in `PROOF_LOG/survey-of-prior-work.md` and downstream entries.
