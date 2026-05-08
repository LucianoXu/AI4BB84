# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project goal

Formally verify the **BB84 quantum key distribution protocol** in **Lean 4**, targeting two classes of theorems:

- **Functional correctness** — honest Alice and Bob, after sifting and (optionally) error correction + privacy amplification, agree on a shared key with the expected length and distribution.
- **Safety / security properties** — bounds on Eve's information about the final key, detection probability of an active eavesdropper, and composable security against the relevant adversary model.

Keep this dual focus in mind when designing definitions: the same protocol model should support both kinds of proofs without forking. If a definition only serves one side cleanly, that's a signal to reshape it.

## Design philosophy

Two principles govern every modeling decision in this repo:

1. **Balance faithful encoding against engineering / proof effort.** A definition that captures every physical nuance of qubits, channels, and adversaries but takes 200 lines to unfold is a worse foundation than a leaner one that abstracts away what the theorems don't actually need. Conversely, simplifications that erase a property the security argument depends on are not allowed — even if they save proof effort. Every time you introduce a new definition, ask: *what is the smallest model that still admits the theorems we need?* If you find yourself writing a long lemma to recover something a different definition would give for free, the definition is wrong, not the lemma.

2. **Borrow before inventing.** Look at Mathlib first, then at prior Lean / Coq / Isabelle formalizations of cryptographic protocols and quantum systems, then at the original BB84 / security-proof literature. Mathlib's `MeasureTheory`, `ProbabilityTheory`, `LinearAlgebra`, `Matrix`, and `InnerProductSpace` namespaces likely already encode what you need; reusing their conventions makes proofs shorter and gets you `simp` / `aesop` lemmas for free. When you do diverge from a Mathlib pattern, leave a one-line comment explaining why — future readers (including future Claude) need to know it was a deliberate choice.

These two principles often pull against each other (faithful = bigger, borrowed-from-Mathlib = sometimes more abstract than needed). Resolving the tension is the actual design work — don't paper over it.

## `material/`

Research papers, lecture notes, and reference write-ups that inform the formalization live in `material/`. When citing a result or following a definition from a paper, mention the filename in a comment near the relevant Lean code so the chain of provenance is recoverable. Drop new references in as you find them; this folder is the project's reading list.

## `PROOF_LOG/` — long-term project memory (READ FIRST)

`PROOF_LOG/` is the repo's durable working memory: every non-trivial **formalization choice, attempt, dead-end, discovery, and result** is recorded there so a future agent (Claude or human) can pick up where the last one left off without re-deriving the reasoning. It is checked into git and travels with the repo, distinct from any agent's private/machine-local memory.

**Structure.** One markdown file per topic, plus a curated `INDEX.md`:

```
PROOF_LOG/
├── INDEX.md                       — curated table of contents (read this first, every session)
├── qubit-state-encoding.md        — example: how qubits are represented and why
├── sifting-correctness.md         — example: the correctness statement for sifting and what's proved
└── …                              — one file per topic
```

Filenames are short kebab-case nouns/topics, not dates. `INDEX.md` provides chronology and curation: it lists each entry with a one-line hook, optionally grouped by area (modeling, correctness, security, infrastructure).

**When to read.**
- At the start of any session that touches modeling, proofs, or design choices, **read `PROOF_LOG/INDEX.md` first**, then any entries the index suggests are relevant. This is non-negotiable — the log exists to prevent re-litigating settled decisions and re-walking known dead-ends.
- Before introducing a new definition or proof strategy, grep `PROOF_LOG/` for the concept; an entry may already record why an earlier attempt failed.

**When to write.**
- After making a non-trivial modeling decision (e.g. "qubits as `Fin 2 → ℂ`, not as `Matrix.unitGroup`"), record what was chosen, what alternatives were considered, and why.
- After a failed attempt that's worth not repeating: write up the dead-end so future agents skip it.
- After a discovery that changes how the proof should be structured.
- After completing a proof that's load-bearing for later work, summarize the statement, the key lemmas it depends on, and any axioms (`#print axioms`).
- Update `INDEX.md` in the same edit. An entry with no index pointer is invisible.

**What NOT to put in `PROOF_LOG/`.**
- Routine *what changed* — that's git history. The log captures *why* and *what was tried*.
- Paper summaries — those go in `material/`. The log may *cite* a paper from `material/` but not duplicate it.
- TODO lists for the current session — use Claude's task tool, not the log.
- Personal preferences or environment quirks — those belong in private agent memory, not the shared log.

**Entry format.** Keep it loose and useful, not bureaucratic. A workable shape:

```markdown
# <Topic>

**Status:** open question | decided | proved | abandoned
**Last updated:** 2026-05-08

## Context
<what we're trying to do, in 1-3 sentences>

## What was tried / decided
<the substance>

## Why
<the reasoning, including alternatives ruled out>

## References
- material/<paper>.pdf §X
- AI4BB84/<file>.lean — `theoremName`
- PROOF_LOG/<other-entry>.md — for cross-cutting context
```

Sections can be added or dropped; the goal is recoverability, not conformance.

**Hygiene.** When a decision is reversed, do not delete the old entry — mark it `Status: superseded by <new-entry>.md` and add a `Why superseded:` paragraph. The log's value is partly in showing the path, including wrong turns.

## Layout

```
.
├── AI4BB84.lean        — umbrella module; should re-export the protocol's public API
├── AI4BB84/            — implementation modules; create new files here
│   └── Basic.lean      — placeholder; replace as the project grows
├── lakefile.toml       — package config (name "AI4BB84", Mathlib v4.29.1, lints enabled)
├── lean-toolchain      — pins leanprover/lean4:v4.29.1
├── lake-manifest.json  — dependency lockfile (auto-managed)
├── material/           — research papers and reference notes (see "material/" above)
├── PROOF_LOG/          — durable record of formalization decisions & attempts (see "PROOF_LOG/" above)
├── .lake/              — build artifacts (gitignored)
└── .github/            — CI workflows generated by the math template
```

The library is named `AI4BB84` (matching the directory). All source modules go under the `AI4BB84` namespace, e.g. `AI4BB84/Protocol/Sifting.lean` becomes `AI4BB84.Protocol.Sifting`. The umbrella file `AI4BB84.lean` should `import` each public sub-module so a downstream user can `import AI4BB84` and get everything. Keep internal helpers out of the umbrella.

The `lakefile.toml` enables several non-default options worth knowing:

- `relaxedAutoImplicit = false` — Lean will not silently introduce auto-bound implicit variables for unknown identifiers. If you reference an undeclared name in a binder, you'll get an error rather than a mystery type variable. Embrace this; it catches typos.
- `weak.linter.mathlibStandardSet = true` — Mathlib's full linter set is on. Expect warnings about naming conventions, missing docstrings on public defs, unused arguments, etc. Treat these as actionable, not noise.
- `pp.unicode.fun = true` — pretty-prints `fun a ↦ b`.

## Toolchain

Lean is installed via `elan` at `~/.elan/bin` (added to `PATH` via `~/.profile`). Versions at the time this file was written:

- `elan` 4.2.1
- `lean` 4.29.1 (the default `stable` toolchain)
- `lake` 5.0.0

A project's own `lean-toolchain` file pins its required Lean version; elan auto-installs that version on first `lake build`. Do not edit `lean-toolchain` casually — bumping it can trigger a Mathlib re-download and a long rebuild.

If `lean` / `lake` are not on `PATH` in a fresh shell, `source ~/.profile` (or open a login shell).

## Common commands

Run from the project root.

```bash
lake build                       # compile everything
lake build AI4BB84.Basic         # compile one module (replace with the path you're iterating on)
lake exe cache get               # download Mathlib oleans — run after lake update or after switching mathlib rev. Skipping it forces a from-source Mathlib rebuild (hours).
lake env lean AI4BB84/Basic.lean # type-check one file with the project env (fastest single-file feedback)
lake clean                       # clear build artifacts (rarely needed; prefer targeted rebuilds)
lake update                      # update dependencies per lakefile — only run when intentionally bumping mathlib
```

There is no test target defined yet. When tests are added (likely as a separate `lean_lib` like `Test`), document the runner here.

## Working with proofs

A few conventions that will matter for this codebase regardless of how it's organized:

- **`sorry` is a TODO marker, not a tolerated state.** Any commit/PR claiming a theorem is proved must build cleanly without `sorry` in the proof of that theorem. Use `#print axioms TheoremName` to confirm a theorem doesn't transitively depend on `sorryAx` before declaring it done.
- **Prefer `theorem` over `lemma` for named protocol-level results** (correctness, security bounds) so they're easy to grep for. Use `lemma` for local technical helpers.
- **Quantum state representation matters.** BB84 only needs qubit states + computational/Hadamard bases, so resist pulling in heavyweight general quantum frameworks unless they already exist in Mathlib. A minimal, BB84-specific model (states as `Fin 2 → ℂ` or basis-tagged vectors) is usually faster to reason about than a categorical formulation.
- **Probabilistic reasoning** should go through Mathlib's `MeasureTheory` / `ProbabilityTheory` namespaces rather than ad-hoc reals. The security proofs hinge on this, so a homegrown probability layer will become a liability.

## Notes for future Claude

- The repo is scaffolded but contains no protocol code yet — only Lake's `def hello := "world"` placeholder in `AI4BB84/Basic.lean`. Replace the placeholder, don't grow it.
- When adding a new top-level concept (channel model, adversary model, sifting procedure, error-correction stub), add a short architecture section here listing the namespace and what lives in it. Don't let this file drift out of sync with the protocol model.
- The user works on BB84 as a formal verification target, not as an implementation — runtime performance of Lean code is not a goal; proof-friendliness of definitions is.
