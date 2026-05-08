# PhysLib (`QuantumInfo`) coverage for our project

**Status:** 🔵 reference (inventory of an upstream library; informs framework choice)
**Last updated:** 2026-05-08

## Context

Before committing to Devetak–Winter / collective-attacks / asymptotic security as our v1 proof framework (see `proof-framework.md`), we needed to confirm that PhysLib's `QuantumInfo` namespace actually supplies the entropic and operational machinery the proof depends on. This entry records what was found — file references are to a clone of `leanprover-community/physlib@main` taken on 2026-05-08.

## Package facts

- Repo: <https://github.com/leanprover-community/physlib>
- Lean toolchain: `leanprover/lean4:v4.29.1` — **identical to ours**
- Mathlib pin: `v4.29.1` — identical to ours
- Lake package name: `«Physlib»`
- Two `lean_lib`s: `Physlib` (physics, irrelevant to us) and `QuantumInfo` (what we want). We can depend on the package and import only `QuantumInfo` modules.
- Build flags include `-Dwarn.sorry=false` (warns but allows). We should keep our project stricter (no `sorry` admitted).

## What's present (with file references)

### Quantum states, channels, measurements

| Concept | Definition | File |
|---|---|---|
| Mixed state (density operator) | `MState` | `QuantumInfo/Finite/MState.lean` |
| Pure state (ket) | `Ket` | `QuantumInfo/Finite/Braket.lean` |
| Classical-as-quantum embedding | `MState.ofClassical` | used in `POVM.lean:133`, `HypothesisTesting.lean:390` |
| CPTP channel | `CPTPMap` | `QuantumInfo/Finite/CPTPMap.lean` and `CPTPMap/` subdir |
| n-fold parallel channel | `CPTPMap.piProd` | `QuantumInfo/Finite/CPTPMap/MatrixMap.lean:405`, used in `Capacity.lean:85` |
| Tensor-power state notation | `⊗ᵣ^[n]` | seen in `ResourceTheory/SteinsLemma.lean` |
| POVM / measurement | `POVM` | `QuantumInfo/Finite/POVM.lean` |
| Measurement → classical readout | `(Λ.measurementMap ρ).traceLeft = MState.ofClassical (Λ.measure ρ)` | `POVM.lean:133` |
| Pinching channel (dephasing in σ-eigenbasis) | `pinching_map` | `QuantumInfo/Finite/Pinching.lean:88` |
| Trace distance | (in `Distance/TraceDistance.lean`) | `QuantumInfo/Finite/Distance/TraceDistance.lean` |
| Fidelity | (in `Distance/Fidelity.lean`) | `QuantumInfo/Finite/Distance/Fidelity.lean` |
| Unitary group | `Unitary.lean` | `QuantumInfo/Finite/Unitary.lean` |

### Qubits and BB84-relevant gates

| Concept | Definition | File |
|---|---|---|
| Qubit | `abbrev Qubit := Fin 2` | `Qubit/Basic.lean:21` |
| Pauli X / Y / Z | `X`, `Y`, `Z : 𝐔[Qubit]` | `Qubit/Basic.lean:58–66` |
| **Hadamard** | `noncomputable def H : 𝐔[Qubit]` | `Qubit/Basic.lean:70` |
| S, T phase gates | | `Qubit/Basic.lean:74,78` |
| CNOT, controlled-U | `CNOT`, `controllize` | `Qubit/Basic.lean:140,159` |
| Algebraic identities | `H * X = Z * H`, `H_sq`, etc. | `Qubit/Basic.lean:94,119,123` |

The Hadamard gate's existence + the `H * X = Z * H` and `H_sq` identities means the BB84 basis-switching algebra is already covered.

### Probability / classical info

| Concept | Definition | File |
|---|---|---|
| Discrete distribution | `ProbDistribution` / `Distribution` | `QuantumInfo/ClassicalInfo/Distribution.lean` |
| Random variable | `ProbDistribution.RandVar` | (used by `Ensemble.lean`) |
| Classical channel | (in `ClassicalInfo/Channel.lean`) | `QuantumInfo/ClassicalInfo/Channel.lean` |
| Shannon entropy `Hₛ` | (in `ClassicalInfo/Entropy.lean`) | used by `Sᵥₙ` definition |

### Ensembles (the {pᵢ, ρᵢ} structure underlying Holevo χ)

`QuantumInfo/Finite/Ensemble.lean` provides:

- `MEnsemble d α := ProbDistribution.RandVar α (MState d)` (line 20)
- `PEnsemble d α := ProbDistribution.RandVar α (Ket d)` (line 25)
- `MEnsemble.states`, `PEnsemble.states` — the ρᵢ family (lines 30, 33)
- `mix : MEnsemble d α → MState d` — the mixture Σ pᵢρᵢ (line 63)
- `average f e` — Σ pᵢ f(ρᵢ) for `f : MState → T` (line 89)
- `spectral_ensemble` — the spectral decomposition of ρ as a `PEnsemble` (line 303)

This means **Holevo χ is a one-liner**:
```
χ(e) = Sᵥₙ (mix e) - average e Sᵥₙ
```
on top of existing definitions. We will likely contribute this back to PhysLib rather than carrying it locally.

### Entropic quantities

In `QuantumInfo/Finite/Entropy/VonNeumann.lean`:

- `Sᵥₙ ρ` — von Neumann entropy (line ~64)
- `qConditionalEnt ρ` — S(A|B) (line 76)
- `qMutualInfo ρ` — I(A:B) (line 80)
- `coherentInfo ρ Λ` — coherent information (line 86)
- `qcmi` — conditional mutual information I(A;C|B) (in `SSA.lean`)
- `Sᵥₙ_nonneg` (line 95)
- `qMutualInfo_symm` (line 331)

In `QuantumInfo/Finite/Entropy/SSA.lean`:

- `qMutualInfo_strong_subadditivity` (line 1263) — SSA in mutual-info form

In `QuantumInfo/Finite/Entropy/Relative.lean`:

- Relative entropy `𝐃(ρ‖σ)`
- `qMutualInfo_as_qRelativeEnt` (line 2137) — I(A:B) = D(ρ_AB ‖ ρ_A ⊗ ρ_B)

In `QuantumInfo/Finite/Entropy/DPI.lean`:

- Sandwiched / Renyi relative entropy machinery: `H_hat α`, traceFunctional bounds, joint convexity
- *Note:* this file is the α-Renyi infrastructure, **not** a one-line "DPI for Sᵥₙ" lemma. The classical-channel DPI for von Neumann entropy / mutual information is derivable from SSA but doesn't appear to have a single named theorem. We'll likely add it or upstream it.

### Capacities

In `QuantumInfo/Finite/Capacity.lean`:

- `quantumCapacity` (line 89), `AchievesRate` (line 82), `Emulates` (line 70), `εApproximates` (line 76)
- `coherentInfo_le_quantumCapacity` (line 210), `quantumCapacity_eq_piProd_coherentInfo` (line 214) — LSD theorem statement
- **Holevo capacity is not yet defined** — only mentioned in module-level docstring (line 51). No `accessibleInformation`, no HSW theorem.

### Resource theory / Stein's lemma

`QuantumInfo/Finite/ResourceTheory/`:

- `FreeState`, `HypothesisTesting`, `ResourceTheory`, `SteinsLemma` — the Generalized Quantum Stein's Lemma is formalized (this is the headline result of arXiv:2510.08672).
- The `SteinsLemma.lean` file uses `MState (H i ^ n)` and `⊗ᵣ^[n]`, confirming **asymptotic / iid-tensor reasoning is first-class**.

## What's missing for our v1 proof

Listed in roughly the order we'll need them:

1. **Holevo χ as a named quantity.** Trivial to add: `χ e := Sᵥₙ (mix e) - average e Sᵥₙ`. ~5 lines.
2. **Holevo bound theorem** `I_acc(X; ρ_X) ≤ χ` (where I_acc is accessible information via any POVM). Standard textbook proof, ~50–200 lines using existing entropy lemmas. Likely upstreamable.
3. **General DPI for von Neumann entropy / mutual information** under classical channels, as a single named lemma. Derivable from SSA + monotonicity of Sᵥₙ under partial trace. Worth upstreaming.
4. **Concavity of `Sᵥₙ`** as a named lemma. Not located in the grep — likely derivable from `Hₛ` concavity and the spectral decomposition, but needs a check. Possibly already there under a different name.
5. **Devetak–Winter rate as a Lean theorem statement.** Project-internal, layered on top of #1–#4.
6. **BB84 protocol model itself.** Project-internal, no PhysLib analogue (and this is what we're here to build).

What is **NOT** missing (and we therefore do not need to build):
- Density operators, Kets, Bras, channels, POVMs, measurements
- Trace distance, fidelity
- Von Neumann entropy and conditional entropy and mutual information
- Tensor-power channels and states
- Pinching, ensembles, mixing, averaging
- Hadamard and the Pauli/Clifford gate algebra
- Classical embedding `MState.ofClassical`

## Implication for the framework choice

Devetak–Winter (`χ`-based, collective attacks, asymptotic) is **directly supported** by what's in PhysLib, modulo a small (~hundreds of LOC) gap consisting of Holevo χ, the Holevo bound, and a clean DPI lemma — each of which is a known, textbook result. By contrast:

- **Shor–Preskill** would additionally require a CSS-code formalization (stabilizer formalism + classical linear codes + the CSS construction + quantum error-correction proofs); none of this is in PhysLib. This is the dominant cost.
- **Pure Renner** would additionally require smooth min-entropy `H_min^ε`, the smoothing constructions, 2-universal hash families, and the **leftover hash lemma against quantum side-information**. Greps for `privacy`, `leftoverHash`, `secretKey`, `secrecy` returned **zero hits** in `QuantumInfo`. This is also a dominant cost.

The coverage gap for Devetak–Winter is roughly *one order of magnitude smaller* than for either alternative. That's the engineering basis for the v1 framework decision recorded in `proof-framework.md`.

## How to depend on PhysLib

Our `lakefile.toml` will need (roughly — verify when the time comes):

```toml
[[require]]
name = "Physlib"
git = "https://github.com/leanprover-community/physlib.git"
rev = "main"        # later: pin to a specific commit
```

Plus `mathlib` is already required transitively. Note the package name `«Physlib»` (with French quotes in PhysLib's lakefile) — when we depend on it, the `name = "Physlib"` form in our lakefile.toml should work; the quoted form is only how Lake parses identifiers internally.

## References

- Local clone for grepping: `/tmp/physlib-inventory` (transient; can be re-fetched with `git clone --depth 1 https://github.com/leanprover-community/physlib.git`)
- `material/quantum-steins-lemma-lean.pdf` — the paper that drove the recent QuantumInfo→PhysLib merge
- `PROOF_LOG/proof-framework.md` — the framework decision that depends on this inventory
- `PROOF_LOG/survey-of-prior-work.md` — broader landscape context
