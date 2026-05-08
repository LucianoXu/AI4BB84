# PhysLib (`QuantumInfo`) Lake dependency

**Status:** 🟢 decided / wired (2026-05-08)
**Last updated:** 2026-05-08

## Context

`PROOF_LOG/proof-framework.md` commits us to Devetak–Winter security on top of PhysLib's `QuantumInfo` namespace. This entry records the actual Lake wiring — including two gotchas that the next session would otherwise rediscover.

## What was added

`lakefile.toml` now contains:

```toml
[[require]]
name = "Physlib"
git = "https://github.com/leanprover-community/physlib.git"
rev = "c8fa2271"
```

Pinned to commit `c8fa2271` (`feat: Fix CI breaking (#1089)`, master tip on 2026-05-08). Pinning to a specific commit rather than a branch keeps builds reproducible across machines and across time.

`AI4BB84/Basic.lean` is now a smoke test exercising real PhysLib definitions:

```lean
import QuantumInfo.Finite.Entropy.VonNeumann
import QuantumInfo.Finite.Qubit.Basic

example {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) : 0 ≤ Sᵥₙ ρ :=
  Sᵥₙ_nonneg ρ

example {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    (ρ : MState (dA × dB)) : qMutualInfo ρ.SWAP = qMutualInfo ρ :=
  qMutualInfo_symm ρ
```

Both compile.

## Gotchas (recorded so the next session doesn't repeat them)

### G1. `lake update Physlib` does not register a *new* dependency in the manifest.

When PhysLib was added to `lakefile.toml` and `lake update Physlib` was run, Lake **cloned PhysLib and its transitive dependencies** but did **not** write `Physlib` into `lake-manifest.json`. The next `lake build` then failed with:

```
error: dependency 'Physlib' not in manifest; use `lake update Physlib` to add it`
```

Workaround: run **`lake update`** with no arguments. Plain `lake update` re-reconciles the manifest against the lakefile and registers new packages. The named-package form is for refreshing existing entries.

### G3. `lake build AI4BB84` is ambiguous and silently builds the wrong thing.

After PhysLib was added as a dependency, `lake build` (no args) and `lake build AI4BB84` started reporting "Build completed successfully (8743 jobs)" without actually building anything in `AI4BB84/`. The umbrella's `defaultTargets = ["AI4BB84"]` silently lost to PhysLib's own `@[default_target]` annotations on its `Physlib` and `QuantumInfo` libraries when the package and library names collide (our package is also named `AI4BB84`).

**Workaround:** disambiguate with `@`:

```bash
lake build @AI4BB84       # builds the AI4BB84 package's defaults
```

Symptom that exposed this: a freshly-added module produced no `.olean`, no warnings, and exit code 0 — but `find .lake/build/lib/lean/AI4BB84` showed only the older modules. With `@AI4BB84` the build sees the new module and either compiles it or surfaces real Lean errors.

### G2. The Lean *namespace* in PhysLib is not `QuantumInfo`.

`QuantumInfo` is the *library* name (the `lean_lib QuantumInfo` declaration in PhysLib's `lakefile.lean`), which determines that source files at `QuantumInfo/X/Y.lean` are imported as `import QuantumInfo.X.Y`. **It is not the Lean namespace** the definitions live in.

A first attempt at the smoke test wrote:

```lean
open QuantumInfo
example ... := Sᵥₙ_nonneg ρ
```

and failed with `unknown namespace 'QuantumInfo'`. Inspection of the source confirmed:

- `VonNeumann.lean` does *not* declare `namespace QuantumInfo`. `Sᵥₙ`, `qMutualInfo`, `qConditionalEnt`, `coherentInfo` etc. live in the **root namespace**.
- `MState.lean` declares `namespace MState` (so `MState.SWAP` etc. are nested under `MState`, but `MState` itself is at root).
- `Qubit/Basic.lean` declares `namespace Qubit` (so `Qubit.X`, `Qubit.H` etc.).

**Convention:** when importing PhysLib, do not write `open QuantumInfo`. Open specific namespaces only as needed (e.g. `open MState` if you want unqualified access to `MState.*` declarations).

## Dependency graph after `lake update`

PhysLib pulls in two extra direct deps (`BibtexQuery`, `MD4Lean`) and several indirect ones (`doc-gen4`, `leansqlite`, `UnicodeBasic`). Total package count went from 9 to 15. None of these affect our build other than `Physlib` itself; they are PhysLib build-side concerns.

Mathlib version did **not** change — both PhysLib and our project pin `mathlib v4.29.1`, so Lake reuses the existing manifest entry.

## Build cost

- **Cold build** of `lake build AI4BB84` after adding PhysLib compiled all of `QuantumInfo` from source (Mathlib oleans were already cached from scaffolding). 8307 modules total; on the order of several minutes wall-clock. There is **no** PhysLib-side olean cache analogous to Mathlib's `lake exe cache get`, so anyone setting up this repo on a fresh machine will pay the cold-build cost once.
- **Incremental rebuild** after editing only `AI4BB84/Basic.lean` is **<10s** (8.6s on this machine). PhysLib oleans are persistent under `.lake/packages/Physlib/.lake/build/` and are reused.

If cold-build cost becomes a recurring issue (e.g. CI), options to consider later:
1. Cache `.lake/packages/Physlib/.lake/build/` between CI runs (PhysLib is a pinned commit, so the cache is content-stable).
2. Watch upstream for a community-distributed PhysLib olean cache.

Both are deferrable; not blocking.

## Verification

`lake build AI4BB84` exits 0; both smoke-test `example`s compile. The basic functions of the dependency (importing `MState`, `Sᵥₙ`, `qMutualInfo`, `MState.SWAP`, `Sᵥₙ_nonneg`, `qMutualInfo_symm`) are all reachable from project code.

## References

- `lakefile.toml` — the `[[require]]` block for PhysLib
- `lake-manifest.json` — pinned commit recorded
- `AI4BB84/Basic.lean` — the smoke test
- `PROOF_LOG/physlib-coverage.md` — what we expect to use from PhysLib
- `PROOF_LOG/proof-framework.md` — why PhysLib is the chosen substrate
- <https://github.com/leanprover-community/physlib> commit `c8fa2271`
