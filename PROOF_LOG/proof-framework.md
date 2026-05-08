# v1 proof framework: Devetak–Winter / collective attacks / asymptotic

**Status:** 🟢 decided (v1 target locked in 2026-05-08 after PhysLib inventory)
**Last updated:** 2026-05-08

## Decision

The v1 security theorem for our BB84 formalization will be the **Devetak–Winter asymptotic key rate against collective attacks**:

> For an honest run of BB84 followed by classical post-processing (error correction + privacy amplification), the asymptotic secret-key rate against a *collective* attacker satisfies
>
>   r ≥ I(A;B) − χ(A;E)
>
> where I(A;B) is the classical mutual information between Alice's and Bob's sifted strings, and χ(A;E) is the Holevo information of the classical-quantum state Eve holds after the protocol.

This is the **v1** target. Coherent-attack security and finite-key / composable security are scoped as later upgrades on top — see "Upgrade path" below.

## Why this and not the alternatives

The user is indifferent between Shannon-MI-flavored and trace-distance-flavored security definitions, and explicitly asked: which path has the smallest **proof-engineering** cost?

The PhysLib inventory in `physlib-coverage.md` settled it:

| Framework | Quantum-info infrastructure missing in PhysLib | Approx. extra prerequisite work |
|---|---|---|
| **Devetak–Winter (this one)** | Holevo χ (5-line def); Holevo bound (~hundreds LOC); DPI-for-mutual-info lemma | small (~hundreds of LOC, mostly upstreamable) |
| Shor–Preskill / CSS reduction | Stabilizer formalism, CSS codes, quantum error-correction proofs, BBM92↔BB84 equivalence | large (likely thousands of LOC of pure quantum coding theory) |
| Pure Renner / smooth-min-entropy | `H_min^ε`, smoothing, 2-universal hashing, **leftover hash lemma against quantum side info** | large (zero hits in `QuantumInfo` for `privacy`/`secrecy`/`leftoverHash`) |

Devetak–Winter rests on machinery PhysLib already supplies (Sᵥₙ, qConditionalEnt, qMutualInfo, MEnsemble + mix + average, MState.ofClassical, POVMs, tensor powers, SSA, relative entropy, pinching, Hadamard + Pauli algebra). The other two require entire infrastructure layers we'd have to build first. For the same end (a publishable security theorem about BB84), that's an order-of-magnitude difference in prerequisite cost.

## Concretely, what we will state and prove

### Top-level theorem (informal)

For BB84 with parameters (n, basis-bias, post-processing), against a collective attacker who applies the same channel to each pulse and measures jointly at the end, the asymptotic key rate as n → ∞ is at least I(A;B) − χ(A;E), where the right-hand side is computed from observed sifted statistics (QBER) and the channel's classical-quantum output to Eve.

### Intermediate lemmas (the prerequisites we'll need to mechanize)

1. **Holevo χ** as a defined quantity on `MEnsemble`.
2. **Holevo bound**: I_acc(X; ρ_X) ≤ χ(e) for any POVM measurement on the ensemble e.
3. **Data processing for mutual information**: classical post-processing cannot increase I(A;B) above its value on the raw sifted strings; symmetrically for χ.
4. **Devetak–Winter rate theorem** (the headline) — proved by combining #2, #3, AEP-style asymptotic statements (already supported via `⊗ᵣ^[n]` and Stein's-lemma-style infrastructure), and a privacy-amplification step that here just needs the Holevo bound (not the leftover hash lemma).
5. **BB84 → collective-attack model**: the protocol's outputs are an i.i.d. sequence of classical-quantum states under the collective-attack assumption, justifying the use of asymptotic rate formulas.

Each of #1–#5 will get its own `PROOF_LOG/` entry once it has been worked through.

## What we are explicitly punting on (and why it's OK)

- **Coherent attacks.** Eve might use a single coherent operation across all n pulses rather than the same operation per pulse. Devetak–Winter does not directly cover this. The standard upgrade is a **de Finetti reduction** for symmetric protocols (Renner thesis ch. 4–5), which lets us reduce coherent → collective. This is a separate, well-understood result; adding it later does not invalidate the v1 proof, it strengthens its conclusion.
- **Finite-key bounds.** Our v1 theorem is asymptotic (n → ∞). Practical QKD bounds the key rate for finite n; this is the finite-key regime where smooth min-entropy and the leftover hash lemma become unavoidable. Punted to a later milestone.
- **Composability.** The trace-distance-from-ideal-key statement of Renner–König composability would require the leftover hash lemma against quantum side information. The v1 Holevo-bound version implies the *asymptotic, average-case* security needed to write a rate theorem, but is **not** by itself composable for downstream use. A later milestone will upgrade to composable security; the framework here does not preclude that upgrade.
- **Authentication / classical channel adversary.** We assume an authenticated classical channel (the standard QKD assumption). This is *not* what we are proving security against; this is the classical-cryptographic primitive QKD relies on.

## Upgrade path

This v1 framework was deliberately chosen to admit clean upgrades:

```
v1   Devetak–Winter / collective / asymptotic        ← we are here
 │
 ├── + de Finetti reduction       ⇒  coherent attacks (still asymptotic)
 │
 ├── + leftover hash lemma         ⇒  composable security (still asymptotic)
 │
 └── + smooth min-entropy machinery ⇒  finite-key / practical bounds
```

Each upgrade is largely *additive*: the protocol model, channel model, ensemble structure, and entropic infrastructure stay the same; later milestones add new lemmas without rewriting v1.

## Open prerequisite-checks before writing any v1 code

Recorded for the next session to act on:

1. **Verify concavity of `Sᵥₙ`** is in PhysLib (under some name) — needed for Holevo-bound proof. If not, derive it; tiny.
2. **Verify a usable DPI for `qMutualInfo`** under classical post-processing — needed for step #3. May need to be added.
3. **Add PhysLib as a Lake dependency** (deferred entry: `physlib-dependency.md`) and confirm `import QuantumInfo.Finite.Entropy.VonNeumann` works against our toolchain.
4. **Decide BB84 protocol's Lean module layout** — proposed: `AI4BB84.Protocol.{Basis, Prepare, Measure, Sift}`, `AI4BB84.Adversary.Collective`, `AI4BB84.Security.DevetakWinter`. Defer locking until after #1–#3.

## References

- `PROOF_LOG/physlib-coverage.md` — the inventory that justifies this choice
- `PROOF_LOG/survey-of-prior-work.md` — broader landscape
- `material/renner-thesis-qkd-security.pdf` — Devetak–Winter and de Finetti both discussed; ch. 6 for the asymptotic key-rate formula in the modern smooth-entropy framing
- Devetak & Winter, "Distillation of secret key and entanglement from quantum states," Proc. R. Soc. A 461 (2005) — the original key-rate theorem (not yet in `material/`; consider adding if we need to cite the original derivation)
- `material/SURVEY.md` — annotated bibliography (Holevo bound textbook proof referenced via the Lewis survey D1)
