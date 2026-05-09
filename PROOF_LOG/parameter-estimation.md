# Bar 2: parameter estimation + symmetric channel + entropic QBER bound

**Status:** 🟡 open / scoped — nothing implemented yet, this entry is the roadmap
**Last updated:** 2026-05-09

## Context

Bar 1 (Holevo bound) is closed. The placeholder `keyRate_nonneg` was at one
point planned as a direct consequence of the Holevo bound; in 2026-05-09 we
realized this is wrong and that the bottleneck is **modeling, not entropy
manipulation**. This entry captures what Bar 2 actually is.

## Why `keyRate_nonneg` is not a universal theorem

The universal claim

```
∀ (atk : CollectiveAttack E) (a : Basis), 0 ≤ keyRate atk a
```

is **false** in the current model. Concrete counterexample:

> *Measure-Z-resend-`|+⟩` attack at basis `Z`.* Eve measures the qubit in the
> Z basis (learning Alice's bit perfectly, `χ(A; E) = 1`), then forwards the
> fixed state `|+⟩` to Bob. Bob's Z-measurement outcome is independent of
> Alice's bit, so `I(A; B) = 0`. Hence `keyRate = 0 - 1 = -1`.

This attack does not threaten BB84 *as a protocol* because the protocol
reveals it during parameter estimation: the QBER is 50%, the protocol aborts,
and no key is produced. But the *inequality* `keyRate ≥ 0` is decidedly not
something we can prove for arbitrary `CollectiveAttack`. The Holevo bound
gives `I_acc(A; Λ(E)) ≤ χ(A; E)` for any POVM `Λ` Eve might apply — that's
a bound on Eve's *accessible* information, **not** a comparison between
`χ(A; E)` and `I(A; B)`.

## What Bar 2 must do

The honest fix is to **strengthen the model** so the abort-on-high-QBER step
is representable, then prove the standard symmetric-channel BB84 bound
`keyRate ≥ 1 − 2 h(δ)` (positive for `δ < ≈11%`).

## Five subtasks

Each is its own PR-sized piece of work; subsequent entries should split off
as they land.

### 1. `QBER` observable

Define

```lean
noncomputable def QBER (atk : CollectiveAttack E) (a : Basis) : ℝ
```

as the probability (averaged over Alice's uniform bit and the resend channel)
that Bob's Z-basis measurement disagrees with Alice's bit. Concretely, in
basis `a`,

```
QBER atk a := ∑ b, (1/2) * Pr[ measureZ ((atk.attackedState a b).traceRight) ≠ b ]
```

This is a function of the attack only and must be `≤ 1/2`. The technical
content is computing the marginal-on-Bob probability under `MState.measure`.

### 2. Symmetric / passing-PE attack subclass

We will not (in Bar 2) try to prove security for *all* attacks that pass
parameter estimation. The standard textbook path is:

> By a symmetrization argument (Renner thesis ch. 6.5, or Shor–Preskill §3),
> any collective attack that passes parameter estimation can be replaced by
> a *symmetric* (Pauli-mixture) attack achieving the same I(A;B) but with
> at most the same `χ(A; E)`.

Bar 2 takes the symmetrized form **as a hypothesis**, not as a derived fact:

```lean
structure SymmetricAttack (E : Type*) [Fintype E] [DecidableEq E]
    extends CollectiveAttack E where
  -- Bob's marginal channel is depolarizing with QBER δ in both bases
  symmetric : ∀ a b, … (QBER-symmetric condition)
```

The "symmetrize-then-bound" lemma is deferred to a later milestone; recording
it here as a known gap.

### 3. Entropic bound `χ(A; E) ≤ h(QBER)` for symmetric attacks

The BB84 entropic uncertainty argument (or, equivalently, the Holevo-bound
calculation on the depolarizing channel's complementary channel) gives

```
χ(A; E) ≤ h(δ)    where δ = QBER
```

Tools needed:
* PhysLib's `Sᵥₙ` on a 2×2 mixture, reducible to `negMulLog` of eigenvalues.
* A binary-entropy function `h : ℝ → ℝ` (Mathlib has `Real.binEntropy` —
  verify availability).
* The complementary-channel calculation: writing Eve's reduced state given
  Alice's bit explicitly in the symmetric case and reading off `Sᵥₙ`.

### 4. `I(A; B) = 1 − h(QBER)`

For the symmetric depolarizing channel, Bob's measurement outcome equals
Alice's bit with probability `1 − δ` and disagrees with probability `δ`.
The classical mutual information is then `1 − h(δ)`, by direct calculation
on `holevoChi (bobEnsemble …)` (which is classical, so `holevoChi` collapses
to Shannon mutual information).

Tools: `Sᵥₙ_ofClassical` (PhysLib), and a classical-mutual-information
identity `I(X; Y) = H(Y) − H(Y|X)` for binary uniform `X`, which is a
direct calculation on `holevoChi` of the classicalized ensemble.

### 5. Assemble

```lean
theorem keyRate_symmetric_lower_bound
    (atk : SymmetricAttack E) (a : Basis) :
    keyRate atk.toCollectiveAttack a ≥ 1 - 2 * h (QBER atk.toCollectiveAttack a)
```

Combining steps 3 and 4 by `linarith`. The corollary

```
QBER < δ_threshold → 0 < keyRate
```

(with `δ_threshold ≈ 0.11` the unique root of `2 h(δ) = 1` on `[0, 1/2]`) is
the BB84 textbook security statement against symmetric collective attacks.

## What this does *not* cover

* Coherent attacks — needs a de Finetti reduction on top.
* Composability / trace-distance security — needs leftover hash lemma.
* Finite-key bounds — needs smooth min-entropy.
* The symmetrization step itself (used as hypothesis in #2 above).

These remain as recorded in `PROOF_LOG/proof-framework.md` § "Upgrade path".

## Why this ordering

Subtasks #1 and #2 are pure modeling — no entropic content, but every
subsequent step depends on having `QBER` and `SymmetricAttack` as types.
#3 is the analytically hardest step; #4 is mostly bookkeeping; #5 is
`linarith`. Doing them in order gives clear checkpoints.

## References

* `AI4BB84/Security/DevetakWinter.lean` — `keyRate`, `keyRate_nonneg_of_eve_le_bob`
  (placeholder, not a security claim)
* `AI4BB84/Adversary/Collective.lean` — `CollectiveAttack`, `attackedState`,
  `eveEnsemble`
* `AI4BB84/Information/HolevoBound.lean` — `holevoBound` (Bar 1, used in #3)
* `material/renner-thesis-qkd-security.pdf` ch. 6 — symmetric collective-attack
  security and the asymptotic key-rate calculation
* `material/shor-preskill-bb84-security.pdf` — original BB84 symmetric-channel
  rate `1 − 2h(δ)` derivation (different proof technique, same target rate)
* `PROOF_LOG/proof-framework.md` — v1 framework decision and upgrade path
