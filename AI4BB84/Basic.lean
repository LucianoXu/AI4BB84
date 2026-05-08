import QuantumInfo.Finite.Entropy.VonNeumann
import QuantumInfo.Finite.Qubit.Basic

/-! Smoke test for the PhysLib (`QuantumInfo`) dependency.

If this file builds, the project can use `MState`, `Sᵥₙ`, `qMutualInfo`, and the
`Qubit` algebra from PhysLib. See `PROOF_LOG/physlib-dependency.md`. -/

example {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) : 0 ≤ Sᵥₙ ρ :=
  Sᵥₙ_nonneg ρ

example {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    (ρ : MState (dA × dB)) : qMutualInfo ρ.SWAP = qMutualInfo ρ :=
  qMutualInfo_symm ρ
