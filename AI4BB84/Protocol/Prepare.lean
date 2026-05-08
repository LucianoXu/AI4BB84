import QuantumInfo.Finite.Qubit.Basic
import QuantumInfo.Finite.Unitary
import AI4BB84.Protocol.Basis

/-!
# Alice's BB84 preparation

For each round Alice samples a classical bit `b ∈ Bool` and a basis
`a : Basis`, and prepares the qubit state encoding `b` in basis `a`:

| basis | bit `false` | bit `true` |
|-------|-------------|-------------|
| `Z`   | `\|0⟩⟨0\|`    | `\|1⟩⟨1\|`    |
| `X`   | `\|+⟩⟨+\|`    | `\|−⟩⟨−\|`    |

The X-basis states are `H \|0⟩⟨0\| H†` and `H \|1⟩⟨1\| H†` — i.e., the Z-basis
preparation conjugated by the Hadamard. This is exactly the encoding
required for the Shor–Preskill / Devetak–Winter analyses.

We model preparation at the `MState`-level (density-matrix), which is what
all subsequent calculations (post-channel state, ensemble χ, …) need.
-/

open MState  -- enables the `U ◃ ρ` conjugation notation on mixed states
open Qubit   -- exposes `H`, the Hadamard unitary

namespace AI4BB84

/-- Convert a classical bit to an index in `Fin 2`. -/
@[reducible] def bitIdx (b : Bool) : Fin 2 := if b then 1 else 0

/-- The pure mixed state `|i⟩⟨i|` on a qubit, where `i = 0` if `b = false`
and `i = 1` if `b = true`. This is Alice's Z-basis encoding. -/
noncomputable def computationalState (b : Bool) : MState Qubit :=
  MState.pure (Ket.basis (bitIdx b))

/-- Alice's BB84 state preparation: encode bit `b` in basis `a`.

* `Z, false` ↦ `|0⟩⟨0|`
* `Z, true`  ↦ `|1⟩⟨1|`
* `X, false` ↦ `|+⟩⟨+| = H |0⟩⟨0| H†`
* `X, true`  ↦ `|−⟩⟨−| = H |1⟩⟨1| H†`
-/
noncomputable def prepare (a : Basis) (b : Bool) : MState Qubit :=
  match a with
  | .Z => computationalState b
  | .X => H ◃ computationalState b

@[simp] theorem prepare_Z (b : Bool) : prepare .Z b = computationalState b := rfl
@[simp] theorem prepare_X (b : Bool) : prepare .X b = H ◃ computationalState b := rfl

end AI4BB84
