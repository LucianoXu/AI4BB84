import Mathlib.Data.Fintype.Basic

/-!
# BB84 basis choice

In BB84 each party (Alice, Bob) independently chooses a *basis* for each
transmitted qubit:

* **Z** — the computational (rectilinear) basis `{|0⟩, |1⟩}`
* **X** — the Hadamard (diagonal) basis `{|+⟩, |−⟩}`

Sifting later discards rounds where the two parties' choices differ.

We model the basis as a small finite inductive type rather than as `Bool`,
to make the protocol code self-documenting at the cost of a few derived
instances. The choice of representation here is deliberately minimal — the
protocol model should not need anything more from a basis than equality,
enumeration, and a one-bit complement; all of which fall out of `deriving`.
-/

namespace AI4BB84

/-- The two BB84 bases: computational `Z` and Hadamard `X`. -/
inductive Basis : Type where
  /-- The computational (Z) basis `{|0⟩, |1⟩}`. -/
  | Z : Basis
  /-- The Hadamard (X) basis `{|+⟩, |−⟩}`. -/
  | X : Basis
  deriving DecidableEq, Repr, Inhabited

namespace Basis

instance : Fintype Basis where
  elems := {Z, X}
  complete := by intro b; cases b <;> decide

/-- The "other" basis (`Z ↔ X`). Useful for stating algebraic facts about the
Hadamard transform that swaps the two bases. -/
def flip : Basis → Basis
  | Z => X
  | X => Z

@[simp] theorem flip_Z : flip Z = X := rfl
@[simp] theorem flip_X : flip X = Z := rfl
@[simp] theorem flip_flip (b : Basis) : (flip b).flip = b := by cases b <;> rfl

end Basis

end AI4BB84
