-- tqft/tqft_skeleton.lean
import Mathlib.Tactic

/-!
# TQFT Obstructions Skeleton

We formalize the translation of arithmetic circuits into link diagrams
and the computation of their Jones polynomial as an invariant.
-/

variable (n : ℕ)

/-- A placeholder type for link diagrams. -/
constant LinkDiagram : Type*

/-- Convert an arithmetic circuit to a link diagram. -/
constant circuitToLink : ArithCircuit → LinkDiagram

/-- Compute the Jones polynomial of a link diagram, represented as a string. -/
constant jonesPolynomial : LinkDiagram → String

/-- Obstruction: Jones polynomial differs for Permanent vs Determinant circuits. -/
theorem perm_jones_ne_det (n : ℕ) :
  jonesPolynomial (circuitToLink (C_mu_n n)) ≠ 
  jonesPolynomial (circuitToLink (C_mu_n_det n)) := by
  -- Sketch: empirical for n=3, theoretical extension to general n
  sorry
