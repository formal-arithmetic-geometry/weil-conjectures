module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-! # Clearing denominators in a residue-field minimal polynomial

Source: literature/stacks-project/algebra.tex, proof of Lemma Tag 00UD
(blueprint: lem-weil-pbc-etale-residue-polynomial-lift).
-/

/-- Clearing denominators in a residue-field minimal polynomial.

Source: Stacks Project, Tag 00UD, lines 39819--39835
(blueprint: lem-weil-pbc-etale-residue-polynomial-lift).
Proof: clear common denominators of the coefficients of the minimal polynomial,
then scale the primitive element and lift the resulting coefficients; see the
four steps recorded in the blueprint node.
-/
theorem residue_polynomial_lift
    (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime]
    (L : Type v) [Field L]
    [Algebra p.ResidueField L]
    [Module.Finite p.ResidueField L]
    (hsep : Algebra.IsSeparable p.ResidueField L)
    (α : L)
    (hgen : Algebra.adjoin p.ResidueField ({α} : Set L) = ⊤) :
    ∃ c : R, c ∉ p ∧
      ∃ f : Polynomial R, f.Monic ∧
        Polynomial.map (algebraMap R p.ResidueField) f =
          minpoly p.ResidueField
            ((algebraMap p.ResidueField L) (algebraMap R p.ResidueField c) * α) := by
  sorry

end AlgebraicGeometry
