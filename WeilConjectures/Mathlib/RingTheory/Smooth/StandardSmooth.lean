/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Polynomial algebras are standard smooth

The polynomial algebra `MvPolynomial ι R` has a submersive presentation with variables `ι` and
no relations, so it is standard smooth of relative dimension `Nat.card ι` over `R` for finite
`ι`.

## Main definitions

- `Algebra.Presentation.mvPolynomial`: the presentation of `MvPolynomial ι R` with variables
  `ι` and no relations.
- `Algebra.SubmersivePresentation.mvPolynomial`: the same presentation, as a submersive
  presentation.

## Main results

- `Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial`: `MvPolynomial ι R` is standard
  smooth of relative dimension `Nat.card ι` over `R`, for finite `ι`.
-/

@[expose] public section

open MvPolynomial

namespace Algebra

variable (R : Type*) [CommRing R] (ι : Type*)

/-- The presentation of the polynomial algebra `MvPolynomial ι R` with variables `ι` and no
relations. -/
noncomputable def Presentation.mvPolynomial :
    Presentation R (MvPolynomial ι R) ι PEmpty.{1} where
  __ := Generators.mvPolynomial R ι
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    rw [Generators.ker_mvPolynomial]
    simp

/-- The presentation of `MvPolynomial ι R` with variables `ι` and no relations has
dimension `Nat.card ι`. -/
@[simp]
lemma Presentation.mvPolynomial_dimension :
    (Presentation.mvPolynomial R ι).dimension = Nat.card ι := by
  simp [Presentation.dimension]

/-- The submersive presentation of the polynomial algebra `MvPolynomial ι R` with variables `ι`
and no relations. -/
noncomputable def SubmersivePresentation.mvPolynomial :
    SubmersivePresentation R (MvPolynomial ι R) ι PEmpty.{1} where
  toPresentation := Presentation.mvPolynomial R ι
  map := PEmpty.elim
  map_inj a := a.elim
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, RingHom.map_det,
      Matrix.det_isEmpty]
    exact isUnit_one

/-- The polynomial algebra `MvPolynomial ι R` in finitely many variables is standard smooth of
relative dimension `Nat.card ι` over `R`. -/
instance IsStandardSmoothOfRelativeDimension.mvPolynomial [Finite ι] :
    IsStandardSmoothOfRelativeDimension (Nat.card ι) R (MvPolynomial ι R) :=
  (SubmersivePresentation.mvPolynomial R ι).isStandardSmoothOfRelativeDimension
    (Presentation.mvPolynomial_dimension R ι)

end Algebra
