/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Algebra.Homology.RegularScalarQuotientNotation

/-! # Normalized tensor comparison for power quotients

Source: blueprint sk-lem-sp-tower, first proof paragraph; Stacks Project, Tags 03EK and 06YN.
(blueprint: lem-sp-regular-scalar-quotient-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.RegularScalarQuotient

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J CommRingCat.{r}]
  (R : Sheaf J CommRingCat.{r}) (t : (unit R).sections)

/-- Tensoring a principal Koszul complex with a quotient in degree zero gives
the scalar cone over that quotient, with the two coordinate normalizations.
This calculation needs neither regularity nor an inequality between the indices.

Proof: the first tensor factor is concentrated in degree zero. Thus the total
complex has only the summands (0,-1) and (0,0). On each summand the right unitor
identifies Q_n tensor R with Q_n, by x tensor r ↦ r*x, with inverse x ↦ x tensor 1.
The total differential has sign (-1)^0=1 and becomes multiplication by the image
of t^(m+1). Restriction of scalars preserves the two cone summands and their
inclusions; it carries this differential to the same scalar multiplication.
These termwise maps therefore define a chain isomorphism. Their formulas on
the two inclusions give the required equations. Zero terms and zero quotient
rings cause no exception.
Source: Stacks Project, Tags 03EK and 06YN.
(blueprint: lem-sp-regular-scalar-quotient-tensor-comparison). -/
theorem regularScalarQuotient_tensorComparison (n m : ℕ) :
    ∃ e : tensor R t n m ≅ restrictedP R t n m,
      tensorIn R t n m (-1) (koszulLeft R t m) ≫ e.hom.f (-1) =
        (res (projection R t n)).map
          (leftIn (B R t n) (scalarImage R t (projection R t n))
            (unit (B R t n)) (m + 1)) ∧
      tensorIn R t n m 0 (koszulRight R t m) ≫ e.hom.f 0 =
        (res (projection R t n)).map
          (rightIn (B R t n) (scalarImage R t (projection R t n))
            (unit (B R t n)) (m + 1)) := by
  sorry

end CategoryTheory.RegularScalarQuotient
