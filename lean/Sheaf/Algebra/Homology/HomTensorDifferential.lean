/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.Algebra.Homology.HomTensorDegreewise

/-!
# Degreewise currying for the Hom-total-tensor comparison

Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1, Tag 0A90.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option synthInstance.maxSize 256 in
/-- Degreewise currying commutes with the Hom-complex differentials.
Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1 (Tag 0A90),
compatibility with differentials (blueprint: lem-sc-hom-tensor-differential).

Proof: Test the equality using the Hom product projections, restricting to
`K^p ⊗ L^q` in each total tensor term and evaluating on localized pure tensors.
Write `F(x ⊗ y) = f(x)(y)` by the defining equation of the degreewise map.
For consecutive degrees `n,m = n+1`, the iterated Hom differential evaluated
at `x,y` is `d_M(f(x)(y)) - (-1)^(p+n) f(x)(d_L y)
- (-1)^n f(d_K x)(y)`. The total tensor differential on the summand is
`d_K x ⊗ y + (-1)^p x ⊗ d_L y`. The Hom differential on the right is
`d_M F - (-1)^n F d_Tot`, so its evaluation gives the same three terms,
because `(-1)^(p+n) = (-1)^p (-1)^n`. Linearity and the tensor universal
property give equality before sheafification; the sheafification adjunction
and coproduct and product universal properties give the displayed equality.
For nonconsecutive degrees both differentials vanish by the complex shape.
Thus the claim uses the actual constructed maps and adds no invertibility
or naturality assertion. -/
theorem homTensorDegreewiseMap_comm (K L M : CochainComplex Mod ℤ) (n m : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    homTensorDegreewiseMap R K L M n ≫
        (homComplex (R := R)
          (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).d n m =
      (homComplex (R := R) K (homComplex (R := R) L M)).d n m ≫
        homTensorDegreewiseMap R K L M m := by sorry

end CategoryTheory
