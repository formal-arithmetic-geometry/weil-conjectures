/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.Algebra.Homology.HomTensorDegreewiseEquation

/-!
# Forward degreewise currying construction

Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1, Tag 0A90.
(blueprint: lem-sc-hom-tensor-degreewise-construction)
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
/-- Forward degreewise construction, without uniqueness or invertibility.
Source: Stacks Project, Tag 0A90, degreewise construction 
(blueprint: lem-sc-hom-tensor-degreewise-construction).

Proof: Expand the product projections in both Hom complexes. For each p and q,
evaluate the outer localized map on x and the inner map on y. These evaluations
are linear in x, y and the input section, and commute with restrictions. Descend
the balanced bilinear map through the presheaf tensor and its sheafification.
For fixed total degree, combine these maps by the coproduct universal property;
then combine the resulting maps into M by the Hom product universal property.
This constructs a sheaf morphism and gives the displayed pure-tensor equation.
No uniqueness or inverse assertion is used in this construction. -/
theorem homTensorDegreewise_construct (K L M : CochainComplex Mod ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ∃ a : (homComplex (R := R) K (homComplex (R := R) L M)).X n ⟶
      (homComplex (R := R)
        (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X n,
      HomTensorDegreewiseEquation R K L M n a := by sorry

end CategoryTheory
