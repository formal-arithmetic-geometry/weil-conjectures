/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Algebra.Homology.HomTensorDegreewiseEquation

/-!
# Reverse degreewise currying construction

Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1, Tag 0A90.
(blueprint: lem-sc-hom-tensor-reverse-construction)
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
/-- Reverse currying construction with its evaluation equation, without inverse laws.
Source: Stacks Project, Cohomology on Sites, Tag 0A90, inverse construction;
Modules on Sites, Tag 03EO and Section 03EK.
(blueprint: lem-sc-hom-tensor-reverse-construction).

Proof: Restrict a localized map out of the total tensor term to each (p,q)
summand. Pull it back along the presheaf-to-sheaf tensor map. Curry the resulting
bilinear map, first in y and then in x, on the localized site. These maps commute
with further restriction because restriction of a bilinear map commutes with
currying. Assemble the q components using the product cone of the inner Hom
complex, then assemble the p components using the outer Hom product cone.
Linearity in the initial localized map and restriction compatibility give a
morphism of sheaves b. Evaluating the assembled components at x and y recovers
the original bilinear map by the tensor-Hom evaluation identity. This proves
the displayed equation. There are no inverse identities in this construction,
no boundedness assumptions, and no assumption of global pure-tensor generation. -/
theorem homTensorDegreewise_reverse_construct (K L M : CochainComplex Mod ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ∃ b : (homComplex (R := R)
        (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X n ⟶
      (homComplex (R := R) K (homComplex (R := R) L M)).X n,
      ∀ (p q : ℤ) (U : Cᵒᵖ)
    (s : (homComplex (R := R)
      (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X n |>.val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (K.X p).val.obj (op W.unop.left))
    (y : (L.X q).val.obj (op W.unop.left)),
    let φ := ((homTensorCurryProjection R
      (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M
      n (p + q) (p + q + n) rfl).val.app U).hom s
    let ψ := ((homTensorCurryProjection R K (homComplex (R := R) L M)
      n p (p + n) rfl).val.app U).hom ((b.val.app U).hom s)
    let χ := ((homTensorCurryProjection R L M (p + n) q (p + q + n)
      (by omega)).val.app (op W.unop.left)).hom ((ψ.app W).hom x)
    (φ.app W).hom
      (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
        p q (p + q) rfl).val.app (op W.unop.left)).hom
        (((homTensorCurrySectionMap R (K.X p) (L.X q)).app (op W.unop.left)).hom
          (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))) =
      (χ.app (op (Over.mk (𝟙 W.unop.left)))).hom y
 := by sorry

end CategoryTheory
