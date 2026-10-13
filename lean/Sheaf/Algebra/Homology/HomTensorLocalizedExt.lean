/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.Algebra.Homology.HomTensorDegreewise

/-!
# Localized pure-tensor extensionality

Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1, Tag 0A90.
(blueprint: lem-sc-hom-tensor-localized-ext)
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
/-- Maps to the internal Hom out of a total tensor are determined on localized pure tensors.
Source: Stacks Project, Cohomology on Sites, Tag 0A90, degreewise construction;
Modules on Sites, Section 03EK, tensor product universal property.
(blueprint: lem-sc-hom-tensor-localized-ext)

Proof: Fix a source section over U and regard its images as morphisms on the
localized site over U. Restrict each such morphism to every total tensor summand.
The tensor summand is the sheafification of the presheaf tensor. Equality on
pure tensors gives equality on the presheaf tensor by its bilinear universal
property. The sheafification adjunction gives equality on the sheaf tensor,
including after localization, since sheafification commutes with restriction
to a localized site. The coproduct universal property gives equality on the
total term. Finally extensionality of internal-Hom sections, linear maps and
sheaf morphisms gives equality of the two original morphisms. -/
theorem homTensorLocalized_ext
    (K L : CochainComplex Mod ℤ) (N X : Mod) (p : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ∀ (a b : X ⟶ SheafOfModules.homObj (R := R)
      ((CochainComplex.mapBifunctor K L (curriedTensor Mod)).X p) N),
    (∀ (U : Cᵒᵖ) (s : X.val.obj U) (W : (Over U.unop)ᵒᵖ)
      (i j : ℤ) (hij : i + j = p)
      (x : (K.X i).val.obj (op W.unop.left))
      (y : (L.X j).val.obj (op W.unop.left)),
      (((a.val.app U).hom s).app W).hom
        (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
          i j p hij).val.app (op W.unop.left)).hom
          (((homTensorSectionMap R (K.X i) (L.X j)).app (op W.unop.left)).hom
            (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))) =
      (((b.val.app U).hom s).app W).hom
        (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
          i j p hij).val.app (op W.unop.left)).hom
          (((homTensorSectionMap R (K.X i) (L.X j)).app (op W.unop.left)).hom
            (x ⊗ₜ[R.obj.obj (op W.unop.left)] y)))) → a = b := by sorry

end CategoryTheory
