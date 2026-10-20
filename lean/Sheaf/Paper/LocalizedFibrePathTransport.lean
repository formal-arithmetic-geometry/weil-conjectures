/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module

public import Mathlib.CategoryTheory.Localization.Construction

/-!
# Descent of fibre paths through localization

Source: Weil II (1.1.1) d), localization of coefficient pairs.
(blueprint: new-e5-localized-fibre-path-transport).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Localization.Construction

universe v u w z
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {A : Type w} [Category.{z} A]
  {F G H : C ⥤ A} (hF : W.IsInvertedBy F) (hG : W.IsInvertedBy G)

/-- Localization extends a natural fibre isomorphism without changing its components.
Source: Weil II (1.1.1) d).
(blueprint: new-e5-localized-fibre-path-transport). -/
noncomputable def liftFiberNatIso (e : F ≅ G) : lift F hF ≅ lift G hG :=
  (WhiskeringLeftEquivalence.inverse W A).mapIso
    (ObjectProperty.isoMk _ e : (⟨F, hF⟩ : W.FunctorsInverting A) ≅ ⟨G, hG⟩)

/-- The component of the descended path on a coefficient pair.
Source: Weil II (1.1.1) d).
(blueprint: new-e5-localized-fibre-path-transport).
Proof: the inverse of the localization equivalence extends a natural transformation;
its component on the image of an object is the original component. -/
theorem liftFiberNatIso_hom_app (e : F ≅ G) (X : C) :
    (liftFiberNatIso W hF hG e).hom.app (W.Q.obj X) = e.hom.app X := by
  simp only [liftFiberNatIso, Functor.mapIso_hom,
    WhiskeringLeftEquivalence.inverse, natTransExtension_app,
    NatTransExtension.app_eq, NatTrans.comp_app, eqToHom_app, eqToHom_refl,
    Category.id_comp, Category.comp_id, ObjectProperty.isoMk]
  rfl

end CategoryTheory.Localization.Construction
