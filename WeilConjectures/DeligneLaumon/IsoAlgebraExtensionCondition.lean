/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra

/-! # Extension of an isomorphism algebra through a functor

This is the existential extension condition with its comparison kept as a parameter.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory

namespace CategoryTheory

/-- Extension of an isomorphism algebra with an object property and a comparison witness.
Source: rem-dl-a1-conventions, lisse Weil extension condition.
(blueprint: def-dl-a1-iso-algebra-extension-condition).

Construction: quantify an isomorphism algebra on A satisfying P, a witness h of H,
and an isomorphism of its restricted carrier with F. The displayed equation requires
compatibility with their structure isomorphisms using c h. This proposition-valued
construction uses no choice and is valid even if H or either category is empty.
-/
def HasIsoAlgebraExtension
    {A : Type*} [Category A] {B : Type*} [Category B]
    (J : A ⥤ B) (PC : A ⥤ A) (PU : B ⥤ B)
    (H : Prop) (c : H → (J ⋙ PU ≅ PC ⋙ J)) (P : A → Prop)
    (F : CategoryTheory.Endofunctor.IsoAlgebra PU) : Prop :=
  ∃ K : CategoryTheory.Endofunctor.IsoAlgebra PC, P K.carrier ∧
    ∃ h : H, ∃ e : J.obj K.carrier ≅ F.carrier,
      PU.map e.hom ≫ F.str.hom = (c h).hom.app K.carrier ≫ J.map K.str.hom ≫ e.hom

end CategoryTheory
