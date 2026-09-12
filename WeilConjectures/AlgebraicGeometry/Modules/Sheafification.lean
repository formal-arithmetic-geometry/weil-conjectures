/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Monoidal

/-!
# Comparing the tensor product of sheaves of modules with the sectionwise tensor product

Let `R` be a sheaf of commutative rings on a site `(C, J)`. The tensor product of two sheaves of
modules over `R` is the sheafification of the sectionwise tensor product of the underlying
presheaves of modules, see `WeilConjectures/AlgebraicGeometry/Modules/Monoidal.lean`. In order to
identify the tensor product of two sheaves of modules with a third one, it is therefore enough to
produce a morphism from the sectionwise tensor product of the underlying presheaves of modules
which becomes an isomorphism after sheafification, i.e. which is locally bijective.

## Main definitions and results

- `SheafOfModules.sheafificationObjIso`: the sheafification of the underlying presheaf of modules
  of a sheaf of modules `F` is `F` itself.
- `SheafOfModules.tensorIsoOfW`: a morphism `P ⊗ Q ⟶ S` of presheaves of modules which becomes
  an isomorphism after sheafification identifies the tensor product of the sheafifications of `P`
  and `Q` with the sheafification of `S`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v₁ u₁ u

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

/-- The sheafification of the underlying presheaf of modules of a sheaf of modules `F` is `F`
itself; this is the counit of the sheafification adjunction. -/
noncomputable def sheafificationObjIso
    (F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) :
    (sheafification R).obj
      ((SheafOfModules.forget
        ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)).obj F) ≅ F :=
  asIso ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R).obj)).counit.app F)

variable {R}

/-- A morphism of presheaves of modules whose underlying morphism of presheaves of abelian groups
becomes an isomorphism after sheafification induces an isomorphism of the sheafifications. -/
theorem isIso_sheafification_map
    {P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat.{u})} (φ : P ⟶ Q)
    (hφ : J.W ((PresheafOfModules.toPresheaf
      (R.obj ⋙ forget₂ CommRingCat RingCat.{u})).map φ)) :
    IsIso ((sheafification R).map φ) :=
  Localization.inverts (sheafification R)
    (J.W.inverseImage (PresheafOfModules.toPresheaf _)) _ hφ

/-- A morphism `φ : P ⊗ Q ⟶ S` from the sectionwise tensor product of two presheaves of modules
which becomes an isomorphism after sheafification identifies the tensor product of the
sheafifications of `P` and `Q` with the sheafification of `S`. -/
noncomputable def tensorIsoOfW
    {P Q S : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat.{u})}
    {F G H : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)}
    (eF : (sheafification R).obj P ≅ F) (eG : (sheafification R).obj Q ≅ G)
    (eH : (sheafification R).obj S ≅ H) (φ : P ⊗ Q ⟶ S)
    (hφ : J.W ((PresheafOfModules.toPresheaf
      (R.obj ⋙ forget₂ CommRingCat RingCat.{u})).map φ)) :
    F ⊗ G ≅ H :=
  have := isIso_sheafification_map φ hφ
  tensorIso eF.symm eG.symm ≪≫ Functor.Monoidal.μIso (sheafification R) P Q ≪≫
    asIso ((sheafification R).map φ) ≪≫ eH

end SheafOfModules
