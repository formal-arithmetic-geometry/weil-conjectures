/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSheafificationSquare.CoefficientSheafificationMapForget
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement

/-! # A normalized scalar square for finite coefficient presentations

Compose scalar restriction on module presheaves with the sheafification square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.CoefficientSheafificationSquare
section CoefficientSquare
variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {B B' R S : Type (u + 1)} [CommRing B] [CommRing B'] [CommRing R] [CommRing S]
    (q : B →+* B') (b : R →+* B) (b' : S →+* B') (r : R →+* S)
    (h : b'.comp r = q.comp b)
    {T U : Sheaf J RingCat.{u + 1}} (a : T ⟶ U)
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶ T.obj)
    (β : (Functor.const Cᵒᵖ).obj (RingCat.of S) ⟶ U.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (ha : (Functor.const Cᵒᵖ).map (RingCat.ofHom r) ≫ β = α ≫ a.hom)

include h in
@[irreducible] def coefficientPresheafIso :
    sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
        coefficientPresheaf J b ≅ coefficientPresheaf J b' ⋙ rawRestriction r :=
  NatIso.ofComponents (fun F ↦ PresheafOfModules.isoMk
    (fun V ↦ (ModuleCat.restrictScalarsComp'App b q (q.comp b) rfl (F.obj.obj V)).symm ≪≫
      ModuleCat.restrictScalarsComp'App r b' (q.comp b) h.symm (F.obj.obj V))
    (by intros; ext x; rfl)) (by intros; ext V x; rfl)

include h ha in
@[irreducible] def coefficientScalarIso :
    sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
        (sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} b) ⋙
          coefficientRealization J α) ≅
      (sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} b') ⋙
        coefficientRealization J β) ⋙ SheafOfModules.restrictScalars a :=
  Functor.isoWhiskerRight (coefficientPresheafIso J q b b' r h)
      (PresheafOfModules.sheafification α) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (coefficientPresheaf J b') (rawIso J r a α β ha) ≪≫
    (Functor.associator _ _ _).symm

end CoefficientSquare
end AlgebraicGeometry.Scheme.CoefficientSheafificationSquare
