/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Reduction
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange

/-! # Universal principal coefficient changes

The fixed scalar extension is constructed from K-flat resolutions and the scalar
adjunction. Its unit is a universal derived base change. No adic witness model is used.
Source: the universal-pair argument of lem-fix-operation-reduction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Functor
attribute [local instance 2000] CommRing.toRing

namespace AlgebraicGeometry
namespace Etale
set_option hygiene false in
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

end Etale

namespace PrincipalCoefficient

/-- The fixed derived extension on an arbitrary coefficient site. -/
abbrev extension {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :=
  Sheaf.fixedCoefficientDerivedScalarExtension J φ

/-- The adjunction used by the fixed derived scalar extension. -/
def scalarAdjunction {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    extension J φ ⊣ Sheaf.derivedRestrictScalars J φ :=
  letI := Sheaf.fixedCoefficientDerivedRestriction_isRightAdjoint J φ
  Adjunction.ofIsRightAdjoint _

/-- The scalar adjunction unit is a universal derived base change.
Proof: its factorization map is the adjunction hom-equivalence.
Source: lem-fix-operation-reduction universal-pair argument
(blueprint: lem-principal-coefficient-universal-transport). -/
lemma coefficientUnit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {S : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    (ad : S ⊣ Sheaf.derivedRestrictScalars J φ)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) :
    Sheaf.IsDerivedBaseChange (ad.unit.app K) := by
  intro N
  convert (ad.homEquiv K N).bijective using 1
  funext g
  exact (ad.homEquiv_unit K N g).symm

/-- Two universal derived base changes of one object have isomorphic targets.
Proof: the adjunction inverse image of the specified arrow is invertible by
uniqueness of universal arrows.
Source: lem-fix-operation-reduction universal-pair argument
(blueprint: lem-principal-coefficient-universal-transport). -/
lemma coefficientIso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {S : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    (ad : S ⊣ Sheaf.derivedRestrictScalars J φ)
    {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))}
    {K' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    {η : K ⟶ (Sheaf.derivedRestrictScalars J φ).obj K'}
    (hη : Sheaf.IsDerivedBaseChange η) : Nonempty (S.obj K ≅ K') := by
  have := (coefficientUnit J φ ad K).isIso hη ((ad.homEquiv K K').symm η)
    ((ad.homEquiv_unit K K' _).symm.trans ((ad.homEquiv K K').apply_symm_apply η))
  exact ⟨asIso ((ad.homEquiv K K').symm η)⟩

/-- Transport a universal scalar unit to an isomorphic target.
Proof: compose the unit with restriction of the target isomorphism.
Source: lem-fix-operation-reduction universal-pair argument
(blueprint: lem-principal-coefficient-universal-transport). -/
lemma coefficientFromIso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {S : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    (ad : S ⊣ Sheaf.derivedRestrictScalars J φ)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)))
    (N : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))
    (e : Nonempty (S.obj K ≅ N)) :
    ∃ θ : K ⟶ (Sheaf.derivedRestrictScalars J φ).obj N,
      Sheaf.IsDerivedBaseChange θ := by
  obtain ⟨e⟩ := e
  exact ⟨ad.unit.app K ≫ (Sheaf.derivedRestrictScalars J φ).map e.hom,
    (coefficientUnit J φ ad K).comp_map_iso e⟩

/-- Naturality identifies components at isomorphic inputs as arrows.
Proof: use the functor images of the input isomorphism as the two sides.
Source: lem-fix-operation-reduction universal-pair argument
(blueprint: lem-principal-coefficient-universal-transport). -/
@[irreducible] noncomputable def coefficientArrowUnary
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (a : F ⟶ G) {K L : C} (e : K ≅ L) :
    Arrow.mk (a.app K) ≅ Arrow.mk (a.app L) :=
  Arrow.isoMk (F.mapIso e) (G.mapIso e) (a.naturality e.hom)

/-- Two-variable naturality identifies components as arrows.
Proof: paste the naturality squares in the two variables.
Source: lem-fix-operation-reduction universal-pair argument
(blueprint: lem-principal-coefficient-universal-transport). -/
@[irreducible] noncomputable def coefficientArrowBinary
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D ⥤ E} (a : F ⟶ G)
    {K K' : C} {L L' : D} (eK : K ≅ K') (eL : L ≅ L') :
    Arrow.mk ((a.app K).app L) ≅ Arrow.mk ((a.app K').app L') :=
  Arrow.isoMk ((F.mapIso eK).app L ≪≫ (F.obj K').mapIso eL)
    ((G.mapIso eK).app L ≪≫ (G.obj K').mapIso eL) (by
      have h₁ := congr_app (a.naturality eK.hom) L
      have h₂ := (a.app K').naturality eL.hom
      simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Arrow.mk_hom,
        Category.assoc]
      change (F.map eK.hom).app L ≫ (F.obj K').map eL.hom ≫
          (a.app K').app L' =
        (a.app K).app L ≫ (G.map eK.hom).app L ≫ (G.obj K').map eL.hom
      dsimp only [NatTrans.comp_app] at h₁
      rw [h₂, ← Category.assoc, h₁, Category.assoc])





/-- Transport a fixed unary coefficient comparison to any universal target.
Proof: compose the fixed comparison with the image of the uniquely determined
target isomorphism, and transport the scalar unit.
Source: lem-fix-operation-reduction universal-pair argument
(blueprint: lem-principal-coefficient-universal-transport). -/
lemma coefficientUnary
    {C₁ C₂ : Type (u + 1)} [Category.{u} C₁] [Category.{u} C₂]
    [EssentiallySmall.{u + 1} C₁] [EssentiallySmall.{u + 1} C₂]
    (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {S₁ : DerivedCategory (Sheaf J₁ (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J₁ (ModuleCat.{u + 1} B))}
    {S₂ : DerivedCategory (Sheaf J₂ (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J₂ (ModuleCat.{u + 1} B))}
    (ad₁ : S₁ ⊣ Sheaf.derivedRestrictScalars J₁ φ)
    (ad₂ : S₂ ⊣ Sheaf.derivedRestrictScalars J₂ φ)
    (F : DerivedCategory (Sheaf J₁ (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J₂ (ModuleCat.{u + 1} A)))
    (G : DerivedCategory (Sheaf J₁ (ModuleCat.{u + 1} B)) ⥤
      DerivedCategory (Sheaf J₂ (ModuleCat.{u + 1} B)))
    (K : DerivedCategory (Sheaf J₁ (ModuleCat.{u + 1} A)))
    (N : DerivedCategory (Sheaf J₁ (ModuleCat.{u + 1} B)))
    (η : K ⟶ (Sheaf.derivedRestrictScalars J₁ φ).obj N)
    (hη : Sheaf.IsDerivedBaseChange η)
    (e : Nonempty (S₂.obj (F.obj K) ≅ G.obj (S₁.obj K))) :
    ∃ θ : F.obj K ⟶ (Sheaf.derivedRestrictScalars J₂ φ).obj (G.obj N),
      Sheaf.IsDerivedBaseChange θ := by
  obtain ⟨e⟩ := e
  obtain ⟨eK⟩ := coefficientIso J₁ φ ad₁ (η := η) hη
  exact coefficientFromIso J₂ φ ad₂ _ _ ⟨e ≪≫ G.mapIso eK⟩

end PrincipalCoefficient
end AlgebraicGeometry
