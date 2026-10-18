/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalizationData

/-!
# Termwise projections for the compactification graph

Source: SGA 4 XVII 6.2.11; Stacks Project Tags 03S6 and 07A7.
-/

@[expose] public section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar lowerStar etaleLowerShriek openImmersionLowerShriek
attribute [local irreducible] compactSupportComparisonOnHomotopy

private theorem transpose_comparison
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj' : L' ⊣ R')
    (Q : C ⥤ C') (Q' : D ⥤ D')
    (α : Q ⋙ L' ⟶ L ⋙ Q') (β : R ⋙ Q ⟶ Q' ⋙ R')
    (hε : ∀ Y, L'.map (β.app Y) ≫ adj'.counit.app (Q'.obj Y) =
      α.app (R.obj Y) ≫ Q'.map (adj.counit.app Y))
    {M : C} {N : D} {Z : C'} {W : D'}
    (a : M ⟶ R.obj N) (e : Z ⟶ Q.obj M) (j : Q'.obj N ⟶ W) :
    L'.map (e ≫ Q.map a ≫ β.app N ≫ R'.map j) ≫ adj'.counit.app W =
      L'.map e ≫ α.app M ≫ Q'.map (L.map a ≫ adj.counit.app N) ≫ j := by
  simp only [Functor.map_comp, Category.assoc]
  have hj := adj'.counit.naturality j
  dsimp only [Functor.comp_map, Functor.id_map] at hj
  rw [hj, reassoc_of% (hε N)]
  have hn := α.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]

private theorem transpose_comparison_exact
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj' : L' ⊣ R')
    (Q : C ⥤ C') (Q' : D ⥤ D')
    (α : Q ⋙ L' ⟶ L ⋙ Q') (β : R ⋙ Q ⟶ Q' ⋙ R')
    (hε : ∀ Y, L'.map (β.app Y) ≫ adj'.counit.app (Q'.obj Y) =
      α.app (R.obj Y) ≫ Q'.map (adj.counit.app Y))
    (P : C' ⥤ D') (μ : L' ⟶ P) (φ : Q ⋙ P ⟶ L ⋙ Q')
    (hα : ∀ M, μ.app (Q.obj M) ≫ φ.app M = α.app M)
    {M : C} {N : D} {Z : C'} {W : D'}
    (a : M ⟶ R.obj N) (e : Z ⟶ Q.obj M) (j : Q'.obj N ⟶ W) :
    L'.map (e ≫ Q.map a ≫ β.app N ≫ R'.map j) ≫ adj'.counit.app W =
      μ.app Z ≫ P.map e ≫ φ.app M ≫ Q'.map (L.map a ≫ adj.counit.app N) ≫ j := by
  rw [transpose_comparison adj adj' Q Q' α β hε, ← hα M]
  simp only [← Category.assoc]
  rw [μ.naturality]

/-- Transpose a transformation through an adjunction by its component counit.
Source: Stacks Project Tag 07A7.
(blueprint: lem-a2-compact-support-derived-projection). -/
@[irreducible]
noncomputable def graphProjectionTranspose
    {B C D : Type*} [Category B] [Category C] [Category D]
    {P : C ⥤ D} {R : D ⥤ C} (adj : P ⊣ R)
    {E : B ⥤ C} {J : B ⥤ D} (a : E ⟶ J ⋙ R) : E ⋙ P ⟶ J :=
  Functor.whiskerRight a P ≫ Functor.whiskerLeft J adj.counit

/-- The transpose formula, with no structural identity maps left to cancel.
Source: Stacks Project Tag 07A7.
(blueprint: lem-a2-compact-support-derived-projection). -/
theorem graphProjectionTranspose_app
    {B C D : Type*} [Category B] [Category C] [Category D]
    {P : C ⥤ D} {R : D ⥤ C} (adj : P ⊣ R)
    {E : B ⥤ C} {J : B ⥤ D} (a : E ⟶ J ⋙ R) (M : B) :
    (graphProjectionTranspose adj a).app M =
      P.map (a.app M) ≫ adj.counit.app (J.obj M) := by
  simp only [graphProjectionTranspose, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]

/-- Descend a projection with its specified source and target factorization isomorphisms.
Source: Stacks Project Tag 04VG.
(blueprint: lem-a2-compact-support-derived-projection). -/
@[irreducible]
noncomputable def graphProjectionLocalizationDesc
    {B B' C C' D D' : Type*}
    [Category B] [Category B'] [Category C] [Category C'] [Category D] [Category D']
    (QB : B ⥤ B') (W : MorphismProperty B) [QB.IsLocalization W]
    {Q : C ⥤ C'} {Q' : D ⥤ D'}
    {E : B ⥤ C} {ED : B' ⥤ C'} {J : B ⥤ D} {JD : B' ⥤ D'}
    {P : C ⥤ D} {PD : C' ⥤ D'}
    (e : QB ⋙ ED ≅ E ⋙ Q) (j : QB ⋙ JD ≅ J ⋙ Q')
    (p : Q ⋙ PD ≅ P ⋙ Q') (δ : E ⋙ P ⟶ J) : ED ⋙ PD ⟶ JD :=
  normalizationLocalizationDesc QB W
    (Functor.whiskerRight e.hom PD ≫ Functor.whiskerLeft E p.hom ≫
      Functor.whiskerRight δ Q' ≫ j.inv)

/-- Component formula for a descended projection.
Source: Stacks Project Tag 04VG.
(blueprint: lem-a2-compact-support-derived-projection). -/
theorem graphProjectionLocalizationDesc_app
    {B B' C C' D D' : Type*}
    [Category B] [Category B'] [Category C] [Category C'] [Category D] [Category D']
    (QB : B ⥤ B') (W : MorphismProperty B) [QB.IsLocalization W]
    {Q : C ⥤ C'} {Q' : D ⥤ D'}
    {E : B ⥤ C} {ED : B' ⥤ C'} {J : B ⥤ D} {JD : B' ⥤ D'}
    {P : C ⥤ D} {PD : C' ⥤ D'}
    (e : QB ⋙ ED ≅ E ⋙ Q) (j : QB ⋙ JD ≅ J ⋙ Q')
    (p : Q ⋙ PD ≅ P ⋙ Q') (δ : E ⋙ P ⟶ J) (M : B) :
    (graphProjectionLocalizationDesc QB W e j p δ).app (QB.obj M) =
      PD.map (e.hom.app M) ≫ p.hom.app (E.obj M) ≫
        Q'.map (δ.app M) ≫ j.inv.app M := by
  rw [graphProjectionLocalizationDesc, normalizationLocalizationDesc_app]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]

/-- The graph projection on homotopy categories, before deriving the proper direct image.
It applies the sheaf graph map termwise and then the inverse-image/direct-image counit.
Source: SGA 4 XVII 6.2.11; Stacks Project Tag 0F4L.
(blueprint: lem-a2-compact-support-derived-projection). -/
@[irreducible]
noncomputable def compactSupportGraphProjectionOnHomotopy
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (c : Compactification f)
    (a : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapHomotopyCategory (.up ℤ) ⋙
        (upperStar (ModuleCat.{u + 1} A) c.g).mapHomotopyCategory (.up ℤ) ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapHomotopyCategory (.up ℤ) :=
  graphProjectionTranspose
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g).mapHomotopyCategory (.up ℤ))
    (a.mapHomotopyCategory (.up ℤ) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv)

/-- Descend the termwise graph projection along the homotopy localization.
This construction uses no total derived direct image.
Source: Stacks Project Tags 04VG and 0F4L.
(blueprint: lem-a2-compact-support-derived-projection). -/
@[irreducible]
noncomputable def compactSupportGraphDerivedProjection
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (c : Compactification f)
    (a : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) c.g).mapDerivedCategory ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory :=
  graphProjectionLocalizationDesc DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ))
    (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategoryFactorsh
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryFactorsh
    (upperStar (ModuleCat.{u + 1} A) c.g).mapDerivedCategoryFactorsh
    (compactSupportGraphProjectionOnHomotopy A f c a)

/-- The specified total-derived graph comparison transposes to the termwise graph projection.
Source: SGA 4 XVII 6.2.11; Stacks Project Tags 04VG and 07A7.
(blueprint: lem-a2-compact-support-derived-projection).

Proof: precompose with the homotopy localization, where the comparison is its defining
termwise map followed by the right-derived unit. Naturality moves the exact-extension
comparison past the derived counit. The defining counit equation of the derived adjunction
replaces the right-derived unit followed by that counit with the homotopy counit. The
remaining factors are precisely the displayed termwise projection. Full faithfulness of
precomposition with the localization gives the equality. -/
theorem compactSupportDerivedComparison_leftDerived_transpose
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (c : Compactification f)
    (a : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor.map
        ((compactSupportDerivedComparison A f c a).app K) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g).counit.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K) =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) c.g).hom.app
          ((etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory.obj K) ≫
        (compactSupportGraphDerivedProjection A f c a).app K := by
  let E := etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance
  let J := openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i
  let P := upperStar (ModuleCat.{u + 1} A) c.g
  let R := lowerStar (ModuleCat.{u + 1} A) c.g
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g
  let adjD := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g
  let τ : E.mapDerivedCategory ⋙ P.leftDerivedFunctor ⟶ J.mapDerivedCategory :=
    Functor.whiskerRight (compactSupportDerivedComparison A f c a) P.leftDerivedFunctor ≫
      Functor.whiskerLeft J.mapDerivedCategory adjD.counit
  have h : τ =
      Functor.whiskerLeft E.mapDerivedCategory P.leftDerivedFunctorIsoMapDerivedCategory.hom ≫
        compactSupportGraphDerivedProjection A f c a := by
    apply Localization.natTrans_ext DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ))
    intro M
    have hε (Y : HomotopyCategory
        (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
        P.leftDerivedFunctor.map (R.rightDerivedFunctorUnit.app Y) ≫
            adjD.counit.app (DerivedCategory.Qh.obj Y) =
          P.leftDerivedFunctorCounit.app ((R.mapHomotopyCategory (.up ℤ)).obj Y) ≫
            DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app Y) :=
      (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
        (HomotopyCategory.quasiIso
          (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ))
        P.leftDerivedFunctorCounit R.rightDerivedFunctorUnit Y
    have hα (Y : HomotopyCategory
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
        P.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Qh.obj Y) ≫
            P.mapDerivedCategoryFactorsh.hom.app Y = P.leftDerivedFunctorCounit.app Y :=
      congr_app P.leftDerivedFunctorIsoMapDerivedCategory_hom_fac Y
    have ht := transpose_comparison_exact (adj.mapHomotopyCategory (.up ℤ)) adjD
      DerivedCategory.Qh DerivedCategory.Qh P.leftDerivedFunctorCounit
      R.rightDerivedFunctorUnit hε P.mapDerivedCategory
      P.leftDerivedFunctorIsoMapDerivedCategory.hom P.mapDerivedCategoryFactorsh.hom hα
      ((a.mapHomotopyCategory (.up ℤ)).app M ≫
        (Functor.mapHomotopyCategoryCompIso (F := J) (G := R)
          (Iso.refl (J ⋙ R)) (.up ℤ)).inv.app M)
      (E.mapDerivedCategoryFactorsh.hom.app M) (J.mapDerivedCategoryFactorsh.inv.app M)
    dsimp only [τ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.rightUnitor_hom_app]
    rw [compactSupportDerivedComparison_app, compactSupportGraphDerivedProjection,
      graphProjectionLocalizationDesc_app]
    dsimp only [E, J, P, R, adj, adjD] at ht ⊢
    simp only [compactSupportComparisonOnHomotopy, compactSupportGraphProjectionOnHomotopy,
      graphProjectionTranspose_app, NatTrans.comp_app,
      Functor.map_comp, Functor.comp_obj, Functor.id_obj, Category.assoc] at ht ⊢
    exact ht
  simpa only [τ, E, J, P, adjD, leftDerivedUpperStarIsoMapDerivedCategory,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id] using congr_app h K

end AlgebraicGeometry.Etale
