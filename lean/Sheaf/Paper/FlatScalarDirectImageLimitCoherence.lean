/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.CategoryTheory.FlatRingedDiagramRestriction
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
public import Sheaf.Paper.ExactProductFunctorStrictLimit
import Sheaf.CategoryTheory.FlatRestrictionExactLeftAdjoint
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Flat scalar restriction and the normalized direct-image/strict-limit comparison

Source: Stacks Project, Cohomology on Sites, Tag 0A07
(`lemma-Rf-commutes-with-Rlim`), common K-injective tower model and its scalar compatibility
(blueprint: lem-cbc-flat-scalar-direct-image-limit-coherence).

The transparent abbreviations below only name the existing module categories and functors.
All comparison isomorphisms in the theorem have explicit ordinary or derived-unit
normalizations. The conclusion concerns these very maps on the derived category of strict
inverse sequences, indexed by zero-based naturals (reindexing positive naturals by n + 1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048

universe u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.FlatScalarLimitCoherence

private theorem ordinary_square
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasLimitsOfShape ℕᵒᵖ A'] [HasLimitsOfShape ℕᵒᵖ B']
    (F : A ⥤ B) (G : A' ⥤ B') (r : A ⥤ A') (s : B ⥤ B')
    (d : F ⋙ s ≅ r ⋙ G) (T : ℕᵒᵖ ⥤ A) :
    s.map (limit.post T F) ≫ limit.post (T ⋙ F) s ≫
        lim.map (Functor.whiskerLeft T d.hom) =
      d.hom.app (limit T) ≫ G.map (limit.post T r) ≫ limit.post (T ⋙ r) G := by
  apply limit.hom_ext
  intro n
  simp only [Category.assoc, lim_map, limMap_π, limit.post_π_assoc, limit.post_π,
    ← Functor.map_comp_assoc]
  erw [limit.post_π, ← G.map_comp, limit.post_π]
  exact d.hom.naturality (limit.π T n)

private theorem derived_nat_ext
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A]
    {B : Type*} [Category B] {F G : DerivedCategory.{w} A ⥤ B}
    (a b : F ⟶ G)
    (h : ∀ (I : CochainComplex A ℤ), I.IsKInjective →
      a.app (DerivedCategory.Q.obj I) = b.app (DerivedCategory.Q.obj I)) : a = b := by
  apply NatTrans.ext
  funext M
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  apply (cancel_mono (G.map e.hom)).mp
  rw [← a.naturality, ← b.naturality, h I hI]

private theorem limit_kinjective
    {A : Type*} [Category A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive] :
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A).PreservesKInjectiveComplexes := by
  have : (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact Adjunction.preservesKInjectiveComplexes constLimAdj

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {H : GrothendieckTopology D}

/-- Reuse the existing abelian structure on small-site module sheaves with a compact
instance term in the comparison signature.
Source: Stacks 0A07 (blueprint: lem-cbc-flat-scalar-direct-image-limit-coherence). -/
instance (priority := 2500) moduleAbelian (R : Sheaf K RingCat.{u}) :
    Abelian (ringedSiteModules.{u} R) :=
  inferInstance

/-- Reuse the existing small limits of module sheaves, including tower limits.
Source: Stacks 0A07 (blueprint: lem-cbc-flat-scalar-direct-image-limit-coherence). -/
instance (priority := 2500) moduleLimits (R : Sheaf K RingCat.{u}) :
    HasLimitsOfSize.{u, u} (ringedSiteModules.{u} R) :=
  inferInstance

/-- The existing RU module category, with no change of encoding.
Source: Stacks 0A07 (blueprint: lem-cbc-flat-scalar-direct-image-limit-coherence). -/
abbrev RU (x : FlatRingedDiagramInput K H) :=
  ringedSiteModules.{u} ((sheafCompose H (forget₂ CommRingCat RingCat)).obj x.RU)

/-- The existing SU module category, with no change of encoding.
Source: Stacks 0A07 (blueprint: lem-cbc-flat-scalar-direct-image-limit-coherence). -/
abbrev SU (x : FlatRingedDiagramInput K H) :=
  ringedSiteModules.{u} ((sheafCompose H (forget₂ CommRingCat RingCat)).obj x.SU)

/-- The existing RV module category, with no change of encoding.
Source: Stacks 0A07 (blueprint: lem-cbc-flat-scalar-direct-image-limit-coherence). -/
abbrev RV (x : FlatRingedDiagramInput K H) :=
  ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj x.RV)

/-- The existing SV module category, with no change of encoding.
Source: Stacks 0A07 (blueprint: lem-cbc-flat-scalar-direct-image-limit-coherence). -/
abbrev SV (x : FlatRingedDiagramInput K H) :=
  ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj x.SV)

/-- The actual sheaf restriction of scalars at U.
Source: Stacks 0A07 (blueprint: lem-cbc-flat-scalar-direct-image-limit-coherence). -/
abbrev rU (x : FlatRingedDiagramInput K H) : SU x ⥤ RU x :=
  SheafOfModules.restrictScalars.{u}
    ((sheafCompose H (forget₂ CommRingCat RingCat)).map x.aU)

/-- The actual sheaf restriction of scalars at V.
Source: Stacks 0A07 (blueprint: lem-cbc-flat-scalar-direct-image-limit-coherence). -/
abbrev rV (x : FlatRingedDiagramInput K H) : SV x ⥤ RV x :=
  SheafOfModules.restrictScalars.{u}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).map x.aV)

/-- Actual postcomposition on strict towers, allowing the natural numbers' own universe.
Source: Stacks 0A07 (blueprint: lem-cbc-flat-scalar-direct-image-limit-coherence). -/
abbrev rUt (x : FlatRingedDiagramInput K H) : (ℕᵒᵖ ⥤ SU x) ⥤ (ℕᵒᵖ ⥤ RU x) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (rU x)

/-- Actual postcomposition on strict towers, allowing the natural numbers' own universe.
Source: Stacks 0A07 (blueprint: lem-cbc-flat-scalar-direct-image-limit-coherence). -/
abbrev rVt (x : FlatRingedDiagramInput K H) : (ℕᵒᵖ ⥤ SV x) ⥤ (ℕᵒᵖ ⥤ RV x) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (rV x)

/-- Actual postcomposition on strict towers, allowing the natural numbers' own universe.
Source: Stacks 0A07 (blueprint: lem-cbc-flat-scalar-direct-image-limit-coherence). -/
abbrev FRt (x : FlatRingedDiagramInput K H) : (ℕᵒᵖ ⥤ RU x) ⥤ (ℕᵒᵖ ⥤ RV x) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (x.R.morphism.modules)

/-- Actual postcomposition on strict towers, allowing the natural numbers' own universe.
Source: Stacks 0A07 (blueprint: lem-cbc-flat-scalar-direct-image-limit-coherence). -/
abbrev FSt (x : FlatRingedDiagramInput K H) : (ℕᵒᵖ ⥤ SU x) ⥤ (ℕᵒᵖ ⥤ SV x) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (x.S.morphism.modules)

variable (x : FlatRingedDiagramInput K H)
  [HasDerivedCategory.{w} (RU x)] [HasDerivedCategory.{w} (SU x)]
  [HasDerivedCategory.{w} (RV x)] [HasDerivedCategory.{w} (SV x)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ RU x)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SU x)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ RV x)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SV x)]

set_option maxHeartbeats 1600000 in
-- Normalizing six long functor composites requires additional elaborator heartbeats.
/-- Flat scalar restriction preserves the specified direct-image/derived-limit comparison,
as an equality of natural maps on the derived category of strict towers.

`x` supplies the small sites, flat ring-sheaf maps and compatible invertible ring
identifications. The eight universal units specify the chosen K-injective derived direct
images and limits. The four q isomorphisms specify exact localization of scalar restriction.
The ordinary d0 is fixed on underlying sheaves; beta and e are fixed by limit projections.
The d, lambda and c equations are precisely their derived-unit normalizations. In
particular they allow no independently chosen automorphisms of the comparison maps.

Source: Stacks 0A07, first proof, and the flat-scalar refinement of its common tower model
(blueprint: lem-cbc-flat-scalar-direct-image-limit-coherence).

Proof:
1. The ordinary square commutes after each limit projection by naturality of d0.
   The four projection-normalization hypotheses identify its edges. Apply the square
   degreewise to obtain an equality of chain maps.
2. Strict towers form a Grothendieck category, so every derived tower object is
   isomorphic to QI with I K-injective. The exact constant-tower functor has inverse
   limit as right adjoint; hence lim I is K-injective.
3. At QI precompose both composites with rVD applied to the composite unit
   etaFS(lim I), FS(etaLUS(I)), which is invertible. Postcompose with the invertible
   LVR(FTR(qrtUD(I))). Use the six given normalization equations and naturality of
   their constituent transformations. The resulting two expressions agree by the
   localized ordinary square from step 1.
4. Transport this equality through the K-injective representative isomorphism.
   Naturality of the composite transformation supplies the equality for every
   actual derived tower morphism.
5. Flat scalar extension is an exact additive left adjoint to restriction.
   Whiskering this adjunction with towers preserves exactness, so its right
   adjoint rUt preserves K-injective complexes. This retains the original I.
No boundedness, completeness, finite-coefficient or etale-origin assumption is used. -/
theorem flatScalarDirectImageLimitCoherence
    [HasExactLimitsOfShape (Discrete ℕ) (RU x)]
    [HasExactLimitsOfShape (Discrete ℕ) (SU x)]
    [HasExactLimitsOfShape (Discrete ℕ) (RV x)]
    [HasExactLimitsOfShape (Discrete ℕ) (SV x)]
    (rUD : DerivedCategory.{w} (SU x) ⥤ DerivedCategory.{w} (RU x))
    (qrUD : DerivedCategory.Q ⋙ rUD ≅
      (rU x).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (rVD : DerivedCategory.{w} (SV x) ⥤ DerivedCategory.{w} (RV x))
    (qrVD : DerivedCategory.Q ⋙ rVD ≅
      (rV x).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (rtUD : DerivedCategory.{w} (ℕᵒᵖ ⥤ SU x) ⥤ DerivedCategory.{w} (ℕᵒᵖ ⥤ RU x))
    (qrtUD : DerivedCategory.Q ⋙ rtUD ≅
      (rUt x).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (rtVD : DerivedCategory.{w} (ℕᵒᵖ ⥤ SV x) ⥤ DerivedCategory.{w} (ℕᵒᵖ ⥤ RV x))
    (qrtVD : DerivedCategory.Q ⋙ rtVD ≅
      (rVt x).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (FR : DerivedCategory.{w} (RU x) ⥤ DerivedCategory.{w} (RV x))
    (ηFR : (x.R.morphism.modules).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ FR)
    (_universalFR : FR.IsRightDerivedFunctor ηFR
      (HomologicalComplex.quasiIso (RU x) (.up ℤ)))
    (_computesFR : ∀ I : CochainComplex (RU x) ℤ,
      I.IsKInjective → IsIso (ηFR.app I))
    (FS : DerivedCategory.{w} (SU x) ⥤ DerivedCategory.{w} (SV x))
    (ηFS : (x.S.morphism.modules).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ FS)
    (_universalFS : FS.IsRightDerivedFunctor ηFS
      (HomologicalComplex.quasiIso (SU x) (.up ℤ)))
    (_computesFS : ∀ I : CochainComplex (SU x) ℤ,
      I.IsKInjective → IsIso (ηFS.app I))
    (FTR : DerivedCategory.{w} (ℕᵒᵖ ⥤ RU x) ⥤ DerivedCategory.{w} (ℕᵒᵖ ⥤ RV x))
    (ηFTR : (FRt x).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ FTR)
    (_universalFTR : FTR.IsRightDerivedFunctor ηFTR
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ RU x) (.up ℤ)))
    (_computesFTR : ∀ I : CochainComplex (ℕᵒᵖ ⥤ RU x) ℤ,
      I.IsKInjective → IsIso (ηFTR.app I))
    (FTS : DerivedCategory.{w} (ℕᵒᵖ ⥤ SU x) ⥤ DerivedCategory.{w} (ℕᵒᵖ ⥤ SV x))
    (ηFTS : (FSt x).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ FTS)
    (_universalFTS : FTS.IsRightDerivedFunctor ηFTS
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ SU x) (.up ℤ)))
    (_computesFTS : ∀ I : CochainComplex (ℕᵒᵖ ⥤ SU x) ℤ,
      I.IsKInjective → IsIso (ηFTS.app I))
    (LUR : DerivedCategory.{w} (ℕᵒᵖ ⥤ RU x) ⥤ DerivedCategory.{w} (RU x))
    (ηLUR : (lim : (ℕᵒᵖ ⥤ RU x) ⥤ RU x).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LUR)
    (_universalLUR : LUR.IsRightDerivedFunctor ηLUR
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ RU x) (.up ℤ)))
    (_computesLUR : ∀ I : CochainComplex (ℕᵒᵖ ⥤ RU x) ℤ,
      I.IsKInjective → IsIso (ηLUR.app I))
    (LUS : DerivedCategory.{w} (ℕᵒᵖ ⥤ SU x) ⥤ DerivedCategory.{w} (SU x))
    (ηLUS : (lim : (ℕᵒᵖ ⥤ SU x) ⥤ SU x).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LUS)
    (_universalLUS : LUS.IsRightDerivedFunctor ηLUS
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ SU x) (.up ℤ)))
    (_computesLUS : ∀ I : CochainComplex (ℕᵒᵖ ⥤ SU x) ℤ,
      I.IsKInjective → IsIso (ηLUS.app I))
    (LVR : DerivedCategory.{w} (ℕᵒᵖ ⥤ RV x) ⥤ DerivedCategory.{w} (RV x))
    (ηLVR : (lim : (ℕᵒᵖ ⥤ RV x) ⥤ RV x).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LVR)
    (_universalLVR : LVR.IsRightDerivedFunctor ηLVR
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ RV x) (.up ℤ)))
    (_computesLVR : ∀ I : CochainComplex (ℕᵒᵖ ⥤ RV x) ℤ,
      I.IsKInjective → IsIso (ηLVR.app I))
    (LVS : DerivedCategory.{w} (ℕᵒᵖ ⥤ SV x) ⥤ DerivedCategory.{w} (SV x))
    (ηLVS : (lim : (ℕᵒᵖ ⥤ SV x) ⥤ SV x).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ LVS)
    (_universalLVS : LVS.IsRightDerivedFunctor ηLVS
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ SV x) (.up ℤ)))
    (_computesLVS : ∀ I : CochainComplex (ℕᵒᵖ ⥤ SV x) ℤ,
      I.IsKInjective → IsIso (ηLVS.app I))
    (d0 : x.S.morphism.modules ⋙ rV x ≅ rU x ⋙ x.R.morphism.modules)
    (_ordinaryD : ∀ N : SU x,
      (SheafOfModules.toSheaf _ ⋙ sheafCompose K (forget AddCommGrpCat)).map
          (d0.hom.app N) ≫
        x.R.morphism.underlying.hom.app ((rU x).obj N) =
      x.S.morphism.underlying.hom.app N ≫
        eqToHom (congrArg (fun F ↦ F.obj
          ((SheafOfModules.toSheaf _ ⋙ sheafCompose H (forget AddCommGrpCat)).obj N))
            x.sameDirect.symm))
    (betaU : (lim : (ℕᵒᵖ ⥤ SU x) ⥤ SU x) ⋙ rU x ≅
      rUt x ⋙ (lim : (ℕᵒᵖ ⥤ RU x) ⥤ RU x))
    (_ordinaryBetaU : ∀ T : ℕᵒᵖ ⥤ SU x,
      betaU.hom.app T = limit.post T (rU x))
    (betaV : (lim : (ℕᵒᵖ ⥤ SV x) ⥤ SV x) ⋙ rV x ≅
      rVt x ⋙ (lim : (ℕᵒᵖ ⥤ RV x) ⥤ RV x))
    (_ordinaryBetaV : ∀ T : ℕᵒᵖ ⥤ SV x,
      betaV.hom.app T = limit.post T (rV x))
    (eR : (lim : (ℕᵒᵖ ⥤ RU x) ⥤ RU x) ⋙ x.R.morphism.modules ≅
      FRt x ⋙ (lim : (ℕᵒᵖ ⥤ RV x) ⥤ RV x))
    (_ordinaryER : ∀ T : ℕᵒᵖ ⥤ RU x,
      eR.hom.app T = limit.post T x.R.morphism.modules)
    (eS : (lim : (ℕᵒᵖ ⥤ SU x) ⥤ SU x) ⋙ x.S.morphism.modules ≅
      FSt x ⋙ (lim : (ℕᵒᵖ ⥤ SV x) ⥤ SV x))
    (_ordinaryES : ∀ T : ℕᵒᵖ ⥤ SU x,
      eS.hom.app T = limit.post T x.S.morphism.modules)
    (d : FS ⋙ rVD ≅ rUD ⋙ FR)
    (_normalizedD : ∀ I : CochainComplex (SU x) ℤ,
      rVD.map (ηFS.app I) ≫ d.hom.app (DerivedCategory.Q.obj I) ≫
          FR.map (qrUD.hom.app I) =
        qrVD.hom.app ((x.S.morphism.modules.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex d0 (.up ℤ)).hom.app I) ≫
          ηFR.app (((rU x).mapHomologicalComplex (.up ℤ)).obj I))
    (dt : FTS ⋙ rtVD ≅ rtUD ⋙ FTR)
    (_normalizedDt : ∀ I : CochainComplex (ℕᵒᵖ ⥤ SU x) ℤ,
      rtVD.map (ηFTS.app I) ≫ dt.hom.app (DerivedCategory.Q.obj I) ≫
          FTR.map (qrtUD.hom.app I) =
        qrtVD.hom.app (((FSt x).mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso d0) (.up ℤ)).hom.app I) ≫
          ηFTR.app (((rUt x).mapHomologicalComplex (.up ℤ)).obj I))
    (lambdaU : LUS ⋙ rUD ≅ rtUD ⋙ LUR)
    (_normalizedLambdaU : ∀ I : CochainComplex (ℕᵒᵖ ⥤ SU x) ℤ,
      rUD.map (ηLUS.app I) ≫ lambdaU.hom.app (DerivedCategory.Q.obj I) ≫
          LUR.map (qrtUD.hom.app I) =
        qrUD.hom.app (((lim : (ℕᵒᵖ ⥤ SU x) ⥤ SU x).mapHomologicalComplex
          (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex betaU (.up ℤ)).hom.app I) ≫
          ηLUR.app (((rUt x).mapHomologicalComplex (.up ℤ)).obj I))
    (lambdaV : LVS ⋙ rVD ≅ rtVD ⋙ LVR)
    (_normalizedLambdaV : ∀ I : CochainComplex (ℕᵒᵖ ⥤ SV x) ℤ,
      rVD.map (ηLVS.app I) ≫ lambdaV.hom.app (DerivedCategory.Q.obj I) ≫
          LVR.map (qrtVD.hom.app I) =
        qrVD.hom.app (((lim : (ℕᵒᵖ ⥤ SV x) ⥤ SV x).mapHomologicalComplex
          (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex betaV (.up ℤ)).hom.app I) ≫
          ηLVR.app (((rVt x).mapHomologicalComplex (.up ℤ)).obj I))
    (cR : LUR ⋙ FR ≅ FTR ⋙ LVR)
    (_normalizedCR : ∀ I : CochainComplex (ℕᵒᵖ ⥤ RU x) ℤ,
      ηFR.app (((lim : (ℕᵒᵖ ⥤ RU x) ⥤ RU x).mapHomologicalComplex
          (.up ℤ)).obj I) ≫
          FR.map (ηLUR.app I) ≫ cR.hom.app (DerivedCategory.Q.obj I) =
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex eR (.up ℤ)).hom.app I) ≫
          ηLVR.app (((FRt x).mapHomologicalComplex (.up ℤ)).obj I) ≫ LVR.map (ηFTR.app I))
    (cS : LUS ⋙ FS ≅ FTS ⋙ LVS)
    (_normalizedCS : ∀ I : CochainComplex (ℕᵒᵖ ⥤ SU x) ℤ,
      ηFS.app (((lim : (ℕᵒᵖ ⥤ SU x) ⥤ SU x).mapHomologicalComplex
          (.up ℤ)).obj I) ≫
          FS.map (ηLUS.app I) ≫ cS.hom.app (DerivedCategory.Q.obj I) =
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex eS (.up ℤ)).hom.app I) ≫
          ηLVS.app (((FSt x).mapHomologicalComplex (.up ℤ)).obj I) ≫ LVS.map (ηFTS.app I)) :
    (∀ M : DerivedCategory.{w} (ℕᵒᵖ ⥤ SU x),
      rVD.map (cS.hom.app M) ≫ lambdaV.hom.app (FTS.obj M) ≫ LVR.map (dt.hom.app M) =
        d.hom.app (LUS.obj M) ≫ FR.map (lambdaU.hom.app M) ≫ cR.hom.app (rtUD.obj M)) ∧
    (∀ (M N : DerivedCategory.{w} (ℕᵒᵖ ⥤ SU x)) (f : M ⟶ N),
      rVD.map (FS.map (LUS.map f)) ≫
          rVD.map (cS.hom.app N) ≫ lambdaV.hom.app (FTS.obj N) ≫ LVR.map (dt.hom.app N) =
        (rVD.map (cS.hom.app M) ≫ lambdaV.hom.app (FTS.obj M) ≫ LVR.map (dt.hom.app M)) ≫
          LVR.map (FTR.map (rtUD.map f))) ∧
    (∀ I : CochainComplex (ℕᵒᵖ ⥤ SU x) ℤ, I.IsKInjective →
      CochainComplex.IsKInjective (((rUt x).mapHomologicalComplex (.up ℤ)).obj I)) := by
  let a : LUS ⋙ FS ⋙ rVD ⟶ rtUD ⋙ FTR ⋙ LVR :=
    Functor.whiskerRight cS.hom rVD ≫ Functor.whiskerLeft FTS lambdaV.hom ≫
      Functor.whiskerRight dt.hom LVR
  let b : LUS ⋙ FS ⋙ rVD ⟶ rtUD ⋙ FTR ⋙ LVR :=
    Functor.whiskerLeft LUS d.hom ≫ Functor.whiskerRight lambdaU.hom FR ≫
      Functor.whiskerLeft rtUD cR.hom
  have : IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ SU x) := by
    have := smallModuleDiagrams_isGrothendieckAbelian H
      ((sheafCompose H (forget₂ CommRingCat RingCat)).obj x.SU)
      (ULiftHom.{u} (ULift.{u} ℕᵒᵖ))
    exact IsGrothendieckAbelian.of_equivalence
      (ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ).congrLeft.symm
  have : (lim : (ℕᵒᵖ ⥤ SU x) ⥤ SU x).Additive :=
    Functor.additive_of_preserves_binary_products _
  let lS : CochainComplex (ℕᵒᵖ ⥤ SU x) ℤ ⥤ CochainComplex (SU x) ℤ :=
    (lim : (ℕᵒᵖ ⥤ SU x) ⥤ SU x).mapHomologicalComplex (.up ℤ)
  let lvR := (lim : (ℕᵒᵖ ⥤ RV x) ⥤ RV x).mapHomologicalComplex (.up ℤ)
  let fR := x.R.morphism.modules.mapHomologicalComplex (.up ℤ)
  let ftS := (FSt x).mapHomologicalComplex (.up ℤ)
  let rv := (rV x).mapHomologicalComplex (.up ℤ)
  let rtu := (rUt x).mapHomologicalComplex (.up ℤ)
  let α := NatIso.mapHomologicalComplex d0 (.up ℤ)
  let αt := NatIso.mapHomologicalComplex
    ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso d0) (.up ℤ)
  let βu := NatIso.mapHomologicalComplex betaU (.up ℤ)
  let βv := NatIso.mapHomologicalComplex betaV (.up ℤ)
  let εs := NatIso.mapHomologicalComplex eS (.up ℤ)
  let εr := NatIso.mapHomologicalComplex eR (.up ℤ)
  have ha : a = b := by
    apply derived_nat_ext
    intro I hI
    have := hI
    have : (lim : (ℕᵒᵖ ⥤ SU x) ⥤ SU x).PreservesKInjectiveComplexes :=
      limit_kinjective
    have hlimI : CochainComplex.IsKInjective (lS.obj I) := inferInstance
    have := _computesFS (lS.obj I) hlimI
    have := _computesLUS I hI
    have hcS := congrArg (fun t ↦ rVD.map t) (_normalizedCS I)
    simp only [Functor.map_comp] at hcS
    have hlv := _normalizedLambdaV (ftS.obj I)
    have hlvn := lambdaV.hom.naturality (ηFTS.app I)
    dsimp only [Functor.comp_map] at hlvn
    have hdt := congrArg (fun t ↦ LVR.map t) (_normalizedDt I)
    simp only [Functor.map_comp] at hdt
    have hqr := qrVD.hom.naturality (εs.hom.app I)
    dsimp only [Functor.comp_map] at hqr
    have hηv := ηLVR.naturality (αt.hom.app I)
    dsimp only [Functor.comp_map] at hηv
    have hdn := d.hom.naturality (ηLUS.app I)
    dsimp only [Functor.comp_map] at hdn
    have hcn := cR.hom.naturality (qrtUD.hom.app I)
    dsimp only [Functor.comp_map] at hcn
    have hlu := congrArg (fun t ↦ FR.map t) (_normalizedLambdaU I)
    simp only [Functor.map_comp] at hlu
    have hd := _normalizedD (lS.obj I)
    have hηr := ηFR.naturality (βu.hom.app I)
    dsimp only [Functor.comp_map] at hηr
    have hcR := _normalizedCR (rtu.obj I)
    have hchain : rv.map (εs.hom.app I) ≫ βv.hom.app (ftS.obj I) ≫
        lvR.map (αt.hom.app I) =
        α.hom.app (lS.obj I) ≫ fR.map (βu.hom.app I) ≫ εr.hom.app (rtu.obj I) := by
      apply HomologicalComplex.hom_ext
      intro p
      change (rV x).map (eS.hom.app (I.X p)) ≫
          betaV.hom.app ((FSt x).obj (I.X p)) ≫
            lim.map (Functor.whiskerLeft (I.X p) d0.hom) =
        d0.hom.app (limit (I.X p)) ≫
          x.R.morphism.modules.map (betaU.hom.app (I.X p)) ≫
            eR.hom.app ((rUt x).obj (I.X p))
      rw [_ordinaryES, _ordinaryBetaV, _ordinaryBetaU, _ordinaryER]
      exact ordinary_square x.S.morphism.modules x.R.morphism.modules
        (rU x) (rV x) d0 (I.X p)
    apply (cancel_epi (rVD.map (ηFS.app (lS.obj I) ≫ FS.map (ηLUS.app I)))).mp
    apply (cancel_mono (LVR.map (FTR.map (qrtUD.hom.app I)))).mp
    dsimp only [a, b, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [Functor.map_comp, Category.assoc]
    erw [reassoc_of% hcS, reassoc_of% hlvn, hdt, reassoc_of% hlv,
      reassoc_of% hqr, ← reassoc_of% hηv]
    erw [reassoc_of% hdn, ← hcn, reassoc_of% hlu, reassoc_of% hd,
      ← reassoc_of% hηr, hcR]
    simp only [← DerivedCategory.Q.map_comp_assoc]
    rw [hchain]
    rfl
  refine ⟨fun M ↦ congrArg (fun t ↦ t.app M) ha, ?_, ?_⟩
  · intro M N f
    exact a.naturality f
  · intro I hI
    obtain ⟨E, hE, hlim, ⟨adj⟩⟩ :=
      SheafOfModules.flatRestriction_exact_leftAdjoint x.aU x.flatU
    have := hE
    have := hlim
    have : PreservesColimits E := adj.leftAdjoint_preservesColimits
    let Et := (Functor.whiskeringRight ℕᵒᵖ _ _).obj E
    have : PreservesFiniteLimits Et := ⟨fun _ _ _ ↦
      whiskeringRight_preservesLimitsOfShape _⟩
    have : PreservesFiniteColimits Et := ⟨fun _ _ _ ↦
      whiskeringRight_preservesColimitsOfShape _⟩
    have : (rUt x).PreservesKInjectiveComplexes :=
      (Adjunction.whiskerRight ℕᵒᵖ adj).preservesKInjectiveComplexes
    have := hI
    exact Functor.PreservesKInjectiveComplexes.isKInjective_map I

end CategoryTheory.FlatScalarLimitCoherence
