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
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitAcyclic
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

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

Proof plan:
1. Realize strict towers as module sheaves on diagram sites by
   lem-weil-pbc-diagram-site-realization (reindex its lifted naturals along their
   canonical equivalence with native naturals). By prop-pur-kinjective-resolutions-exist choose
   a K-injective S_U tower I and a K-injective target resolution j: F_S^Tow I → J.
   Flat restriction preserves K-injectives by lem-weil-pbc-flat-ringed-diagram-restriction.
2. The constant-tower functor is exact, since tower kernels and cokernels are levelwise
   (lem-weil-tower-category-levelwise-abelian). Its right adjoint, inverse limit, preserves
   K-injectives by lem-weil-pbc-right-adjoint-preserves-kinjective. The four ordinary
   limits of I, r_U I, J and r_V J therefore compute total derived limits by
   lem-weil-pbc-ringed-strict-tower-homotopy-limit.
3. Restriction changes only scalar action. The ordinary scalar/direct-image map d0,
   scalar/limit maps beta, and direct-image/limit maps e are the identified underlying
   maps, with the displayed projection normalizations. Restriction also preserves products.
4. Compose the ordinary coherence square with each limit projection. Its two composites
   agree by naturality of d0; the projections determine the map. Naturality of beta also
   commutes with the target-resolution map j. These are equalities of chain maps.
5. Use j_R = d0_Tow(I) inverse followed by r_V(j). Its target r_V J is K-injective.
   Lemma lem-weil-ringed-tower-pushforward-limit-acyclic makes both target-limit maps
   quasi-isomorphisms. The normalization in lem-weil-ringed-tower-pushforward-limit-comparison
   represents c by e followed by the target-resolution limit. The d maps use d0 on the
   same K-injective source complexes.
6. Apply lem-cbc-exact-product-functor-strict-limit to restriction at U and V.
   Its resolution normalization permits identity resolutions of r_U I and r_V J,
   hence computes both lambda maps using the corresponding beta, on these same complexes.
7. Naturality of beta moves r_V(lim j) past beta. Substitute
   lim(r_V j) = lim(j_R) lim(d0_Tow(I)). The ordinary square from step 4 gives exactly
   the two composites in the first conclusion. Localize this equality of chain maps.
8. Every derived tower object has such a representative. By lem-weil-pbc-kinjective-hom-derived,
   actual derived morphisms between K-injectives are chain maps modulo homotopy.
   The ordinary maps are natural and additive functors preserve homotopies, giving
   the second conclusion for actual derived morphisms. Resolution independence follows
   from the specified c and lambda normalizations. The last conclusion retains the
   original I and its K-injective restriction. The all-complexes normalization equations
   above compute the maps on these very complexes using d0, beta and e.
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
  sorry

end CategoryTheory.FlatScalarLimitCoherence
