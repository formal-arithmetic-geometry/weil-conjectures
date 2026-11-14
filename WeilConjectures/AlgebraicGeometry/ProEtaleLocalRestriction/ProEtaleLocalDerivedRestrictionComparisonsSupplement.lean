/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons

/-!
# Exact inverse image and local derived restriction

Source: Stacks Project, derived.tex, Tag 015F; sites-modules.tex, Tags 03D2, 03DA,
04IX; Bhatt--Scholze, Proposition 6.8.11(3).
(blueprint: lem-weil-pbc-local-derived-restriction-comparisons).

## Main declarations

* `inverseImage_exact`: exactness over the actual inverse-image ring.
* `comparison`: the prescribed localization-representative comparison.
* `comparisons`: its functorial cohomology and shifted-single normalizations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u wT wS wU

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.ProEtaleLocalRestriction

variable {S T : Scheme.{u}} (g : S ⟶ T)
  (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt)
  [HasDerivedCategory.{wT} (SheafOfModules.{u + 1} (ring R))]
  [HasDerivedCategory.{wS} (SheafOfModules.{u + 1} (inverseRing g R))]
  [HasDerivedCategory.{wU} (SheafOfModules.{u + 1} ((inverseRing g R).over U))]

/-- The specified representative-normalized comparison: first apply derived restriction
of the inverse representative isomorphism, then the exact localization factor.
Source: Stacks, Tag 015F (blueprint: lem-weil-pbc-local-derived-restriction-comparisons). -/
def comparison (K : DerivedCategory (SheafOfModules.{u + 1} (ring R))) :
    (restriction g R U).mapDerivedCategory.obj
        ((proEtaleModuleInverseImage g R).mapDerivedCategory.obj K) ≅
      ringedSiteDerivedRestrictionOfUniverses (inverseRing g R) U
        ((proEtaleModuleInverseImage g R).mapDerivedCategory.obj K) :=
  (restriction g R U).mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso
        ((proEtaleModuleInverseImage g R).mapDerivedCategory.obj K)).symm ≪≫
    (restriction g R U).mapDerivedCategoryFactors.app
      (DerivedCategory.Q.objPreimage
        ((proEtaleModuleInverseImage g R).mapDerivedCategory.obj K))

/-- Functorial local restriction with normalized cohomology and shifted-single comparisons.
Source: Stacks, Tag 015F; Bhatt--Scholze, Proposition 6.8.11(3)
(blueprint: lem-weil-pbc-local-derived-restriction-comparisons).
Proof:
1. Actual-ring module inverse image is exact by the abelian comparison and faithful
   exact forgetful functors (inverseImage_exact). Slice restriction preserves finite
   limits and colimits; its universe-independent interface applies to this small site.
2. Apply exact-functor localization separately to F and G. It gives DF, DG and their
   factorization isomorphisms, commuting with every integer shift, without boundedness.
3. For X = DF(K), use the chosen representative C and epsilon : Q(C) ≅ X. The comparison
   is DG(epsilon.symm) followed by the localization factor at C, exactly comparison.
4. Define L on objects by the recorded representative restriction, and on maps by
   alpha.inv followed by DG(DF(a)) followed by alpha.hom. Cancellation proves the functor
   laws and naturality, and transports inverses. For any other representative B, replace
   epsilon by Q(B) ≅ X; naturality of the localization factor identifies the comparisons
   on chain maps and inverted quasi-isomorphisms, hence on all derived morphisms.
5. Exact functors commute with complex cohomology by the kernel/image comparison. Descend
   that comparison through localization. Compose G(h_F), h_G and H(alpha); their naturality
   gives the displayed natural cohomology isomorphism and its compatibility with alpha.
6. On degree-zero complexes use the exact-functor single comparison twice. On a shift r,
   use the two derived shift comparisons and shift the single comparison. Compose with
   alpha.inv to obtain the specified natural shifted-single comparison.
7. On the representative M[0][r] these comparisons use the same kernels and images:
   identity on GFM in degree -r and zero in the other degrees. The termwise shifts have
   differential (-1)^r GF(d), for either sign of r. Transport by step 4 identifies these
   comparisons with the chosen representative convention.
DAG inputs: def-weil-proetale-inverse-image, def-pur-localized-ringed-site,
lem-weil-pbc-finite-type-restriction-exact,
situation-conventions,
def-weil-pbc-ringed-site-derived-restriction, def-weil-abstract-derived-category, and
lem-weil-pbc-exact-functor-complex-cohomology. -/
theorem comparisons :
    ∃ (L : DerivedCategory (SheafOfModules.{u + 1} (ring R)) ⥤
        DerivedCategory (SheafOfModules.{u + 1} ((inverseRing g R).over U)))
      (hobj : ∀ K, L.obj K =
        ringedSiteDerivedRestrictionOfUniverses (inverseRing g R) U
          ((proEtaleModuleInverseImage g R).mapDerivedCategory.obj K))
      (α : (proEtaleModuleInverseImage g R).mapDerivedCategory ⋙
        (restriction g R U).mapDerivedCategory ≅ L),
      (∀ K, α.app K ≪≫ eqToIso (hobj K) = comparison g R U K) ∧
      (∀ {K K'} (a : K ⟶ K'), L.map a =
        α.inv.app K ≫ (restriction g R U).mapDerivedCategory.map
          ((proEtaleModuleInverseImage g R).mapDerivedCategory.map a) ≫ α.hom.app K') ∧
      (∀ q : ℤ, ∃ c :
        DerivedCategory.homologyFunctor (SheafOfModules.{u + 1} (ring R)) q ⋙
            proEtaleModuleInverseImage g R ⋙ restriction g R U ≅
          L ⋙ DerivedCategory.homologyFunctor
            (SheafOfModules.{u + 1} ((inverseRing g R).over U)) q,
        ∀ K, c.hom.app K =
          (restriction g R U).map
              (((proEtaleModuleInverseImage g R).mapDerivedCategoryHomologyFunctorIso q).hom.app
                K) ≫
            ((restriction g R U).mapDerivedCategoryHomologyFunctorIso q).hom.app
              ((proEtaleModuleInverseImage g R).mapDerivedCategory.obj K) ≫
            (DerivedCategory.homologyFunctor
              (SheafOfModules.{u + 1} ((inverseRing g R).over U)) q).map (α.hom.app K)) ∧
      (∀ r : ℤ, ∃ s :
        DerivedCategory.singleFunctor (SheafOfModules.{u + 1} (ring R)) 0 ⋙
            shiftFunctor _ r ⋙ L ≅
          proEtaleModuleInverseImage g R ⋙ restriction g R U ⋙
            DerivedCategory.singleFunctor
              (SheafOfModules.{u + 1} ((inverseRing g R).over U)) 0 ⋙ shiftFunctor _ r,
        ∀ M, s.hom.app M =
          α.inv.app ((DerivedCategory.singleFunctor _ 0).obj M⟦r⟧) ≫
            (restriction g R U).mapDerivedCategory.map
              (((proEtaleModuleInverseImage g R).mapDerivedCategory.commShiftIso r).hom.app
                ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
            ((restriction g R U).mapDerivedCategory.commShiftIso r).hom.app
              ((proEtaleModuleInverseImage g R).mapDerivedCategory.obj
                ((DerivedCategory.singleFunctor _ 0).obj M)) ≫
            (shiftFunctor _ r).map
              ((restriction g R U).mapDerivedCategory.map
                  (((proEtaleModuleInverseImage g R).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
                ((restriction g R U).mapDerivedCategorySingleFunctor 0).hom.app
                  ((proEtaleModuleInverseImage g R).obj M))) := by
  let F := proEtaleModuleInverseImage g R
  let G := restriction g R U
  let D := F.mapDerivedCategory ⋙ G.mapDerivedCategory
  let obj := fun K ↦ ringedSiteDerivedRestrictionOfUniverses (inverseRing g R) U
    (F.mapDerivedCategory.obj K)
  let L := D.copyObj obj (comparison g R U)
  let α := D.isoCopyObj obj (comparison g R U)
  refine ⟨L, (fun _ ↦ rfl), α, ?_, ?_, ?_, ?_⟩
  · intro K
    simp [α, Functor.isoCopyObj]
  · intro K K' a
    rfl
  · intro q
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u + 1} ((inverseRing g R).over U)) q
    refine ⟨Functor.isoWhiskerRight (F.mapDerivedCategoryHomologyFunctorIso q) G ≪≫
      Functor.isoWhiskerLeft F.mapDerivedCategory (G.mapDerivedCategoryHomologyFunctorIso q) ≪≫
      Functor.isoWhiskerRight α H, ?_⟩
    intro K
    rfl
  · intro r
    let single := DerivedCategory.singleFunctor (SheafOfModules.{u + 1} (ring R)) 0
    let sF := F.mapDerivedCategorySingleFunctor 0
    let sG := G.mapDerivedCategorySingleFunctor 0
    refine ⟨Functor.isoWhiskerLeft (single ⋙ shiftFunctor _ r) α.symm ≪≫
      Functor.isoWhiskerLeft single
        (Functor.isoWhiskerRight (F.mapDerivedCategory.commShiftIso r) G.mapDerivedCategory ≪≫
          Functor.isoWhiskerLeft F.mapDerivedCategory (G.mapDerivedCategory.commShiftIso r)) ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerRight sF G.mapDerivedCategory ≪≫ Functor.isoWhiskerLeft F sG)
        (shiftFunctor _ r), ?_⟩
    intro M
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Iso.symm_hom, Functor.comp_obj, Functor.map_comp, Category.assoc]
    rfl

end AlgebraicGeometry.Scheme.ProEtaleLocalRestriction
