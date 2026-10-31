/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsSupplement
public import WeilConjectures.SixFunctors.ClosedCostalkEtaleOperations
import WeilConjectures.SixFunctors.CommonLeftAdjunctionIso
import WeilConjectures.SixFunctors.ClosedTensorDualAdjunction
import WeilConjectures.SixFunctors.EtaleClosedTensorProjection
import WeilConjectures.SixFunctors.ProEtaleClosedTensorProjection
import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-!
# Exceptional restriction of a Verdier dual

Source: the current Weil conjectures blueprint, six-functors basics,
`sk-prop-sf-biduality-general/lem-weil-closed-costalk-duality.md`
(blueprint: lem-weil-closed-costalk-duality).

The two statements cover the small etale and small pro-etale sites. A termwise
localization comparison specifies each derived functor, rather than allowing an
unrelated functor. The duals are the recorded derived internal Hom construction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/- The tensor-Hom and exceptional-adjunction calculation used below has a
   categorical core: both displayed functors are right adjoints of one common
   left adjoint.  We record that core separately so the final comparison is a
   direct application of uniqueness of right adjoints. -/
/-- The six-step etale Hom calculation packages as two adjunctions with one
common left adjoint. The construction uses the closed-support projection,
tensor-Hom currying, and the supplied exceptional adjunction.
(blueprint: lem-weil-closed-costalk-etale-common-left-adjunction). -/
theorem exceptionalRestrictionVerdierDuality_etale_common_left_adjunction
    {T Z U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ)
    (R : Sheaf T.smallEtaleTopology CommRingCat.{u + 1})
    (iStar : closedCostalkEtaleModules T R ⥤
      closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R))
    [iStar.Additive] (_ai : iStar ⊣ closedCostalkEtaleModulePush i R)
    (iPull : DerivedCategory (closedCostalkEtaleModules T R) ⥤
      DerivedCategory (closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R)))
    (_pullFactors : DerivedCategory.Q ⋙ iPull ≅
      iStar.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (iPush : DerivedCategory
        (closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R)) ⥤
      DerivedCategory (closedCostalkEtaleModules T R))
    (_pushFactors : DerivedCategory.Q ⋙ iPush ≅
      (closedCostalkEtaleModulePush i R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (riExcl : DerivedCategory (closedCostalkEtaleModules T R) ⥤ DerivedCategory
      (closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R)))
    (_adj : iPush ⊣ riExcl) (ωT : DerivedCategory (closedCostalkEtaleModules T R)) :
    let Ht := derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2}
      T.smallEtaleTopology R
    let Hz := derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2}
      Z.smallEtaleTopology ((closedCostalkEtaleRingPullback i).obj R)
    ∃ F : DerivedCategory (closedCostalkEtaleModules Z
        ((closedCostalkEtaleRingPullback i).obj R)) ⥤
        (DerivedCategory (closedCostalkEtaleModules T R))ᵒᵖ,
      Nonempty (Adjunction F (((𝟭 (DerivedCategory (closedCostalkEtaleModules T R))ᵒᵖ).prod'
          ((Functor.const _).obj ωT)) ⋙ Ht ⋙ riExcl) ×
        Adjunction F (iPull.op ⋙ ((𝟭 _).prod'
          ((Functor.const _).obj (riExcl.obj ωT))) ⋙ Hz)) := by
  dsimp only
  let RZ := ((closedCostalkEtaleRingPullback i).obj R)
  obtain ⟨⟨mt, aT, eT⟩, hmt, _, _⟩ :=
    RingedDerivedNative.closedAdjunction.{u + 1, u, 0, u + 2} T.smallEtaleTopology R
  dsimp only [WeilConjectures.CoefficientClosedStructure.monoidal] at hmt
  subst mt
  obtain ⟨⟨mz, az, ez⟩, hmz, _, _⟩ :=
    RingedDerivedNative.closedAdjunction.{u + 1, u, 0, u + 2} Z.smallEtaleTopology RZ
  dsimp only [WeilConjectures.CoefficientClosedStructure.monoidal] at hmz
  subst mz
  let ST : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2} T.smallEtaleTopology R) :=
    ⟨RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} T.smallEtaleTopology R, aT, eT⟩
  let SZ : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2} Z.smallEtaleTopology RZ) :=
    ⟨RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} Z.smallEtaleTopology RZ, az, ez⟩
  obtain ⟨e⟩ := etaleClosedTensorProjection i j _hij R iStar _ai
    iPull _pullFactors iPush _pushFactors
  exact ST.common_left_of_projection SZ
    (RingedDerivedNative.symmetric.{u + 1, u, 0, u + 2} T.smallEtaleTopology R)
    (iPull) (iPush) riExcl _adj e ωT

set_option linter.unusedVariables false in
/-- Exceptional restriction of derived internal Hom, on the small etale site.
The underived inverse image is specified by its adjunction to the actual module
pushforward; the two factorization isomorphisms specify termwise descent through Q.
Thus all presentations of the source's exact inverse image and closed direct image
are allowed, and their derived functors are determined up to unique isomorphism.

Source: current blueprint, six-functors basics, closed-costalk-duality;
Stacks, Tags 04CA, 07A4, 08J9 and 08JA (blueprint: lem-weil-closed-costalk-duality).

Proof:
1. Closed pushforward is exact and fully faithful, with invertible inverse-image
counit, by lem-kun-04ca and the closed geometric-stalk formula. Geometric stalks
are exact and conservative. Its composite with complementary open restriction is zero.
2. Exact inverse image and closed direct image descend termwise. Pullback commutes
with derived tensor (lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
3. The projection morphism i_*N tensor K -> i_*(N tensor i^*K), adjoint to
pullback-tensor comparison followed by the closed counit, is invertible: its
closed restriction is invertible and its open restriction is a map of zero objects.
Apply both restrictions to its cone; joint detection makes the cone zero.
4. Currying and derived global Hom (lem-weil-pbc-ringed-internal-hom-exact-restriction,
lem-pur-rhom-global-sections) give Hom(P,RHom(Q,L)) = Hom(P tensor Q,L).
5. For every N, apply the exceptional adjunction, tensor-Hom, the inverse projection
identity, the exceptional adjunction again, and tensor-Hom. This identifies
Hom(N,Ri! RHom(K,omega)) with Hom(N,RHom(i^*K,Ri!omega)).
6. These bijections are natural in N and K. Their values on identities and their
inverse values on identities give mutually inverse Yoneda maps, natural in K.
All arrows are induced by adjunction and evaluation, as in the source. -/
theorem exceptionalRestrictionVerdierDuality_etale
    {T Z U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ)
    (R : Sheaf T.smallEtaleTopology CommRingCat.{u + 1})
    (iStar : closedCostalkEtaleModules T R ⥤
      closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R))
    [iStar.Additive] (_ai : iStar ⊣ closedCostalkEtaleModulePush i R)
    (iPull : DerivedCategory (closedCostalkEtaleModules T R) ⥤
      DerivedCategory (closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R)))
    (_pullFactors : DerivedCategory.Q ⋙ iPull ≅
      iStar.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (iPush : DerivedCategory
        (closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R)) ⥤
      DerivedCategory (closedCostalkEtaleModules T R))
    (_pushFactors : DerivedCategory.Q ⋙ iPush ≅
      (closedCostalkEtaleModulePush i R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (riExcl : DerivedCategory (closedCostalkEtaleModules T R) ⥤ DerivedCategory
      (closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R)))
    (_adj : iPush ⊣ riExcl) (ωT : DerivedCategory (closedCostalkEtaleModules T R)) :
    let ΛU := (closedCostalkEtaleRingPullback j).obj R
    Nonempty
      ((((𝟭 (DerivedCategory (closedCostalkEtaleModules T R))ᵒᵖ).prod'
          ((Functor.const _).obj ωT)) ⋙
        derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2} T.smallEtaleTopology R) ⋙ riExcl ≅
      iPull.op ⋙ ((𝟭 _).prod' ((Functor.const _).obj (riExcl.obj ωT))) ⋙
        derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2} Z.smallEtaleTopology
          ((closedCostalkEtaleRingPullback i).obj R)) := by
  dsimp
  obtain ⟨F, ⟨a, b⟩⟩ := exceptionalRestrictionVerdierDuality_etale_common_left_adjunction
    i j _hij R iStar _ai iPull _pullFactors iPush _pushFactors riExcl _adj ωT
  exact nonempty_iso_of_common_left_adjunctions F a b

/-- The pro-etale version of the common-left-adjunction calculation. The
quasi-compact complement supplies the open-closed detection used in the
projection step.
(blueprint: lem-weil-closed-costalk-proetale-common-left-adjunction). -/
theorem exceptionalRestrictionVerdierDuality_proetale_common_left_adjunction
    {T Z U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (riExcl : DerivedCategory (proEtaleRingModules T R) ⥤ DerivedCategory
      (proEtaleRingModules Z ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)))
    (_adj : proEtaleRingDerivedDirectImage i R
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _) ⊣ riExcl)
    (ωT : DerivedCategory (proEtaleRingModules T R)) :
    let Ht := derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2}
      (ProEt.topology T) R
    let Hz := derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2}
      (ProEt.topology Z) ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)
    ∃ F : DerivedCategory (proEtaleRingModules Z
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)) ⥤
        (DerivedCategory (proEtaleRingModules T R))ᵒᵖ,
      Nonempty (Adjunction F (((𝟭 (DerivedCategory (proEtaleRingModules T R))ᵒᵖ).prod'
          ((Functor.const _).obj ωT)) ⋙ Ht ⋙ riExcl) ×
        Adjunction F ((proEtaleRingDerivedPullback i R
          ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _)).op ⋙
          ((𝟭 _).prod' ((Functor.const _).obj (riExcl.obj ωT))) ⋙ Hz)) := by
  dsimp only
  let RZ := ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)
  obtain ⟨⟨mt, aT, eT⟩, hmt, _, _⟩ :=
    RingedDerivedNative.closedAdjunction.{u + 1, u, 0, u + 2} (ProEt.topology T) R
  dsimp only [WeilConjectures.CoefficientClosedStructure.monoidal] at hmt
  subst mt
  obtain ⟨⟨mz, az, ez⟩, hmz, _, _⟩ :=
    RingedDerivedNative.closedAdjunction.{u + 1, u, 0, u + 2} (ProEt.topology Z) RZ
  dsimp only [WeilConjectures.CoefficientClosedStructure.monoidal] at hmz
  subst mz
  let ST : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2} (ProEt.topology T) R) :=
    ⟨RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} (ProEt.topology T) R, aT, eT⟩
  let SZ : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2} (ProEt.topology Z) RZ) :=
    ⟨RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} (ProEt.topology Z) RZ, az, ez⟩
  obtain ⟨e⟩ := proEtaleClosedTensorProjection i j _hij R
  exact ST.common_left_of_projection SZ
    (RingedDerivedNative.symmetric.{u + 1, u, 0, u + 2} (ProEt.topology T) R)
    (proEtaleRingDerivedPullback i R RZ (Iso.refl _))
    (proEtaleRingDerivedDirectImage i R RZ (Iso.refl _)) riExcl _adj e ωT

set_option linter.unusedVariables false in
/-- Exceptional restriction of a Verdier dual, on the small pro-etale site.
Here the open complement is quasi-compact, as required for the ringed recollement.
The coefficient ring on Z is exactly the actual inverse image of R; its identification
in the recorded ringed derived operations is the identity. The dualizing object on Z
is Ri!omegaT itself, and both duals are the recorded K-injective internal Hom.

Source: current blueprint, six-functors basics, closed-costalk-duality;
Stacks, Tags 09AA, 09BM, 09AH, 07A4, 08J9 and 08JA
(blueprint: lem-weil-closed-costalk-duality).

Proof: follow the six steps in exceptionalRestrictionVerdierDuality_etale, replacing
geometric-stalk detection in step 1 by lem-weil-pbc-proetale-ringed-open-closed.
Its quasi-compact-complement hypothesis is supplied by j. The closed counit and the
open-closed exact sequence give joint detection, so the projection map is invertible
on arbitrary unbounded complexes. The ringed tensor-Hom and global-Hom comparisons
and the assumed ambient exceptional adjunction give the same natural Hom chain.
Yoneda gives the natural isomorphism, without a biduality or Tor bound. -/
theorem exceptionalRestrictionVerdierDuality
    {T Z U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (riExcl : DerivedCategory (proEtaleRingModules T R) ⥤ DerivedCategory
      (proEtaleRingModules Z ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)))
    (_adj : proEtaleRingDerivedDirectImage i R
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _) ⊣ riExcl)
    (ωT : DerivedCategory (proEtaleRingModules T R)) :
    let ΛU := (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R
    Nonempty
      ((((𝟭 (DerivedCategory (proEtaleRingModules T R))ᵒᵖ).prod'
          ((Functor.const _).obj ωT)) ⋙
        derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2} (ProEt.topology T) R) ⋙ riExcl ≅
      (proEtaleRingDerivedPullback i R
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _)).op ⋙
      ((𝟭 _).prod' ((Functor.const _).obj (riExcl.obj ωT))) ⋙
        derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2} (ProEt.topology Z)
          ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)) := by
  dsimp
  obtain ⟨F, ⟨a, b⟩⟩ := exceptionalRestrictionVerdierDuality_proetale_common_left_adjunction
    i j _hij R riExcl _adj ωT
  exact nonempty_iso_of_common_left_adjunctions F a b

end AlgebraicGeometry.Scheme
