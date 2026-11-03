/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedCompactSupportProjection
public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CompactSupportCondensedRealizationSetup
public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.SemilinearCompactSupportCoefficientTransport
public import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERealizationDefinitions
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientComparisons
public import WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.SixFunctors.Supporting.OperationCoefficientActionData
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SystemSupportRefinement

import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SystemSupportRefinementComposition
import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.OmegaProperCoefficientProjection
import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedOpenRestrictedCounit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedComplement
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedEIntegralExchange
public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERationalCondensedExchange
public import WeilConjectures.ProperBaseChange.CondensedERealizationSystem
public import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
public import WeilConjectures.SmoothPurity.Supporting.BasicOperationCoefficientCoherence
public import WeilConjectures.SmoothPurity.Supporting.BasicOperationReductionAndEvaluation

/-! # Compact-support condensed realization

Source: Bhatt--Scholze 6.7.2, 6.7.14--6.7.17, 6.8.14--6.8.15;
blueprint sk-thm-purity-transport, Steps 2--3.
(blueprint: lem-pur-compact-support-condensed-realization).

## Main definitions and statements

- `IntegralModel`, `alpha`: actual strict-tower reconstruction and its counit.
- `condensedProjection`: the original proper/open scalar projection.
- `FiniteComparison`: full-system and rationalized coefficient compatibility.
- `systemRefinement`, `fieldRefinement`: unit-normalized refinement arrows.
- `ComparisonFamily`, `compactSupport_condensedRealization`: simultaneous comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

attribute [local irreducible] HasDerivedCategory.standard
  HasDerivedCategory.ofHasKInjectiveResolutions _root_.instCategoryDerivedCategory

attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.CommShift.ofIso CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.extendScalars
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

attribute [local irreducible] WeilConjectures.integralCoefficientCommRingSheaf

attribute [local irreducible] WeilConjectures.CompactSupportCondensedRealization.encodingScalarMap
  WeilConjectures.CompactSupportCondensedRealization.IsIntegralScalarSquare

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CompactSupportCondensedRealization

namespace CoefficientBasisProof

open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open Profinite

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] CategoryTheory.catToReflQuiver in
end CoefficientBasisProof

variable (l : ℕ) [Fact l.Prime]
  (E F : Type u) [NormedField E] [NormedField F]
  [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The actual finite condensed scalar functor.
Source: blueprint proof Step 6
(blueprint: lem-pur-compact-support-condensed-realization). -/
abbrev fieldScalar (W : Scheme.{u}) :=
  condensedScalar (fieldMap l E F i) W

/-- The actual finite-valued algebraic-closure scalar functor.
Source: blueprint proof Step 13
(blueprint: lem-pur-compact-support-condensed-realization). -/
abbrev omegaScalar (a : E →ₐ[ℚ_[l]] PadicAlgCl l) (W : Scheme.{u}) :=
  condensedScalar (omegaMap l E a) W

variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

attribute [local irreducible] latticeScalar

/-- Simultaneous reconstruction and field realization for one coefficient field.
The reduction and realization data are the recorded dependency data; the support
functors retain the fixed geometric compactification.
Source: blueprint proof Steps 1--5
(blueprint: lem-pur-compact-support-condensed-realization). -/
structure CoefficientData where
  realization : CondensedERealization.Data l E k
  reduction : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus.{u, u} l E W
  atCompactification : ∀ (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))] (c : Compactification f),
    RealizationAt l E k realization reduction X Y f c

/-- The rationalized coefficient square, with exactly the specified scalar and realization
maps. Packaging this equation keeps generated comparison-record declarations small.
Source: blueprint proof Steps 7--12
(blueprint: lem-pur-compact-support-condensed-realization). -/
def IsFiniteRationalSquare (A : CoefficientData l E k) (B : CoefficientData l F k)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f)
    (comparison :
    integralSupport l E c A.reduction (A.atCompactification X Y f c).integral ⋙
        integralScalar l E F i k Y ≅
      integralScalar l E F i k X ⋙
        integralSupport l F c B.reduction (B.atCompactification X Y f c).integral) : Prop :=
  ∀ K : CondensedERealization.Integral l E X.scheme,
    ((B.realization.atObject Y).realization.functor ⋙
      (boundedConstructible (CondensedERealization.Coefficient F Y.scheme)).ι).map
        ((pbcRationalization Y.scheme (pbcIntegralDatum l F) (pbcUniformizer l F)).map
          (comparison.hom.app K)) ≫
        (B.atCompactification X Y f c).realization.hom.app
          (ScalarLocalization.mk ((integralScalar l E F i k X).obj K)) ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification
          (Profinite.continuousCoefficientRingObj F) c).map
            ((latticeScalar l E F i k X
              (A.realization.atObject X) (B.realization.atObject X)).hom.app K) =
      (latticeScalar l E F i k Y
        (A.realization.atObject Y) (B.realization.atObject Y)).hom.app
          ((integralSupport l E c A.reduction
            (A.atCompactification X Y f c).integral).obj K) ≫
        (fieldScalar l E F i Y.scheme).map
          ((A.atCompactification X Y f c).realization.hom.app (ScalarLocalization.mk K)) ≫
        (condensedProjection (fieldMap l E F i) c).app
          (((A.realization.atObject X).realization.functor.obj (ScalarLocalization.mk K)).obj)

attribute [local irreducible] IsFiniteRationalSquare

/-- The finite integral comparison, with its whole-system and rationalized squares.
These equations fix its normalization by the actual coefficient projection mate.
Source: blueprint proof Steps 7--12
(blueprint: lem-pur-compact-support-condensed-realization). -/
structure FiniteComparison (A : CoefficientData l E k) (B : CoefficientData l F k)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f) where
  comparison :
    integralSupport l E c A.reduction (A.atCompactification X Y f c).integral ⋙
        integralScalar l E F i k Y ≅
      integralScalar l E F i k X ⋙
        integralSupport l F c B.reduction (B.atCompactification X Y f c).integral
  reduction : IsIntegralScalarSquare l E F i k A.reduction B.reduction X Y c
    (A.atCompactification X Y f c).integral
    (B.atCompactification X Y f c).integral comparison
  rationalization : IsFiniteRationalSquare l E F i k A B X Y f c comparison

/-- Extension to the finite-valued closure preserves bounded constructibility.
Source: blueprint proof Steps 13--14; finite-coefficient two-colimit
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: scalar extension is the filtered colimit of finite free coefficient changes
and hence exact. Scalar-extending each finite presentation on the same finite
stratification preserves local finite presentation and the cohomological bounds.
The coefficient ring is the finite-subfield-valued ring throughout. -/
theorem omegaScalar_preserves (a : E →ₐ[ℚ_[l]] PadicAlgCl l) (W : Scheme.{u})
    (K : CondensedERealization.Constructible E W) :
    boundedConstructible (padicAlgClRingObj W l) ((omegaScalar l E a W).obj K.obj) := by
  exact boundedConstructible_leftDerivedExtendScalars_obj _ _
    (coefficientMap (omegaMap l E a) W) K.obj K.property

/-- Closure projection is the same canonical map, on the bounded constructible domain.
Source: blueprint proof Steps 13--14
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: express the finite-valued closure coefficient as the filtered colimit of finite
extensions containing the image of E. Use simultaneous coefficient complexes with a
common lower bound. Exact open extension commutes with this colimit. Bounded-below
qcqs proper-image continuity identifies the colimit of the finite projection maps
with this precise counit transpose. Each finite projection is invertible.
The formal combination applies the proper-factor comparison to extension by zero,
then pastes it with the canonical open scalar isomorphism and the associators. -/
theorem omegaProjection_isIso (a : E →ₐ[ℚ_[l]] PadicAlgCl l)
    (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))] (c : Compactification f)
    (K : CondensedERealization.Constructible E X.scheme) :
    IsIso ((condensedProjection (omegaMap l E a) c).app K.obj) := by
  let f' := CondensedERealization.Base.map X Y f
  have : LocallyOfFiniteType (c.overObj (f := f')).hom := by
    change LocallyOfFiniteType (c.g ≫ Y.scheme ↘ Spec (.of k))
    infer_instance
  have : QuasiCompact (c.overObj (f := f')).hom := by
    change QuasiCompact (c.g ≫ Y.scheme ↘ Spec (.of k))
    infer_instance
  have : IsSeparated (c.overObj (f := f')).hom := by
    change IsSeparated (c.g ≫ Y.scheme ↘ Spec (.of k))
    infer_instance
  have : IsOpenImmersion (c.overI (f := f')).left := by
    change IsOpenImmersion c.i
    infer_instance
  have hK := CondensedRing.boundedConstructible_openImmersionLowerShriek_obj
    (Profinite.continuousCoefficientRingObj E) l (c.overI (f := f')) ⟨K.obj, K.property⟩
  let K' : CondensedERealization.Constructible E c.Z := ⟨_, hK⟩
  let : IsNoetherian c.Z := base_noetherian k ⟨c.Z⟩
  have := base_noetherian k Y
  have : IsIso ((condensedPushScalar (omegaMap l E a) c.g).app
      ((CondensedRing.openImmersionLowerShriek
        (Profinite.continuousCoefficientRingObj E) c.i).mapDerivedCategory.obj K.obj)) :=
    omegaProperCoefficientProjection_isIso l E a c.g K'
  unfold condensedProjection pasteScalar
  dsimp only [NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.id_comp, Category.comp_id]
  infer_instance

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- The compactification opens have the finiteness needed for the whole-system mate.
Source: blueprint proof Step 15; finite-type over Noetherian schemes
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: the middle scheme is proper over the Noetherian finite-type target, hence
Noetherian. Every open immersion into a Noetherian scheme is quasi-compact. -/
theorem compactification_open_quasiCompact (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))] (c : Compactification f) :
    QuasiCompact c.i := by
  have := base_noetherian k X
  infer_instance

universe uA uB uC uD vA vB vC vD

attribute [local semireducible] WeilConjectures.integralCoefficientCommRingSheaf

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Whole-system refinement is the intrinsic proper/open mate, followed by the
proper compositor. No levelwise arrows are assembled into a derived-system map.
Source: blueprint proof Step 15; Stacks 0F7B
(blueprint: lem-pur-compact-support-condensed-realization). -/
def systemRefinement (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    {c d : Compactification f} (r : c.Refinement d) :
    systemSupport l E d ⟶ systemSupport l E c := by
  letI := compactification_open_quasiCompact k X Y f c
  letI := compactification_open_quasiCompact k X Y f d
  with_unfolding_all
    exact SemilinearProperOpen.supportRefinement (quotientRings l E) (quotientMaps l E)
      c.i c.g d.i d.g r.hom (r.i_hom.trans (Category.id_comp _).symm)
      (congrArg (SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E)) r.hom_g)

attribute [local irreducible] WeilConjectures.integralCoefficientCommRingSheaf

/-- The actual limit of the whole-system refinement, in the completed presentation.
Source: blueprint proof Step 15
(blueprint: lem-pur-compact-support-condensed-realization). -/
def rawRefinement (A : CoefficientData l E k) (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    {c d : Compactification f} (r : c.Refinement d) :
    rawSupport l E d (A.reduction X.scheme) ⟶ rawSupport l E c (A.reduction X.scheme) :=
  Functor.whiskerRight
    (Functor.whiskerLeft ((purCoefficientModel l E X.scheme).functor ⋙
      (A.reduction X.scheme).reduction) (systemRefinement l E k X Y f r))
    (coefficientSequenceDerivedRestriction.{u, u} l E Y.scheme ⋙
      coefficientConstantTowerLimit.{u, u} l E Y.scheme ⋙
        (purCoefficientModel l E Y.scheme).inverse)

/-- Restrict an actual natural transformation to a full subcategory of its target.
Source: blueprint proof Step 15; Mathlib ObjectProperty.lift
(blueprint: lem-pur-compact-support-condensed-realization). -/
def liftSupportTransformation
    {C : Type uA} {D : Type uB} [Category.{vA} C] [Category.{vB} D]
    (P : ObjectProperty D) (F G : C ⥤ D)
    (hF : ∀ K, P (F.obj K)) (hG : ∀ K, P (G.obj K)) (a : F ⟶ G) :
    P.lift F hF ⟶ P.lift G hG where
  app K := ObjectProperty.homMk (a.app K)
  naturality _K _L v := ObjectProperty.hom_ext _ (a.naturality v)

/-- Restriction of that actual limit map to the full integral categories.
Source: blueprint proof Step 15
(blueprint: lem-pur-compact-support-condensed-realization). -/
def integralRefinement (A : CoefficientData l E k) (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    {c d : Compactification f} (r : c.Refinement d) :
    integralSupport l E d A.reduction (A.atCompactification X Y f d).integral ⟶
      integralSupport l E c A.reduction (A.atCompactification X Y f c).integral :=
  liftSupportTransformation
    (PbcIsBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E))
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)) ⋙
      rawSupport l E d (A.reduction X.scheme))
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)) ⋙
      rawSupport l E c (A.reduction X.scheme))
    (fun K ↦ (A.atCompactification X Y f d).integral.preserves K.obj K.property)
    (fun K ↦ (A.atCompactification X Y f c).integral.preserves K.obj K.property)
    (Functor.whiskerLeft
      (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)))
      (rawRefinement l E k A X Y f r))

/-- The refinement squares for reconstruction and field realization, before any
coefficient extension is made. These are equations of the actual whole-system maps.
Source: blueprint proof Steps 15--16
(blueprint: lem-pur-compact-support-condensed-realization). -/
structure RefinementCoherence (A : CoefficientData l E k)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] {c d : Compactification f} (r : c.Refinement d) : Prop where
  invertible : IsIso (integralRefinement l E k A X Y f r)
  field_invertible : IsIso (fieldRefinement (Profinite.continuousCoefficientRingObj E) r)
  reduction : ∀ K : CondensedERealization.Integral l E X.scheme,
    (integralReduction l E k Y (A.reduction Y.scheme)).map
        ((integralRefinement l E k A X Y f r).app K) ≫
        (alpha l E c A.reduction (A.atCompactification X Y f c).integral).app K =
      (alpha l E d A.reduction (A.atCompactification X Y f d).integral).app K ≫
        (systemRefinement l E k X Y f r).app
          ((integralReduction l E k X (A.reduction X.scheme)).obj K)
  realization : ∀ K : CondensedERealization.Integral l E X.scheme,
    ((A.realization.atObject Y).realization.functor ⋙
      (boundedConstructible (CondensedERealization.Coefficient E Y.scheme)).ι).map
        ((pbcRationalization Y.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).map
          ((integralRefinement l E k A X Y f r).app K)) ≫
        (A.atCompactification X Y f c).realization.hom.app (ScalarLocalization.mk K) =
      (A.atCompactification X Y f d).realization.hom.app (ScalarLocalization.mk K) ≫
        (fieldRefinement (Profinite.continuousCoefficientRingObj E) r).app
          ((A.realization.atObject X).realization.functor.obj (ScalarLocalization.mk K))

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime]
  (E F G : Type u) [NormedField E] [NormedField F] [NormedField G]
  [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F] [NormedAlgebra ℚ_[l] G]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] [FiniteDimensional ℚ_[l] G]
  (i : E →ₐ[ℚ_[l]] F) (j : F →ₐ[ℚ_[l]] G)
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- The inherited integral tensor associator is the published ambient tensor associator.
Source: blueprint proof Steps 9--12; prop-weil-pbc-scalar-extension
(blueprint: lem-pur-compact-support-condensed-realization). -/
def integralScalarComp (T : CondensedERealization.Base k) :
    integralScalar l E F i k T ⋙ integralScalar l F G j k T ≅
      integralScalar l E G (j.comp i) k T :=
  NatIso.ofComponents
    (F := integralScalar l E F i k T ⋙ integralScalar l F G j k T)
    (G := integralScalar l E G (j.comp i) k T)
    (fun K ↦
      ObjectProperty.isoMk _
        (X := (integralScalar l E F i k T ⋙ integralScalar l F G j k T).obj K)
        (Y := (integralScalar l E G (j.comp i) k T).obj K)
        ((pbcAmbientScalarComp l E F G i j T.scheme).app K.obj))
    (fun v ↦ by
      ext
      exact (pbcAmbientScalarComp l E F G i j T.scheme).hom.naturality v.hom)

/-- The integral identity scalar comparison is the actual tensor unit.
Source: blueprint proof Steps 9--12; prop-weil-pbc-scalar-extension
(blueprint: lem-pur-compact-support-condensed-realization). -/
def integralScalarId (T : CondensedERealization.Base k) :
    integralScalar l E E (AlgHom.id ℚ_[l] E) k T ≅ 𝟭 _ :=
  NatIso.ofComponents
    (F := integralScalar l E E (AlgHom.id ℚ_[l] E) k T) (G := 𝟭 _)
    (fun K ↦
      ObjectProperty.isoMk _
        (X := (integralScalar l E E (AlgHom.id ℚ_[l] E) k T).obj K) (Y := K)
        ((pbcEmbeddingAmbientUnit l E T.scheme).app K.obj))
    (fun v ↦ by
      ext
      exact (pbcEmbeddingAmbientUnit l E T.scheme).hom.naturality v.hom)

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- The actual bounded constructible predicate is closed under all ambient shifts.
Source: archived ProEtaleModule/DerivedCategory.lean, cohomological definition;
blueprint proof Step 17 (blueprint: lem-pur-compact-support-condensed-realization).
Proof: shifting reindexes the cohomology sheaves by an integer and translates the
finite vanishing interval. The cohomology shift isomorphism preserves the existing
local finite-presentation condition on every stratum, so constructibility is unchanged.
This uses no kernel or extension closure assertion for arbitrary coefficient rings. -/
theorem fieldConstructible_shiftStable (E : Type u) [NormedField E] (W : Scheme.{u}) :
    (boundedConstructible (CondensedERealization.Coefficient E W)).IsStableUnderShift ℤ := by
  refine ⟨fun n ↦ ⟨fun K hK ↦ ?_⟩⟩
  exact ⟨DerivedCategory.TStructure.t.bounded.le_shift n K hK.1,
    fun a ↦ IsConstructibleModuleObject.of_iso
      (((DerivedCategory.homologyFunctor _ 0).shiftIso n a (n + a) rfl).app K).symm
      (hK.2 (n + a))⟩

attribute [local instance] fieldConstructible_shiftStable

set_option cleanup.letToHave false in
/-- Shift compatibility includes the universal coefficient counits and the
scalar-extension normalization of the realization, fixing the induced comparisons.
The rational shifts are exactly the recorded tensor-localization shifts.
Source: blueprint proof Step 17; lem-weil-pbc-derived-adjunction-shift
(blueprint: lem-pur-compact-support-condensed-realization). -/
def shiftCoherentClauses (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (A : CoefficientData l E k)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))]
    [IsNoetherian X.scheme] [IsNoetherian Y.scheme]
    [Fact (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Y.scheme ≤ n)]
    [Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x))]
    [Fact (∀ y : Y.scheme, IsUnit (l : Y.scheme.presheaf.stalk y))]
    [ObjectProperty.IsTriangulated
      (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E))]
    [ObjectProperty.IsTriangulated
      (PbcIsBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E))]
    (c : Compactification f)
    (sI : (integralSupport l E c A.reduction
      (A.atCompactification X Y f c).integral).CommShift ℤ)
    (sQ : (rationalSupport l E c A.reduction
      (A.atCompactification X Y f c).integral).CommShift ℤ)
    (sX : (A.realization.atObject X).realization.functor.CommShift ℤ)
    (sY : (A.realization.atObject Y).realization.functor.CommShift ℤ)
    (sRX : (A.reduction X.scheme).reduction.CommShift ℤ)
    (sRY : (A.reduction Y.scheme).reduction.CommShift ℤ)
    (sLX : (coefficientSequenceLimit l E X.scheme).CommShift ℤ)
    (sLY : (coefficientSequenceLimit l E Y.scheme).CommShift ℤ)
    (sPX : (purCoefficientModel l E X.scheme).functor.CommShift ℤ)
    (sPY : (purCoefficientModel l E Y.scheme).functor.CommShift ℤ)
    (sS : (systemSupport l E c).CommShift ℤ)
    (sVX : (pbcRationalization X.scheme (pbcIntegralDatum l E)
      (pbcUniformizer l E)).CommShift ℤ)
    (sVY : (pbcRationalization Y.scheme (pbcIntegralDatum l E)
      (pbcUniformizer l E)).CommShift ℤ) : Prop := by
  let := (pbcRationalTriangulationData l E X.scheme
    (base_dimension k X) (base_primeUnit l k X)).choose_spec.choose_spec.2.choose_spec.choose
  let := (pbcRationalTriangulationData l E Y.scheme
    (base_dimension k Y) (base_primeUnit l k Y)).choose_spec.choose_spec.2.choose_spec.choose
  let := (A.realization.atObject X).encodingAdditive
  let := (A.realization.atObject Y).encodingAdditive
  let := (A.realization.atObject X).encodingInverseAdditive
  let := (A.realization.atObject Y).encodingInverseAdditive
  let := sI
  let := sQ
  let := sX
  let := sY
  let := sRX
  let := sRY
  let := sLX
  let := sLY
  let := sPX
  let := sPY
  let := sS
  let := sVX
  let := sVY
  let : (reconstructedSystem l E c A.reduction
      (A.atCompactification X Y f c).integral).CommShift ℤ := by
    unfold reconstructedSystem
    infer_instance
  let : (CondensedERealization.moduleEncoding l E X.scheme
      (A.realization.atObject X).sectionIso).mapDerivedCategory.functor.CommShift ℤ :=
    inferInstanceAs ((CondensedERealization.moduleEncoding l E X.scheme
      (A.realization.atObject X).sectionIso).functor.mapDerivedCategory.CommShift ℤ)
  let : (CondensedERealization.moduleEncoding l E Y.scheme
      (A.realization.atObject Y).sectionIso).mapDerivedCategory.functor.CommShift ℤ :=
    inferInstanceAs ((CondensedERealization.moduleEncoding l E Y.scheme
      (A.realization.atObject Y).sectionIso).functor.mapDerivedCategory.CommShift ℤ)
  let I := integralSupport l E c A.reduction
    (A.atCompactification X Y f c).integral
  let Q := rationalSupport l E c A.reduction
    (A.atCompactification X Y f c).integral
  let hI : Prop := I.IsTriangulated
  let hRX : Prop := NatTrans.CommShift (A.reduction X.scheme).adjunction.counit ℤ
  let hRY : Prop := NatTrans.CommShift (A.reduction Y.scheme).adjunction.counit ℤ
  let hLimit : Prop := NatTrans.CommShift
    (limitPresentation l E c A.reduction (A.atCompactification X Y f c).integral).hom ℤ
  let hAlpha : Prop := NatTrans.CommShift
    (alpha l E c A.reduction (A.atCompactification X Y f c).integral) ℤ
  let : ((A.realization.atObject Y).realization.functor ⋙
      (boundedConstructible (CondensedERealization.Coefficient E Y.scheme)).ι).CommShift ℤ :=
    Functor.CommShift.comp _ _
  let : (rationalSupport l E c A.reduction
      (A.atCompactification X Y f c).integral ⋙
      (A.realization.atObject Y).realization.functor ⋙
      (boundedConstructible (CondensedERealization.Coefficient E Y.scheme)).ι).CommShift ℤ :=
    Functor.CommShift.comp _ _
  let hSX : Prop := NatTrans.CommShift (A.realization.atObject X).scalarExtension.hom ℤ
  let hSY : Prop := NatTrans.CommShift (A.realization.atObject Y).scalarExtension.hom ℤ
  let hReal : Prop := NatTrans.CommShift (A.atCompactification X Y f c).realization.hom ℤ
  exact hI ∧ hRX ∧ hRY ∧ hLimit ∧ hAlpha ∧ hSX ∧ hSY ∧ hReal ∧
        ∀ (K : CondensedERealization.Integral l E X.scheme) (n : ℤ),
          HEq ((Q.commShiftIso n).hom.app
              (ScalarLocalization.mk K))
            ((1 : Localization.Away (pbcUniformizer l E)) ⊗ₜ[PbcIntegralRing l E]
              (I.commShiftIso n).hom.app K)

attribute [local irreducible] shiftCoherentClauses

/-- Shift structures of the support, realization, reduction and their constituent functors,
with the stipulated counit and scalar comparison equations.
Source: blueprint proof Step 17; Bhatt--Scholze 6.8.15
(blueprint: lem-pur-compact-support-condensed-realization). -/
structure ShiftCoherentWitness (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (A : CoefficientData l E k)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))]
    [IsNoetherian X.scheme] [IsNoetherian Y.scheme]
    [Fact (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Y.scheme ≤ n)]
    [Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x))]
    [Fact (∀ y : Y.scheme, IsUnit (l : Y.scheme.presheaf.stalk y))]
    [ObjectProperty.IsTriangulated
      (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E))]
    [ObjectProperty.IsTriangulated
      (PbcIsBoundedConstructibleComplete Y.scheme (pbcIntegralDatum l E))]
    (c : Compactification f) where
  sI : (integralSupport l E c A.reduction
      (A.atCompactification X Y f c).integral).CommShift ℤ
  sQ : (rationalSupport l E c A.reduction
      (A.atCompactification X Y f c).integral).CommShift ℤ
  sX : (A.realization.atObject X).realization.functor.CommShift ℤ
  sY : (A.realization.atObject Y).realization.functor.CommShift ℤ
  sRX : (A.reduction X.scheme).reduction.CommShift ℤ
  sRY : (A.reduction Y.scheme).reduction.CommShift ℤ
  sLX : (coefficientSequenceLimit l E X.scheme).CommShift ℤ
  sLY : (coefficientSequenceLimit l E Y.scheme).CommShift ℤ
  sPX : (purCoefficientModel l E X.scheme).functor.CommShift ℤ
  sPY : (purCoefficientModel l E Y.scheme).functor.CommShift ℤ
  sS : (systemSupport l E c).CommShift ℤ
  sVX : (pbcRationalization X.scheme (pbcIntegralDatum l E)
    (pbcUniformizer l E)).CommShift ℤ
  sVY : (pbcRationalization Y.scheme (pbcIntegralDatum l E)
    (pbcUniformizer l E)).CommShift ℤ
  clauses : shiftCoherentClauses l k E A X Y f c sI sQ sX sY sRX sRY
    sLX sLY sPX sPY sS sVX sVY

/-- Existence of compatible integral, rational, realization and reduction shifts.
Source: blueprint proof Step 17; Bhatt--Scholze 6.8.15
(blueprint: lem-pur-compact-support-condensed-realization). -/
def IsShiftCoherent (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (A : CoefficientData l E k)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f) : Prop :=
  letI := base_noetherian k X
  letI := base_noetherian k Y
  letI : Fact (∃ n : ℕ, topologicalKrullDim X.scheme ≤ n) := ⟨base_dimension k X⟩
  letI : Fact (∃ n : ℕ, topologicalKrullDim Y.scheme ≤ n) := ⟨base_dimension k Y⟩
  letI : Fact (∀ x : X.scheme, IsUnit (l : X.scheme.presheaf.stalk x)) :=
    ⟨base_primeUnit l k X⟩
  letI : Fact (∀ y : Y.scheme, IsUnit (l : Y.scheme.presheaf.stalk y)) :=
    ⟨base_primeUnit l k Y⟩
  letI := pbcIntegralTriangulated l E X.scheme (base_dimension k X) (base_primeUnit l k X)
  letI := pbcIntegralTriangulated l E Y.scheme (base_dimension k Y) (base_primeUnit l k Y)
  Nonempty (ShiftCoherentWitness l k E A X Y f c)

attribute [local irreducible] IsShiftCoherent

/-- Simultaneous compact-support realizations and their specified finite-coefficient
and refinement composition laws. All functors and refinement arrows used below were
constructed above from the recorded dependency operations.
Source: blueprint proof Steps 1--17
(blueprint: lem-pur-compact-support-condensed-realization). -/
structure ComparisonFamilyCore where
  coefficient : ∀
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], CoefficientData l E k
  shifts : ∀
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f),
    IsShiftCoherent l k E (coefficient E) X Y f c
  finite : ∀
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (F : Type u) [NormedField F] [NormedAlgebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f),
    FiniteComparison l E F i k (coefficient E) (coefficient F) X Y f c
  refinement : ∀
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))]
    {c d : Compactification f} (r : c.Refinement d),
    RefinementCoherence l E k (coefficient E) X Y f r

/-- Scalar identity for the specified integral coefficient comparisons.
Source: blueprint proof Steps 9--17
(blueprint: lem-pur-compact-support-condensed-realization). -/
def IsScalarIdentity (C : ComparisonFamilyCore l k) : Prop :=
  ∀
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f)
    (K : CondensedERealization.Integral l E X.scheme),
    (C.finite E E (AlgHom.id ℚ_[l] E) X Y f c).comparison.hom.app K ≫
        (integralSupport l E c (C.coefficient E).reduction
          ((C.coefficient E).atCompactification X Y f c).integral).map
            ((integralScalarId l E k X).hom.app K) =
      (integralScalarId l E k Y).hom.app
        ((integralSupport l E c (C.coefficient E).reduction
          ((C.coefficient E).atCompactification X Y f c).integral).obj K)

/-- Scalar composition for the specified integral coefficient comparisons.
Source: blueprint proof Steps 9--17
(blueprint: lem-pur-compact-support-condensed-realization). -/
def IsScalarComposition (C : ComparisonFamilyCore l k) : Prop :=
  ∀
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (F : Type u) [NormedField F] [NormedAlgebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F]
    (G : Type u) [NormedField G] [NormedAlgebra ℚ_[l] G]
    [FiniteDimensional ℚ_[l] G]
    (i : E →ₐ[ℚ_[l]] F) (j : F →ₐ[ℚ_[l]] G)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f)
    (K : CondensedERealization.Integral l E X.scheme),
    (integralScalar l F G j k Y).map
        ((C.finite E F i X Y f c).comparison.hom.app K) ≫
        (C.finite F G j X Y f c).comparison.hom.app ((integralScalar l E F i k X).obj K) ≫
        (integralSupport l G c (C.coefficient G).reduction
          ((C.coefficient G).atCompactification X Y f c).integral).map
            ((integralScalarComp l E F G i j k X).hom.app K) =
      (integralScalarComp l E F G i j k Y).hom.app
          ((integralSupport l E c (C.coefficient E).reduction
            ((C.coefficient E).atCompactification X Y f c).integral).obj K) ≫
        (C.finite E G (j.comp i) X Y f c).comparison.hom.app K

/-- Scalar refinement for the specified integral coefficient comparisons.
Source: blueprint proof Steps 9--17
(blueprint: lem-pur-compact-support-condensed-realization). -/
def IsScalarRefinement (C : ComparisonFamilyCore l k) : Prop :=
  ∀
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (F : Type u) [NormedField F] [NormedAlgebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F)
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))]
    {c d : Compactification f} (r : c.Refinement d)
    (K : CondensedERealization.Integral l E X.scheme),
    (integralScalar l E F i k Y).map
        ((integralRefinement l E k (C.coefficient E) X Y f r).app K) ≫
        (C.finite E F i X Y f c).comparison.hom.app K =
      (C.finite E F i X Y f d).comparison.hom.app K ≫
        (integralRefinement l F k (C.coefficient F) X Y f r).app
          ((integralScalar l E F i k X).obj K)

attribute [local irreducible] IsScalarIdentity IsScalarComposition IsScalarRefinement

/-- The simultaneous family with its identity, coefficient-tower and refinement equations.
Source: blueprint proof Steps 1--17
(blueprint: lem-pur-compact-support-condensed-realization). -/
structure ComparisonFamily extends ComparisonFamilyCore l k where
  scalar_identity : IsScalarIdentity l k toComparisonFamilyCore
  scalar_composition : IsScalarComposition l k toComparisonFamilyCore
  scalar_refinement : IsScalarRefinement l k toComparisonFamilyCore

/-- The component equation underlying refinement composition.
Source: Stacks 07A7 and 0F7B; the component form is the strict-system calculation.
(blueprint: lem-pur-compact-support-condensed-realization).
(blueprint: lem-pur-compact-support-condensed-realization-system-refinement-comp-component).
Proof: paste the two clopen-section open squares and use the proper compositor
cocycle; this is the component calculation before natural-transformation extensionality. -/
theorem systemRefinement_comp_component (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e)
    (M : coefficientSequenceDerived.{u, u} l E X.scheme) :
    (systemRefinement l E k X Y f (r.comp s)).app M =
      (systemRefinement l E k X Y f s ≫
        systemRefinement l E k X Y f r).app M := by
  let := compactification_open_quasiCompact k X Y f c
  let := compactification_open_quasiCompact k X Y f d
  let := compactification_open_quasiCompact k X Y f e
  unfold systemRefinement
  with_unfolding_all
    exact SemilinearProperOpen.supportRefinement_comp_app
      (quotientRings l E) (quotientMaps l E) c.i c.g d.i d.g e.i e.g r.hom s.hom
      (r.i_hom.trans (Category.id_comp _).symm)
      (s.i_hom.trans (Category.id_comp _).symm)
      ((r.comp s).i_hom.trans (Category.id_comp _).symm)
      r.hom_g s.hom_g (r.comp s).hom_g M

/-- Refinement composition holds before evaluation and before total limit.
Source: blueprint Step 15; Stacks 07A7 and 0F7B
(blueprint: lem-pur-compact-support-condensed-realization).
Proof: the component calculation is natural in the system object, so extensionality
packages it as equality of natural transformations. -/
theorem systemRefinement_comp (X Y : CondensedERealization.Base k)
    (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e) :
    systemRefinement l E k X Y f (r.comp s) =
      systemRefinement l E k X Y f s ≫ systemRefinement l E k X Y f r := by
  apply NatTrans.ext
  funext M
  exact systemRefinement_comp_component l E k X Y f r s M

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

-- Keep the properness and site-size proofs in the field type. Abstracting these
-- into auxiliary declarations forces the kernel to unfold the large mate construction.
set_option backward.proofsInPublic true in
section SystemCompositionProof
set_option backward.proofsInPublic true
attribute [local instance 2000] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local instance 2000] SemilinearProperOpen.derived
attribute [local irreducible] WeilConjectures.SemilinearSections.moduleAbelian

end SystemCompositionProof

section OmegaRefinementProof

attribute [local irreducible] fieldProperOpen fieldOpenAdjunction fieldPushComp
  Functor.rightDerivedFunctor CondensedRing.derivedUpperStarLowerStarAdjunction
  CondensedRing.leftDerivedUpperStarComp

attribute [local instance 2000] fieldSheafAbelian
  fieldSheafGrothendieck fieldSheafBigColimits fieldSheafCoequalizers
  fieldSheafMonoidalPreadditive fieldModuleAbelian fieldModuleGrothendieck
  fieldModuleKInjectiveResolutions fieldModuleDerivedCategory fieldModuleColimits
  fieldModuleBigColimits fieldSheafFlatResolution fieldModuleFlatResolution
  fieldModuleCountableCoproducts fieldModuleIntegerColimits fieldModuleIntegerExactColimits
  fieldTensorColimits fieldTensorColimitsRight fieldGradedTensor fieldGradedFour
  fieldGradedLeft fieldGradedRight fieldExtendScalarsKFlat

end OmegaRefinementProof

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures

end WeilConjectures
