/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingCompactSupportProjectionMap
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparisonMap
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageBoundedBelow
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalBounds
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
public import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
public import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
public import WeilConjectures.AlgebraicGeometry.EtaleSiteCechComplexComparison
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorUpperBound
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.DerivedScalarRestrictionTensor
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Finite coefficient compatibility of the exceptional tensor map

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, (3), Tensor map paragraph.
(blueprint: lem-pur-exceptional-coefficient-comparison).

We use the fixed-scalar presentation of ordinary constant-ring pro-etale modules.
Scalar extension is the recorded functor conjugated by the canonical intrinsic
realization equivalences. Its adjunction to exact scalar restriction specifies
all the comparisons below. Exceptional adjunctions are restricted to Dctf.

## Main definitions

* `scalar`, `support`, `pull`: the recorded operations in ordinary coordinates.
* `compactComparison`, `comparison`: the specified compact-support and exceptional maps.
* `exceptionalTensor`, `sigma`: the inverse-projection transpose and scalar balancing.

## Main statements

* `exceptional_coefficient_tensor_comparison`: the finite-ring compatibility equation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

attribute [local instance 2000] CommRing.toRing isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat finiteProjection_upperFlat

namespace AlgebraicGeometry.ProEtale.FiniteExceptionalTensor

/-- The existing ordinary finite-coefficient presentation.
Source: finite-discrete/ordinary equivalence; blueprint (3), Tensor map.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
abbrev D (A : Type u) [CommRing A] (T : Scheme.{u}) :=
  DerivedCategory.{u + 1} (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))

/-- The recorded bounded intrinsically constructible finite-Tor property.
Source: finite-discrete/ordinary equivalence; blueprint (3), Tensor map.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
abbrev ctf (A : Type u) [CommRing A] (T : Scheme.{u}) :=
  FiniteDiscreteOrdinary.ordinaryCtf A T

/-- Dctf is a full subcategory, so the final equality is an ordinary derived morphism.
Source: blueprint (3), Tensor map.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
abbrev C (A : Type u) [CommRing A] (T : Scheme.{u}) := (ctf A T).FullSubcategory

/-- The actual scalar functor in fixed-scalar coordinates, with its target ring action.
Source: det-sp-scalar-extension-functor and the finite-coefficient equivalence.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def scalar {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) : D A T ⥤ D B T :=
  (sfIntrinsicDerivedEquivalence T A).functor ⋙ scalarExtensionFunctor φ T ⋙
    (sfIntrinsicDerivedEquivalence T B).inverse

/-- Exact scalar restriction in the same ordinary coordinates.
Source: Stacks 06YY; blueprint (3), Tensor map.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
abbrev restrict {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) : D B T ⥤ D A T :=
  Sheaf.derivedRestrictScalars.{u} (ProEt.topology T) (RingHom.ulift.{u + 1, u + 1} φ)

/-- The coefficient-independent proper/open compact-support functor.
Source: det-sp-reduction-direct-image; blueprint (3), Tensor map.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
abbrev support (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : D A X ⥤ D A Y :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1} A)) c

/-- The specified geometric derived pullback.
Source: def-weil-pbc-proetale-operations, in fixed-scalar coordinates.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
abbrev pull (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    D A Y ⥤ D A X :=
  (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).leftDerivedFunctor

/-- Compact support restricted to the existing Dctf property.
Source: sk-prop-sf-rf-shriek-preservation; blueprint (3), domains.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def smallSupport (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (h : ∀ M : C A X, ctf A Y ((support A c).obj M.obj)) : C A X ⥤ C A Y :=
  (ctf A Y).lift ((ctf A X).ι ⋙ support A c) h

/-- The existing Koszul braiding of the derived tensor, named without a local instance.
Source: native derived symmetric monoidal structure; blueprint (3), ordered projection.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def braiding (A : Type u) [CommRing A] (T : Scheme.{u}) (K M : D A T) :
    K ⊗ M ≅ M ⊗ K :=
  @BraidedCategory.braiding (D A T) _ _ (DerivedCategory.braidedCategory' _) K M

/-- The ordered projection map, with K first, using the actual proper/open projection.
Source: lem-sp-finite-ring-compact-support-projection; blueprint (3), Tensor map.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def projection (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : D A Y) (M : D A X) :
    K ⊗ (support A c).obj M ⟶ (support A c).obj ((pull A f).obj K ⊗ M) :=
  (braiding A Y K ((support A c).obj M)).hom ≫
    ((projectionMapOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).app M).app K ≫
    (support A c).map (braiding A X M ((pull A f).obj K)).hom

set_option maxHeartbeats 1600000 in
-- Comparing the canonical derived tensor and localization instances needs more elaboration.
/-- The normalized scalar tensor map is the transpose of tensoring the two scalar units
and applying the canonical derived balancing map for exact restriction. This constructs
it for nonflat ring maps too, without assuming that restriction preserves K-flatness.
Source: Stacks 07A4; lem-fix-condensed-scalar-projection-coherence, tensor comparison.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def scalarTensor {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) (a : scalar φ T ⊣ restrict φ T)
    (K M : D A T) :
    (scalar φ T).obj (K ⊗ M) ⟶ (scalar φ T).obj K ⊗ (scalar φ T).obj M :=
  (a.homEquiv _ _).symm
    ((a.unit.app K ⊗ₘ a.unit.app M) ≫
      (Etale.scalarRestrictionDerivedTensorData
        (Sheaf.restrictScalars.{u + 1, u, u + 1} (ProEt.topology T)
          (RingHom.ulift.{u + 1, u + 1} φ))
        (sheafComposeLaxMonoidal (ProEt.topology T)
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
            (RingHom.ulift.{u + 1, u + 1} φ)))).map
        ((scalar φ T).obj K) ((scalar φ T).obj M))

set_option maxHeartbeats 1600000 in
-- Comparing the canonical derived tensor and localization instances needs more elaboration.
/-- Scalar-unit multiplication, defined by the ordinary ring map in degree zero and
its canonical exact localization factor.
Source: Stacks 03EL and 06YY; blueprint (3), u_Y.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def scalarUnit {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) (a : scalar φ T ⊣ restrict φ T) :
    (scalar φ T).obj (𝟙_ (D A T)) ⟶ 𝟙_ (D B T) :=
  (a.homEquiv _ _).symm
    (DerivedCategory.Q.map
      ((CochainComplex.singleFunctor _ 0).map
        (@Functor.LaxMonoidal.ε _ _ _ _ _ _
          (Sheaf.restrictScalars.{u + 1, u, u + 1} (ProEt.topology T)
          (RingHom.ulift.{u + 1, u + 1} φ))
          (sheafComposeLaxMonoidal (ProEt.topology T)
            (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (RingHom.ulift.{u + 1, u + 1} φ))))) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (Sheaf.restrictScalars.{u + 1, u, u + 1} (ProEt.topology T)
          (RingHom.ulift.{u + 1, u + 1} φ))
          (ComplexShape.up ℤ) 0).inv.app (𝟙_ _)) ≫
      ((Sheaf.restrictScalars.{u + 1, u, u + 1} (ProEt.topology T)
        (RingHom.ulift.{u + 1, u + 1} φ)).mapDerivedCategoryFactors.inv.app
          ((CochainComplex.singleFunctor _ 0).obj (𝟙_ _))))

/-- Scalar/pullback balancing as the transpose of exact restriction/pullback balancing.
Source: lem-sfb-internal-scalar-pullback-normalization, including its units.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def scalarPull {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aX : scalar φ X ⊣ restrict φ X) (aY : scalar φ Y ⊣ restrict φ Y)
    (K : D A Y) :
    (scalar φ X).obj ((pull A f).obj K) ⟶ (pull B f).obj ((scalar φ Y).obj K) :=
  (aX.homEquiv _ _).symm
    ((pull A f).map (aY.unit.app K) ≫
      (fixedScalarRestrictionPullback (RingHom.ulift.{u + 1, u + 1} φ) f).hom.app
        ((scalar φ Y).obj K))

/-- The specified proper-counit/open-tensor comparison, expressed as the transpose
of the specified exact proper/open restriction comparison. In particular b is not
an arbitrary natural isomorphism supplied as an additional hypothesis.
Source: det-sp-reduction-direct-image; Stacks 0GL5, 0GL6 and 07A6.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def compactComparison {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : scalar φ X ⊣ restrict φ X) (aY : scalar φ Y ⊣ restrict φ Y)
    (M : D A X) :
    (scalar φ Y).obj ((support A c).obj M) ⟶
      (support B c).obj ((scalar φ X).obj M) :=
  (aY.homEquiv _ _).symm
    ((support A c).map (aX.unit.app M) ≫
      (compactSupportRestrictionIso (RingHom.ulift.{u + 1, u + 1} φ) c).hom.app
        ((scalar φ X).obj M))

/-- The existing restricted exceptional counit, read in the ambient derived category.
Source: sk-prop-sf-rf-shriek-preservation, restricted adjunction.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def counit (A : Type u) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (hP : ∀ M : C A X, ctf A Y ((support A c).obj M.obj))
    (G : C A Y ⥤ C A X) (adj : smallSupport A c hP ⊣ G) (K : C A Y) :
    (support A c).obj (G.obj K).obj ⟶ K.obj :=
  (adj.counit.app K).hom

/-- The restricted exceptional Hom bijection, followed by the full inclusion.
Source: sk-prop-sf-rf-shriek-preservation, restricted adjunction.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def transpose (A : Type u) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (hP : ∀ M : C A X, ctf A Y ((support A c).obj M.obj))
    (G : C A Y ⥤ C A X) (adj : smallSupport A c hP ⊣ G)
    (M : C A X) (K : C A Y) (v : (support A c).obj M.obj ⟶ K.obj) :
    M.obj ⟶ (G.obj K).obj :=
  (adj.homEquiv M K (ObjectProperty.homMk v)).hom

/-- The exceptional scalar comparison is precisely the specified counit transpose.
Only b is inverted: there is no assumption of invertibility of c.
Source: blueprint (3), Tensor map; the displayed defining equation for c_K.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def comparison {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : scalar φ X ⊣ restrict φ X) (aY : scalar φ Y ⊣ restrict φ Y)
    (hPA : ∀ M : C A X, ctf A Y ((support A c).obj M.obj))
    (hPB : ∀ M : C B X, ctf B Y ((support B c).obj M.obj))
    (GA : C A Y ⥤ C A X) (GB : C B Y ⥤ C B X)
    (adjA : smallSupport A c hPA ⊣ GA) (adjB : smallSupport B c hPB ⊣ GB)
    (K : C A Y)
    (hSG : ctf B X ((scalar φ X).obj (GA.obj K).obj))
    (hSK : ctf B Y ((scalar φ Y).obj K.obj))
    (hb : IsIso (compactComparison φ c aX aY (GA.obj K).obj)) :
    (scalar φ X).obj (GA.obj K).obj ⟶ (GB.obj ⟨(scalar φ Y).obj K.obj, hSK⟩).obj :=
  letI := hb
  transpose B c hPB GB adjB ⟨(scalar φ X).obj (GA.obj K).obj, hSG⟩
    ⟨(scalar φ Y).obj K.obj, hSK⟩
    (inv (compactComparison φ c aX aY (GA.obj K).obj) ≫
      (scalar φ Y).map (counit A c hPA GA adjA K))

/-- The specified composite scalar tensor/pullback map, with its original B action.
Source: blueprint (3), Tensor map, sigma_K.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def sigma {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aX : scalar φ X ⊣ restrict φ X) (aY : scalar φ Y ⊣ restrict φ Y)
    (K : D A Y) (M : D A X) :
    (scalar φ X).obj ((pull A f).obj K ⊗ M) ⟶
      (pull B f).obj ((scalar φ Y).obj K) ⊗ (scalar φ X).obj M :=
  scalarTensor φ X aX ((pull A f).obj K) M ≫
    (scalarPull φ f aX aY K ⊗ₘ 𝟙 ((scalar φ X).obj M))

set_option maxHeartbeats 1600000 in
-- Comparing the canonical derived tensor and localization instances needs more elaboration.
end AlgebraicGeometry.ProEtale.FiniteExceptionalTensor
