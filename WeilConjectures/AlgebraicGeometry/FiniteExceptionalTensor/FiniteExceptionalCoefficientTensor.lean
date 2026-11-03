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
public import WeilConjectures.AlgebraicGeometry.FiniteExceptionalTensor.FiniteExceptionalScalarProjectionSquare
public import WeilConjectures.AlgebraicGeometry.FiniteExceptionalTensor.FiniteExceptionalTensorDomains
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparison

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

/-- The dualizing object is the specified restricted right adjoint on the constant unit.
Source: blueprint (3), Tensor map, omega_R = G_R R_Y.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
abbrev omega (A : Type u) [CommRing A] {X Y : Scheme.{u}}
    (G : C A Y ⥤ C A X) (hI : ctf A Y (𝟙_ (D A Y))) : D A X :=
  (G.obj ⟨𝟙_ (D A Y), hI⟩).obj

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

/-- The exceptional tensor map is the inverse-projection/counit transpose, including
its final ordinary right unitor. Its domain proof records only membership in Dctf.
Source: blueprint (3), Tensor map, defining transpose of tau.
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def exceptionalTensor (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hP : ∀ M : C A X, ctf A Y ((support A c).obj M.obj))
    (G : C A Y ⥤ C A X) (adj : smallSupport A c hP ⊣ G)
    (hI : ctf A Y (𝟙_ (D A Y))) (K : C A Y)
    (hD : ctf A X ((pull A f).obj K.obj ⊗ omega A G hI))
    (hπ : IsIso (projection A c K.obj (omega A G hI))) :
    (pull A f).obj K.obj ⊗ omega A G hI ⟶ (G.obj K).obj :=
  letI := hπ
  transpose A c hP G adj ⟨(pull A f).obj K.obj ⊗ omega A G hI, hD⟩ K
    (inv (projection A c K.obj (omega A G hI)) ≫
      (𝟙 K.obj ⊗ₘ counit A c hP G adj ⟨𝟙_ (D A Y), hI⟩) ≫ (ρ_ K.obj).hom)

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

namespace AlgebraicGeometry.ProEtale.FiniteExceptionalTensor

private theorem counit_transpose (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hP : ∀ M : C A X, ctf A Y ((support A c).obj M.obj))
    (G : C A Y ⥤ C A X) (adj : smallSupport A c hP ⊣ G)
    (M : C A X) (K : C A Y) (v : (support A c).obj M.obj ⟶ K.obj) :
    (support A c).map (transpose A c hP G adj M K v) ≫ counit A c hP G adj K = v := by
  have h := (adj.homEquiv M K).symm_apply_apply (ObjectProperty.homMk v)
  rw [Adjunction.homEquiv_counit] at h
  exact congrArg (fun q ↦ q.hom) h

private theorem counit_injective (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (hP : ∀ M : C A X, ctf A Y ((support A c).obj M.obj))
    (G : C A Y ⥤ C A X) (adj : smallSupport A c hP ⊣ G)
    (M : C A X) (K : C A Y) (v w : M.obj ⟶ (G.obj K).obj)
    (h : (support A c).map v ≫ counit A c hP G adj K =
      (support A c).map w ≫ counit A c hP G adj K) : v = w := by
  have h' : (adj.homEquiv M K).symm (ObjectProperty.homMk v) =
      (adj.homEquiv M K).symm (ObjectProperty.homMk w) := by
    apply ObjectProperty.hom_ext
    rw [Adjunction.homEquiv_counit]
    exact h
  exact congrArg (fun q ↦ q.hom) ((adj.homEquiv M K).symm.injective h')

private theorem compactComparison_naturality
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : scalar φ X ⊣ restrict φ X) (aY : scalar φ Y ⊣ restrict φ Y)
    {M N : D A X} (v : M ⟶ N) :
    (scalar φ Y).map ((support A c).map v) ≫ compactComparison φ c aX aY N =
      compactComparison φ c aX aY M ≫ (support B c).map ((scalar φ X).map v) := by
  apply (aY.homEquiv _ _).injective
  unfold compactComparison
  rw [aY.homEquiv_naturality_left, aY.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hn := aX.unit.naturality v
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← (support A c).map_comp_assoc, hn,
    (support A c).map_comp, Category.assoc]
  simpa only [Category.assoc, Functor.comp_map] using
    congrArg ((support A c).map (aX.unit.app M) ≫ ·)
    ((compactSupportRestrictionIso (RingHom.ulift.{u + 1, u + 1} φ) c).hom.naturality
      ((scalar φ X).map v))

private theorem transpose_tensor_naturality
    {C₀ D₀ : Type*} [Category C₀] [Category D₀]
    [MonoidalCategory C₀] [MonoidalCategory D₀]
    {S : C₀ ⥤ D₀} {R : D₀ ⥤ C₀} (a : S ⊣ R)
    (r : ∀ K M : D₀, R.obj K ⊗ R.obj M ⟶ R.obj (K ⊗ M))
    (hn : ∀ {K K' M M' : D₀} (v : K ⟶ K') (w : M ⟶ M'),
      (R.map v ⊗ₘ R.map w) ≫ r K' M' = r K M ≫ R.map (v ⊗ₘ w))
    {K K' M M' : C₀} (v : K ⟶ K') (w : M ⟶ M') :
    S.map (v ⊗ₘ w) ≫ (a.homEquiv _ _).symm
        ((a.unit.app K' ⊗ₘ a.unit.app M') ≫ r (S.obj K') (S.obj M')) =
      (a.homEquiv _ _).symm
        ((a.unit.app K ⊗ₘ a.unit.app M) ≫ r (S.obj K) (S.obj M)) ≫
        (S.map v ⊗ₘ S.map w) := by
  apply (a.homEquiv _ _).injective
  simp only [a.homEquiv_naturality_left, a.homEquiv_naturality_right,
    Functor.id_obj, Equiv.apply_symm_apply]
  have hv := a.unit.naturality v
  have hw := a.unit.naturality w
  dsimp only [Functor.id_map, Functor.comp_map] at hv hw
  rw [tensorHom_comp_tensorHom_assoc, hv, hw,
    ← tensorHom_comp_tensorHom_assoc, Category.assoc]
  congr 1
  exact hn (S.map v) (S.map w)

private theorem scalarTensor_naturality
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) (a : scalar φ T ⊣ restrict φ T)
    {K K' M M' : D A T} (v : K ⟶ K') (w : M ⟶ M') :
    (scalar φ T).map (v ⊗ₘ w) ≫ scalarTensor φ T a K' M' =
      scalarTensor φ T a K M ≫ ((scalar φ T).map v ⊗ₘ (scalar φ T).map w) := by
  exact transpose_tensor_naturality a _
    (Etale.scalarRestrictionDerivedTensorData
      (Sheaf.restrictScalars.{u + 1, u, u + 1} (ProEt.topology T)
        (RingHom.ulift.{u + 1, u + 1} φ))
      (sheafComposeLaxMonoidal (ProEt.topology T)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (RingHom.ulift.{u + 1, u + 1} φ)))).naturality v w

private theorem ordered_projection_naturality
    {C₀ D₀ : Type*} [Category C₀] [Category D₀]
    [MonoidalCategory C₀] [MonoidalCategory D₀]
    [BraidedCategory C₀] [BraidedCategory D₀]
    (P : C₀ ⥤ D₀) (F : D₀ ⥤ C₀) (K : D₀)
    (p : ∀ M : C₀, P.obj M ⊗ K ⟶ P.obj (M ⊗ F.obj K))
    {M N : C₀} (v : M ⟶ N)
    (h : (P.map v ⊗ₘ 𝟙 K) ≫ p N = p M ≫ P.map (v ⊗ₘ 𝟙 (F.obj K))) :
    (𝟙 K ⊗ₘ P.map v) ≫
        (β_ K (P.obj N)).hom ≫ p N ≫ P.map (β_ N (F.obj K)).hom =
      ((β_ K (P.obj M)).hom ≫ p M ≫ P.map (β_ M (F.obj K)).hom) ≫
        P.map (𝟙 (F.obj K) ⊗ₘ v) := by
  rw [BraidedCategory.braiding_naturality_assoc, reassoc_of% h]
  simp only [Category.assoc, ← P.map_comp]
  rw [BraidedCategory.braiding_naturality]

private theorem projection_naturality
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : D A Y) {M N : D A X} (v : M ⟶ N) :
    (𝟙 K ⊗ₘ (support A c).map v) ≫ projection A c K N =
      projection A c K M ≫ (support A c).map (𝟙 ((pull A f).obj K) ⊗ₘ v) := by
  let := DerivedCategory.braidedCategory'
    (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
  let := DerivedCategory.braidedCategory'
    (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
  have h := congr_app ((projectionMapOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).naturality v) K
  simp only [NatTrans.comp_app, derivedTensorRightDerivedLowerShriek,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar, Functor.comp_obj,
    Functor.comp_map, Functor.postcompose₂, Functor.whiskeringLeft₂,
    Functor.whiskeringRight, Functor.whiskeringLeft, Functor.whiskerLeft,
    Functor.whiskerRight, Functor.id_obj, Functor.id_map, derivedTensor,
    curriedTensor_map_app, ← tensorHom_id] at h
  change ((support A c).map v ⊗ₘ 𝟙 K) ≫
      ((projectionMapOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).app N).app K =
    ((projectionMapOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).app M).app K ≫
        (support A c).map (v ⊗ₘ 𝟙 ((pull A f).obj K)) at h
  unfold projection braiding
  exact ordered_projection_naturality (support A c) (pull A f) K
    (fun M ↦ ((projectionMapOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).app M).app K) v h

/-- Finite-ring scalar compatibility of the exceptional tensor map. The existential
proofs assert the domains and invertibilities used to define the displayed arrows;
they impose no extra hypotheses on K or on the ring map. Scalar and exceptional
adjunctions are presentations of the specified functors; all comparisons are built
from their units/counits and the normalized restriction/tensor comparisons above.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/sk-lem-sp-reduction-compatibilities.proof.md, (3), Tensor map paragraph.
(blueprint: lem-pur-exceptional-coefficient-comparison).

Proof: The algebraically closed base has finite ell-cohomological dimension. The
finite-coefficient equivalences preserve the intrinsic Dctf domain, tensor, and
compact support, so all asserted domain proofs follow from constructible stability
and finite Tor amplitude. The projection theorem and compact-support scalar
comparison give their asserted invertibilities. The canonical restriction mate for
compact support is the proper-counit/open-tensor comparison b, by the proper Hom
bijection and the open normalization. Scalar projection coherence, with symmetry
putting K first, gives the projection square for b, and its inverse square. Transpose
both sides of the claimed identity under P_B adjoint to G_B. The defining equation
of comparison and naturality of b identify the left transpose with S_Y(d_A) followed
by inverse b at F_A K tensor omega_A. Counit naturality at scalarUnit identifies
the transpose involving delta with the inverse B-projection followed by id tensor
(scalarUnit after S_Y of the A-counit after inverse b at omega_A), and the unitor.
Insert the inverse scalar projection square and apply scalar tensor naturality at
the A-counit and scalar-unit coherence. The two transposes agree. Injectivity of
the restricted Hom bijection proves the displayed equality. No inverse of c is used. -/
theorem exceptional_coefficient_tensor_comparison
    (D₀ : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) (_hell : ell.Prime) (_hellp : ell ≠ D₀.p)
    (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, 1 ≤ n ∧ ∀ r : A, (ell ^ n) • r = 0)
    (_hB : ∃ n : ℕ, 1 ≤ n ∧ ∀ r : B, (ell ^ n) • r = 0)
    (φ : A →+* B) {X Y : Scheme.{u}}
    [X.Over (Spec (.of D₀.k))] [Y.Over (Spec (.of D₀.k))]
    [IsSeparated (X ↘ Spec (.of D₀.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D₀.k))]
    [QuasiCompact (X ↘ Spec (.of D₀.k))]
    [IsSeparated (Y ↘ Spec (.of D₀.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D₀.k))]
    [QuasiCompact (Y ↘ Spec (.of D₀.k))]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f]
    (c : Compactification f) [c.Z.Over (Spec (.of D₀.k))]
    [IsSeparated (c.Z ↘ Spec (.of D₀.k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of D₀.k))]
    [QuasiCompact (c.Z ↘ Spec (.of D₀.k))]
    [c.i.IsOver (Spec (.of D₀.k))] [c.g.IsOver (Spec (.of D₀.k))]
    (aX : scalar φ X ⊣ restrict φ X) (aY : scalar φ Y ⊣ restrict φ Y)
    (hPA : ∀ M : C A X, ctf A Y ((support A c).obj M.obj))
    (hPB : ∀ M : C B X, ctf B Y ((support B c).obj M.obj))
    (GA : C A Y ⥤ C A X) (GB : C B Y ⥤ C B X)
    (adjA : smallSupport A c hPA ⊣ GA) (adjB : smallSupport B c hPB ⊣ GB)
    (K : C A Y) :
    ∃ (hIA : ctf A Y (𝟙_ (D A Y))) (hIB : ctf B Y (𝟙_ (D B Y)))
      (hSK : ctf B Y ((scalar φ Y).obj K.obj))
      (hSC : ctf B X ((scalar φ X).obj (GA.obj K).obj))
      (hSI : ctf B Y ((scalar φ Y).obj (𝟙_ (D A Y))))
      (hSω : ctf B X ((scalar φ X).obj (omega A GA hIA)))
      (hDA : ctf A X ((pull A f).obj K.obj ⊗ omega A GA hIA))
      (hDB : ctf B X ((pull B f).obj ((scalar φ Y).obj K.obj) ⊗ omega B GB hIB))
      (hπA : IsIso (projection A c K.obj (omega A GA hIA)))
      (hπB : IsIso (projection B c ((scalar φ Y).obj K.obj) (omega B GB hIB)))
      (hbK : IsIso (compactComparison φ c aX aY (GA.obj K).obj))
      (hbI : IsIso (compactComparison φ c aX aY (omega A GA hIA)))
      (_hσ : IsIso (sigma φ f aX aY K.obj (omega A GA hIA)))
      (_hu : IsIso (scalarUnit φ Y aY)),
      (scalar φ X).map (exceptionalTensor A c hPA GA adjA hIA K hDA hπA) ≫
          comparison φ c aX aY hPA hPB GA GB adjA adjB K hSC hSK hbK =
        sigma φ f aX aY K.obj (omega A GA hIA) ≫
          (𝟙 ((pull B f).obj ((scalar φ Y).obj K.obj)) ⊗ₘ
            (comparison φ c aX aY hPA hPB GA GB adjA adjB
              ⟨𝟙_ (D A Y), hIA⟩ hSω hSI hbI ≫
              (GB.map (ObjectProperty.homMk (scalarUnit φ Y aY))).hom)) ≫
          exceptionalTensor B c hPB GB adjB hIB ⟨(scalar φ Y).obj K.obj, hSK⟩ hDB hπB := by
  obtain ⟨hIA, hIB, hSK, hSC, hSI, hSω, hDA, hDB, hπA, hπB, hbK, hbI,
    hσ, hu, hSD, hbD⟩ := exceptional_tensor_domains D₀ ell _hell _hellp A B _hA _hB
      φ f d c aX aY hPA hPB GA GB adjA adjB K
  refine ⟨hIA, hIB, hSK, hSC, hSI, hSω, hDA, hDB, hπA, hπB, hbK, hbI, hσ, hu, ?_⟩
  let := hπA
  let := hπB
  let := hbK
  let := hbI
  let := hbD
  obtain ⟨hproj, hunit⟩ := finite_exceptional_scalar_projection_square φ c aX aY
  let WA := omega A GA hIA
  let WB := omega B GB hIB
  let DA := (pull A f).obj K.obj ⊗ WA
  let KB : C B Y := ⟨(scalar φ Y).obj K.obj, hSK⟩
  let IA : C A Y := ⟨𝟙_ (D A Y), hIA⟩
  let IB : C B Y := ⟨𝟙_ (D B Y), hIB⟩
  let SI : C B Y := ⟨(scalar φ Y).obj (𝟙_ (D A Y)), hSI⟩
  let δ : (scalar φ X).obj WA ⟶ WB :=
    comparison φ c aX aY hPA hPB GA GB adjA adjB IA hSω hSI hbI ≫
      (GB.map (ObjectProperty.homMk (scalarUnit φ Y aY))).hom
  let dA : (support A c).obj DA ⟶ K.obj :=
    inv (projection A c K.obj WA) ≫
      (𝟙 K.obj ⊗ₘ counit A c hPA GA adjA IA) ≫ (ρ_ K.obj).hom
  let dB : (support B c).obj ((pull B f).obj KB.obj ⊗ WB) ⟶ KB.obj :=
    inv (projection B c KB.obj WB) ≫
      (𝟙 KB.obj ⊗ₘ counit B c hPB GB adjB IB) ≫ (ρ_ KB.obj).hom
  have htA : (support A c).map
      (exceptionalTensor A c hPA GA adjA hIA K hDA hπA) ≫
        counit A c hPA GA adjA K = dA := by
    unfold exceptionalTensor
    exact counit_transpose A c hPA GA adjA _ _ _
  have htB : (support B c).map
      (exceptionalTensor B c hPB GB adjB hIB KB hDB hπB) ≫
        counit B c hPB GB adjB KB = dB := by
    unfold exceptionalTensor
    exact counit_transpose B c hPB GB adjB _ _ _
  have hcK : (support B c).map
      (comparison φ c aX aY hPA hPB GA GB adjA adjB K hSC hSK hbK) ≫
        counit B c hPB GB adjB KB =
      inv (compactComparison φ c aX aY (GA.obj K).obj) ≫
        (scalar φ Y).map (counit A c hPA GA adjA K) := by
    unfold comparison
    exact counit_transpose B c hPB GB adjB _ _ _
  have hcI : (support B c).map
      (comparison φ c aX aY hPA hPB GA GB adjA adjB IA hSω hSI hbI) ≫
        counit B c hPB GB adjB SI =
      inv (compactComparison φ c aX aY WA) ≫
        (scalar φ Y).map (counit A c hPA GA adjA IA) := by
    unfold comparison
    exact counit_transpose B c hPB GB adjB _ _ _
  have hcu : (support B c).map
      (GB.map (ObjectProperty.homMk (scalarUnit φ Y aY))).hom ≫
        counit B c hPB GB adjB IB =
      counit B c hPB GB adjB SI ≫ scalarUnit φ Y aY := by
    exact congrArg (fun q ↦ q.hom)
      (adjB.counit.naturality
        (ObjectProperty.homMk (X := SI) (Y := IB) (scalarUnit φ Y aY)))
  have hd : compactComparison φ c aX aY WA ≫
      (support B c).map δ ≫ counit B c hPB GB adjB IB =
      (scalar φ Y).map (counit A c hPA GA adjA IA) ≫ scalarUnit φ Y aY := by
    dsimp only [δ]
    rw [Functor.map_comp, Category.assoc, hcu, ← Category.assoc
      ((support B c).map (comparison φ c aX aY hPA hPB GA GB adjA adjB
        IA hSω hSI hbI)), hcI]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  apply counit_injective B c hPB GB adjB
    ⟨(scalar φ X).obj DA, hSD⟩ KB
  rw [Functor.map_comp, Category.assoc, hcK]
  have hn := compactComparison_naturality φ c aX aY
    (exceptionalTensor A c hPA GA adjA hIA K hDA hπA)
  have hn' : (support B c).map
      ((scalar φ X).map (exceptionalTensor A c hPA GA adjA hIA K hDA hπA)) ≫
        inv (compactComparison φ c aX aY (GA.obj K).obj) =
      inv (compactComparison φ c aX aY DA) ≫
        (scalar φ Y).map ((support A c).map
          (exceptionalTensor A c hPA GA adjA hIA K hDA hπA)) := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact hn.symm
  rw [← Category.assoc, hn', Category.assoc, ← Functor.map_comp, htA]
  change inv (compactComparison φ c aX aY DA) ≫ (scalar φ Y).map dA =
    (support B c).map (sigma φ f aX aY K.obj WA ≫
      (𝟙 ((pull B f).obj KB.obj) ⊗ₘ δ) ≫
        exceptionalTensor B c hPB GB adjB hIB KB hDB hπB) ≫
      counit B c hPB GB adjB KB
  conv_rhs => rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc, htB]
  apply (cancel_epi (compactComparison φ c aX aY DA)).1
  simp only [IsIso.hom_inv_id_assoc]
  apply (cancel_epi ((scalar φ Y).map (projection A c K.obj WA))).1
  dsimp only [dA, dB]
  conv_lhs =>
    rw [Functor.map_comp, Functor.map_comp]
    rw [← Functor.map_comp_assoc, IsIso.hom_inv_id]
  slice_rhs 1 3 => rw [hproj K.obj WA]
  slice_rhs 3 4 => rw [← projection_naturality B c KB.obj δ]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [Category.id_comp]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]
  rw [hd]
  simp only [Category.comp_id]
  have hs : (𝟙 KB.obj ⊗ₘ
      ((scalar φ Y).map (counit A c hPA GA adjA IA) ≫ scalarUnit φ Y aY)) =
      (𝟙 KB.obj ⊗ₘ (scalar φ Y).map (counit A c hPA GA adjA IA)) ≫
        (𝟙 KB.obj ⊗ₘ scalarUnit φ Y aY) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  rw [hs, Category.assoc]
  have he0 := scalarTensor_naturality φ Y aY (𝟙 K.obj)
    (counit A c hPA GA adjA IA)
  have he :
      (scalar φ Y).map (𝟙 K.obj ⊗ₘ counit A c hPA GA adjA IA) ≫
          scalarTensor φ Y aY K.obj IA.obj =
        scalarTensor φ Y aY K.obj ((support A c).obj WA) ≫
          (𝟙 KB.obj ⊗ₘ (scalar φ Y).map (counit A c hPA GA adjA IA)) := by
    rw [(scalar φ Y).map_id] at he0
    exact he0
  slice_rhs 1 2 => rw [← he]
  simp only [Category.assoc]
  rw [hunit]
  rw [(scalar φ Y).map_id, Category.id_comp]

end AlgebraicGeometry.ProEtale.FiniteExceptionalTensor
