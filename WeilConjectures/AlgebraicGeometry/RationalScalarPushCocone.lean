/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsShortExact
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import Mathlib.CategoryTheory.Monoidal.CommMon_
import WeilConjectures.Algebra.Homology.FilteredColimitsTensor
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization
import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsMixedUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

/-! # The filtered cocone of canonical scalar push mates

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-rational.proof.md, (1)
(blueprint: lem-sfb-rational-scalar-push-cocone).

The helpers retain coefficient maps, ordinary tensor complexes, and the canonical
left-derived counit and right-derived unit computations. Colimits below are taken
in complexes before localization.

## Main definitions

* `coefficientModules`: the actual underlying coefficient-module diagram.
* `scalarComputation`: the flat scalar computation via the left-derived counit.
* `restrictedPush`: the native scalar push mate with its direct-image comparison.
* `sourceFunctor`, `inputFunctor`, `targetFunctor`: compatible complex representatives.

## Main statements

* `rationalScalarPushCocone`: compatibility and both canonical filtered-colimit comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.RationalScalarPush

/-- Commutative condensed coefficients in the existing ring-object encoding.
Source: blueprint coefficient conventions (blueprint: lem-sfb-rational-scalar-push-cocone). -/
abbrev Rings := CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})

/-- The existing internal module category over a pulled-back coefficient ring.
Source: blueprint module conventions (blueprint: lem-sfb-rational-scalar-push-cocone). -/
abbrev Modules (R : Rings.{u}) (Z : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj (CommMon.X R) Z)

variable (R : Rings.{u})

/-- An algebra as an underlying module over the original coefficient ring.
Source: blueprint (1), the modules S_i,Z (blueprint: lem-sfb-rational-scalar-push-cocone). -/
abbrev coefficientModule (A : Under R) (Z : Scheme.{u}) : Modules R Z :=
  (Mod.comap (coefficientMap A.hom.hom.hom Z)).obj
    (Mod.regular (condensedRingObj (CommMon.X A.right) Z))

/-- Commutativity transported through the standard forgetful functor to monoid objects.
Source: Mathlib CommMon.comm (blueprint: lem-sfb-rational-scalar-push-cocone). -/
instance commToMon (A : Rings.{u}) : IsCommMonObj A.toMon.X := CommMon.comm A

/-- The algebra-map square after pullback of coefficients.
Source: blueprint (1) (blueprint: lem-sfb-rational-scalar-push-cocone).
Proof: the Under morphism equation is a followed by b equals the target structure map.
Apply the inverse-image functor from the point and use coefficientMap_comp. -/
theorem coefficientSquare {A B : Under R} (b : A ⟶ B) (Z : Scheme.{u}) :
    coefficientMap A.hom.hom.hom Z ≫ coefficientMap b.right.hom.hom Z =
      coefficientMap B.hom.hom.hom Z := by
  sorry

set_option maxHeartbeats 800000 in
-- These canonical comparisons traverse the derived module functor structures.
/-- The R-linear coefficient map, using restriction-composition and the given ring map.
Source: blueprint (1), b_i tensor 1 (blueprint: lem-sfb-rational-scalar-push-cocone). -/
def coefficientModuleMap {A B : Under R} (b : A ⟶ B) (Z : Scheme.{u}) :
    coefficientModule R A Z ⟶ coefficientModule R B Z :=
  (Mod.comap (coefficientMap A.hom.hom.hom Z)).map
      (Mod.regularToComapRegular (coefficientMap b.right.hom.hom Z)) ≫
    (Mod.comapComp (coefficientMap A.hom.hom.hom Z)
      (coefficientMap b.right.hom.hom Z)).inv.app _ ≫
    (Mod.comapCongr (coefficientSquare R b Z)).hom.app _

/-- The coefficient module maps preserve identities and composition.
Source: blueprint (1), compatible coefficient system
(blueprint: lem-sfb-rational-scalar-push-cocone).
Proof: forget the module actions. Each displayed composite is the original coefficient
ring map, by the restriction-composition formulas. Faithfulness of forgetting modules
and functoriality of coefficientMap prove the two equations. -/
theorem coefficientModuleMap_laws (Z : Scheme.{u}) :
    (∀ A : Under R, coefficientModuleMap R (𝟙 A) Z = 𝟙 _) ∧
    (∀ (A B D : Under R) (b : A ⟶ B) (d : B ⟶ D),
      coefficientModuleMap R (b ≫ d) Z =
        coefficientModuleMap R b Z ≫ coefficientModuleMap R d Z) := by
  sorry

/-- The actual underlying coefficient-module diagram functor.
Source: blueprint (1) (blueprint: lem-sfb-rational-scalar-push-cocone). -/
def coefficientModules (Z : Scheme.{u}) : Under R ⥤ Modules R Z where
  obj A := coefficientModule R A Z
  map b := coefficientModuleMap R b Z
  map_id A := (coefficientModuleMap_laws R Z).1 A
  map_comp b d := (coefficientModuleMap_laws R Z).2 _ _ _ b d

/-- Termwise tensor by a varying coefficient module.
Source: blueprint (1), compatible complex representatives
(blueprint: lem-sfb-rational-scalar-push-cocone). -/
def tensorComplexMap (Z : Scheme.{u}) (C : CochainComplex (Modules R Z) ℤ)
    {M N : Modules R Z} (b : M ⟶ N) :
    ((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj C ⟶
      ((tensorLeft N).mapHomologicalComplex (.up ℤ)).obj C :=
  (NatTrans.mapHomologicalComplex ((curriedTensor (Modules R Z)).map b) (.up ℤ)).app C

/-- Termwise tensor is functorial in the coefficient module.
Source: blueprint (1) (blueprint: lem-sfb-rational-scalar-push-cocone).
Proof: in degree n these are the identity and composition laws of tensorRight (C.X n).
Equality of chain maps is equality in every degree. -/
theorem tensorComplexMap_laws (Z : Scheme.{u}) (C : CochainComplex (Modules R Z) ℤ) :
    (∀ M : Modules R Z, tensorComplexMap R Z C (𝟙 M) = 𝟙 _) ∧
    (∀ (M N P : Modules R Z) (b : M ⟶ N) (d : N ⟶ P),
      tensorComplexMap R Z C (b ≫ d) =
        tensorComplexMap R Z C b ≫ tensorComplexMap R Z C d) := by
  sorry

/-- The termwise coefficient tensor functor on a fixed complex.
Source: blueprint (1) (blueprint: lem-sfb-rational-scalar-push-cocone). -/
def tensorComplex (Z : Scheme.{u}) (C : CochainComplex (Modules R Z) ℤ) :
    Modules R Z ⥤ CochainComplex (Modules R Z) ℤ where
  obj M := ((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj C
  map b := tensorComplexMap R Z C b
  map_id M := (tensorComplexMap_laws R Z C).1 M
  map_comp b d := (tensorComplexMap_laws R Z C).2 _ _ _ b d

/-- Ordinary extension followed by restriction, with the original R-action.
Source: blueprint flat scalar computation (blueprint: lem-sfb-rational-scalar-push-cocone). -/
abbrev ordinaryScalar (A : Under R) (Z : Scheme.{u}) : Modules R Z ⥤ Modules R Z :=
  Mod.extendScalars (coefficientMap A.hom.hom.hom Z) ⋙
    Mod.comap (coefficientMap A.hom.hom.hom Z)

/-- The ordinary tensor/extension identification is natural in the input module.
Source: blueprint flat scalar computation (blueprint: lem-sfb-rational-scalar-push-cocone).
Proof: the projection formula sends s tensor m to s tensor (1 tensor m), and the
regular-module unitor multiplies the first two factors. Its composite is therefore
s tensor m. Both paths for a module map g send s tensor m to s tensor g(m).
The sheaf tensor universal property proves equality, including on sheafified sections. -/
theorem tensorScalar_naturality (A : Under R) (Z : Scheme.{u})
    (M N : Modules R Z) (g : M ⟶ N) :
    (tensorLeft (coefficientModule R A Z)).map g ≫
        ((Mod.projectionIso (coefficientMap A.hom.hom.hom Z)
          (Mod.regular (condensedRingObj (CommMon.X A.right) Z)) N) ≪≫
          (Mod.comap (coefficientMap A.hom.hom.hom Z)).mapIso (λ_ _)).hom =
      ((Mod.projectionIso (coefficientMap A.hom.hom.hom Z)
          (Mod.regular (condensedRingObj (CommMon.X A.right) Z)) M) ≪≫
          (Mod.comap (coefficientMap A.hom.hom.hom Z)).mapIso (λ_ _)).hom ≫
        (ordinaryScalar R A Z).map g := by
  sorry

/-- The canonical ordinary tensor/extension comparison, induced by multiplication.
Source: blueprint flat scalar computation (blueprint: lem-sfb-rational-scalar-push-cocone). -/
def tensorScalar (A : Under R) (Z : Scheme.{u}) :
    tensorLeft (coefficientModule R A Z) ≅ ordinaryScalar R A Z :=
  NatIso.ofComponents (fun M ↦
    Mod.projectionIso (coefficientMap A.hom.hom.hom Z)
        (Mod.regular (condensedRingObj (CommMon.X A.right) Z)) M ≪≫
      (Mod.comap (coefficientMap A.hom.hom.hom Z)).mapIso (λ_ _))
    (fun {M N} g ↦ tensorScalar_naturality R A Z M N g)

/-- The restricted derived extension of scalars, using the recorded left derived functor.
Source: blueprint notation V_Z T_Z (blueprint: lem-sfb-rational-scalar-push-cocone). -/
abbrev derivedScalar (A : Under R) (Z : Scheme.{u}) :=
  (Mod.extendScalars (coefficientMap A.hom.hom.hom Z)).leftDerivedFunctor ⋙
    (Mod.comap (coefficientMap A.hom.hom.hom Z)).mapDerivedCategory

set_option maxHeartbeats 800000 in
-- These canonical comparisons traverse the derived module functor structures.
/-- Canonical flat scalar computation on every complex: the left-derived counit,
exact restriction, and the multiplication tensor comparison.
Source: blueprint (1) (blueprint: lem-sfb-rational-scalar-push-cocone). -/
def scalarComputation (A : Under R) (Z : Scheme.{u})
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap A.hom.hom.hom Z))]
    (P : CochainComplex (Modules R Z) ℤ) :
    (derivedScalar R A Z).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((tensorComplex R Z P).obj (coefficientModule R A Z)) :=
  (Mod.comap (coefficientMap A.hom.hom.hom Z)).mapDerivedCategory.mapIso
      ((Functor.leftDerivedFunctorIsoMapDerivedCategory
        (Mod.extendScalars (coefficientMap A.hom.hom.hom Z))).app
          (DerivedCategory.Q.obj P)) ≪≫
    ((Functor.mapDerivedCategoryCompIso
      (Mod.extendScalars (coefficientMap A.hom.hom.hom Z))
      (Mod.comap (coefficientMap A.hom.hom.hom Z))).symm.app _) ≪≫
    (ordinaryScalar R A Z).mapDerivedCategoryFactors.app P ≪≫
    (DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (tensorScalar R A Z) (.up ℤ)).app P)).symm

/-- The coefficient-induced map on restricted derived scalars. It is computed on the
standard complex representative by the actual b_Z tensor 1, through the fixed flat
scalar computations. The choice of representative is the existing Q.objPreimage;
there is no choice of a map with these endpoints.
Source: blueprint (1), u_i,Z (blueprint: lem-sfb-rational-scalar-push-cocone). -/
def derivedCoefficientMap {A B : Under R} (b : A ⟶ B) (Z : Scheme.{u})
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap A.hom.hom.hom Z))]
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap B.hom.hom.hom Z))]
    (M : DerivedCategory (Modules R Z)) :
    (derivedScalar R A Z).obj M ⟶ (derivedScalar R B Z).obj M :=
  (derivedScalar R A Z).map (DerivedCategory.Q.objObjPreimageIso M).inv ≫
    (scalarComputation R A Z (DerivedCategory.Q.objPreimage M)).hom ≫
    DerivedCategory.Q.map
      ((tensorComplex R Z (DerivedCategory.Q.objPreimage M)).map
        (coefficientModuleMap R b Z)) ≫
    (scalarComputation R B Z (DerivedCategory.Q.objPreimage M)).inv ≫
    (derivedScalar R B Z).map (DerivedCategory.Q.objObjPreimageIso M).hom

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

set_option maxHeartbeats 800000 in
-- These canonical comparisons traverse the derived module functor structures.
/-- The canonical restricted scalar push mate, including the canonical d comparison.
Source: blueprint (1) (blueprint: lem-sfb-rational-scalar-push-cocone). -/
def restrictedPush (A : Under R)
    [∀ Z : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap A.hom.hom.hom Z))]
    (K : DerivedCategory (Modules R X)) :
    (derivedScalar R A Y).obj
        ((CondensedRing.lowerStar (CommMon.X R) p).rightDerivedFunctor.obj K) ⟶
      (CondensedRing.lowerStar (CommMon.X R) p).rightDerivedFunctor.obj
        ((derivedScalar R A X).obj K) :=
  (Mod.comap (coefficientMap A.hom.hom.hom Y)).mapDerivedCategory.map
      ((CondensedRing.derivedPushHom A.hom.hom.hom p).app K) ≫
    (CondensedRing.derivedComapLowerStarIso A.hom.hom.hom p).hom.app
      ((Mod.extendScalars (coefficientMap A.hom.hom.hom X)).leftDerivedFunctor.obj K)

/-- The canonical right-derived unit on an arbitrary complex, in cochain notation.
Source: blueprint right-derived computations (blueprint: lem-sfb-rational-scalar-push-cocone). -/
def pushUnit (P : CochainComplex (Modules R X) ℤ) :
    DerivedCategory.Q.obj
        (((CondensedRing.lowerStar (CommMon.X R) p).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (CondensedRing.lowerStar (CommMon.X R) p).rightDerivedFunctor.obj (DerivedCategory.Q.obj P) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (CondensedRing.lowerStar (CommMon.X R) p).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    (CondensedRing.lowerStar (CommMon.X R) p).rightDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso _).hom.app P)

/-- Use one fixed functorial R_X-module K-injective replacement for all coefficients.
Source: blueprint compatible representatives (blueprint: lem-sfb-rational-scalar-push-cocone). -/
def resolvedPush : CochainComplex (Modules R X) ℤ ⥤ CochainComplex (Modules R Y) ℤ :=
  CochainComplex.kInjectiveResolutionFunctor.{u + 1} (Modules R X) ⋙
    (CondensedRing.lowerStar (CommMon.X R) p).mapHomologicalComplex (.up ℤ)

/-- The fixed augmentation is a quasi-isomorphism by the existing resolution theorem.
Source: functorial K-injective replacement
(blueprint: lem-sfb-rational-scalar-push-cocone). -/
instance resolution_quasiIso (P : CochainComplex (Modules R X) ℤ) :
    QuasiIso ((CochainComplex.toKInjectiveResolution.{u + 1} (Modules R X)).app P) :=
  (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} (Modules R X) P).2

/-- The canonical computation of derived pushforward from the fixed replacement.
Source: blueprint compatible representatives (blueprint: lem-sfb-rational-scalar-push-cocone). -/
def resolvedPushComputation (P : CochainComplex (Modules R X) ℤ) :
    DerivedCategory.Q.obj ((resolvedPush R p).obj P) ⟶
      (CondensedRing.lowerStar (CommMon.X R) p).rightDerivedFunctor.obj (DerivedCategory.Q.obj P) :=
  pushUnit R p ((CochainComplex.kInjectiveResolutionFunctor.{u + 1} (Modules R X)).obj P) ≫
    (CondensedRing.lowerStar (CommMon.X R) p).rightDerivedFunctor.map
      (inv (DerivedCategory.Q.map
        ((CochainComplex.toKInjectiveResolution.{u + 1} (Modules R X)).app P)))

set_option maxHeartbeats 800000 in
-- These canonical comparisons traverse the derived module functor structures.
/-- The source computation for the native mate at the fixed derived input K.
Source: blueprint (1) (blueprint: lem-sfb-rational-scalar-push-cocone). -/
def sourceComputation (A : Under R)
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap A.hom.hom.hom Y))]
    (C : CochainComplex (Modules R X) ℤ) {K : DerivedCategory (Modules R X)}
    (e : DerivedCategory.Q.obj C ≅ K) :
    DerivedCategory.Q.obj ((tensorComplex R Y
      (((CondensedRing.lowerStar (CommMon.X R) p).mapHomologicalComplex (.up ℤ)).obj C)).obj
        (coefficientModule R A Y)) ⟶
      (derivedScalar R A Y).obj
        ((CondensedRing.lowerStar (CommMon.X R) p).rightDerivedFunctor.obj K) :=
  (scalarComputation R A Y _).inv ≫
    (derivedScalar R A Y).map (pushUnit R p C ≫
      (CondensedRing.lowerStar (CommMon.X R) p).rightDerivedFunctor.map e.hom)

set_option maxHeartbeats 800000 in
-- These canonical comparisons traverse the derived module functor structures.
/-- The target computation induced by the same fixed functorial augmentation.
Source: blueprint (1) (blueprint: lem-sfb-rational-scalar-push-cocone). -/
def targetComputation (A : Under R)
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap A.hom.hom.hom X))]
    (C : CochainComplex (Modules R X) ℤ) {K : DerivedCategory (Modules R X)}
    (e : DerivedCategory.Q.obj C ≅ K) :
    DerivedCategory.Q.obj ((resolvedPush R p).obj
      ((tensorComplex R X C).obj (coefficientModule R A X))) ⟶
      (CondensedRing.lowerStar (CommMon.X R) p).rightDerivedFunctor.obj
        ((derivedScalar R A X).obj K) :=
  resolvedPushComputation R p _ ≫
    (CondensedRing.lowerStar (CommMon.X R) p).rightDerivedFunctor.map
      ((scalarComputation R A X C).inv ≫ (derivedScalar R A X).map e.hom)

/-- The source tensor complexes, functorial in the coefficient algebra.
Source: blueprint (1) (blueprint: lem-sfb-rational-scalar-push-cocone). -/
def sourceFunctor (C : CochainComplex (Modules R X) ℤ) :
    Under R ⥤ CochainComplex (Modules R Y) ℤ :=
  coefficientModules R Y ⋙ tensorComplex R Y
    (((CondensedRing.lowerStar (CommMon.X R) p).mapHomologicalComplex (.up ℤ)).obj C)

/-- The coefficient tensor complexes on X, before taking direct image.
Source: blueprint (1) (blueprint: lem-sfb-rational-scalar-push-cocone). -/
def inputFunctor (C : CochainComplex (Modules R X) ℤ) :
    Under R ⥤ CochainComplex (Modules R X) ℤ :=
  coefficientModules R X ⋙ tensorComplex R X C

/-- Compatible complexes representing the derived targets, in the fixed R_X category.
Source: blueprint (1) (blueprint: lem-sfb-rational-scalar-push-cocone). -/
def targetFunctor (C : CochainComplex (Modules R X) ℤ) :
    Under R ⥤ CochainComplex (Modules R Y) ℤ :=
  inputFunctor R C ⋙ resolvedPush R p

set_option maxHeartbeats 800000 in
-- These canonical comparisons traverse the derived module functor structures.
/-- The native scalar mates form a compatible filtered cocone at a fixed bounded-below K;
its source and target comparison maps from termwise colimits are isomorphisms after Q.

Source: current blueprint rational proper-base-change proof, paragraph (1)
(blueprint: lem-sfb-rational-scalar-push-cocone).

Proof:
1. Transport to reconstructed section-module sheaves using the exact section equivalences
and their tensor/operation comparisons. The module category is Grothendieck, hence has enough
injectives. Represent K by a K-injective C zero below a; use one fixed functorial K-injective
replacement in R_X-modules for every coefficient tensor complex.
2. Flat scalar extension computes termwise tensor on every complex. The named scalarComputation
is precisely the left-derived counit computation. The normalized resolution formula identifies
the ordinary mate followed by the fixed augmentation with restrictedPush, including its d
comparison, under sourceComputation and targetComputation.
3. For each coefficient transition b, the ordinary mate square sends a local tensor s tensor c
to b(p-sharp(s)) tensor c along both paths. Local tensor generators and augmentation naturality
make these strict chain squares. They give v and vS and the cocone equation below.
4. Tensor commutes with filtered colimits. The given coefficient colimit therefore makes the
source comparison an isomorphism of complexes, and makes the input cocone a colimit. Each
input tensor complex is zero below a by termwise flat tensor.
5. Exact filtered colimits commute with homology. The homology of the target comparison is
the canonical filtered continuity map for the fixed R_X-module direct image. Bounded-below
continuity for qcqs p makes it an isomorphism in every degree, so Q of this comparison is
invertible. The fixed natural augmentation ensures these are the specified direct-image legs.
6. The strict cocone squares imply beta composed with colim(v) equals vS composed with alpha,
by the colimit universal property in complexes. Localize. The normalization equations identify
Q(vS) with the native restricted mate at K; the two invertible comparisons give exactly the
asserted colimit identification. Naturality of v and the cocone equation give the displayed
coefficient-transition equation under these same scalar/direct-image identifications.
-/
theorem rationalScalarPushCocone
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [p.IsOver (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [QuasiCompact p] [QuasiSeparated p]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Under R) (c : Cocone F)
    (hcolim : ∀ Z : Scheme.{u},
      Nonempty (IsColimit ((coefficientModules R Z).mapCocone c)))
    [∀ (i : I) (Z : Scheme.{u}), PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (F.obj i).hom.hom.hom Z))]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap c.pt.hom.hom.hom Z))]
    (K : DerivedCategory (Modules R X)) (a : ℤ) (hK : K.IsGE a) :
    (∀ (i j : I) (b : i ⟶ j),
      restrictedPush R p (F.obj i) K ≫
          (CondensedRing.lowerStar (CommMon.X R) p).rightDerivedFunctor.map
            (derivedCoefficientMap R (F.map b) X K) =
        derivedCoefficientMap R (F.map b) Y
            ((CondensedRing.lowerStar (CommMon.X R) p).rightDerivedFunctor.obj K) ≫
          restrictedPush R p (F.obj j) K) ∧
    (∀ i : I, restrictedPush R p (F.obj i) K ≫
          (CondensedRing.lowerStar (CommMon.X R) p).rightDerivedFunctor.map
            (derivedCoefficientMap R (B := c.pt) (c.ι.app i) X K) =
        derivedCoefficientMap R (B := c.pt) (c.ι.app i) Y
            ((CondensedRing.lowerStar (CommMon.X R) p).rightDerivedFunctor.obj K) ≫
          restrictedPush R p c.pt K) ∧
    ∃ (C : CochainComplex (Modules R X) ℤ) (e : DerivedCategory.Q.obj C ≅ K),
      C.IsKInjective ∧ (∀ n : ℤ, n < a → IsZero (C.X n)) ∧
      (∀ (i : I) (n : ℤ), n < a → IsZero (((inputFunctor R C).obj (F.obj i)).X n)) ∧
      (∀ n : ℤ, n < a → IsZero (((inputFunctor R C).obj c.pt).X n)) ∧
      ∃ (v : F ⋙ sourceFunctor R p C ⟶ F ⋙ targetFunctor R p C)
        (vS : (sourceFunctor R p C).obj c.pt ⟶ (targetFunctor R p C).obj c.pt),
        (∀ i : I,
          IsIso (sourceComputation R p (F.obj i) C e) ∧
          IsIso (targetComputation R p (F.obj i) C e) ∧
          DerivedCategory.Q.map (v.app i) ≫ targetComputation R p (F.obj i) C e =
            sourceComputation R p (F.obj i) C e ≫ restrictedPush R p (F.obj i) K) ∧
        IsIso (sourceComputation R p c.pt C e) ∧
        IsIso (targetComputation R p c.pt C e) ∧
        DerivedCategory.Q.map vS ≫ targetComputation R p c.pt C e =
          sourceComputation R p c.pt C e ≫ restrictedPush R p c.pt K ∧
        (∀ i : I, v.app i ≫ (targetFunctor R p C).map (c.ι.app i) =
          (sourceFunctor R p C).map (c.ι.app i) ≫ vS) ∧
        IsIso (DerivedCategory.Q.map (colimit.desc (F ⋙ sourceFunctor R p C)
          ((sourceFunctor R p C).mapCocone c))) ∧
        IsIso (DerivedCategory.Q.map (colimit.desc (F ⋙ targetFunctor R p C)
          ((targetFunctor R p C).mapCocone c))) ∧
        colim.map v ≫ colimit.desc (F ⋙ targetFunctor R p C)
            ((targetFunctor R p C).mapCocone c) =
          colimit.desc (F ⋙ sourceFunctor R p C)
            ((sourceFunctor R p C).mapCocone c) ≫ vS := by
  sorry

end AlgebraicGeometry.ProEtale.RationalScalarPush
