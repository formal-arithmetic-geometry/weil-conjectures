/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.ModuleRingedToposDerivedComparison
public import Sheaf.Paper.IntegralResidueTensorPullPresentation
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.FilteredColimitsTensor
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Paper.RingedComparisonTensorAdjunction
import Sheaf.Paper.CondensedQcqsPushforwardContinuity
import Sheaf.Paper.CondensedQbarExchangeRightAdjunct
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction

/-!
# Flat coefficient push comparison and its filtered cocone legs

Source: blueprint main-20261015, rational proper base change, paragraph (1),
localization and finite-extension colimits (blueprint: lem-sfb-coefficient-push-filtered-legs).

The projection arrows and the restricted scalar tensor presentation below are the
existing canonical constructions, including their tensor symmetry normalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint AlgebraicGeometry.ProEtale.upperStar

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open ModuleRingedComparison
  (internalModules internalDerivedPullback internalDerivedPushforward internalProjection
    comparisonSource)

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]

/-- Exact scalar restriction with its two internal module categories exposed.
Its body is the recorded levelwise restriction functor, without any new data.
Source: Stacks 07A6; blueprint rational proper base change, paragraph (1)
(blueprint: lem-sfb-coefficient-push-filtered-legs). -/
def filteredCoefficientRestriction (Z : Scheme.{u}) :
    DerivedCategory (internalModules S Z) ⥤ DerivedCategory (internalModules R Z) :=
  (Mod.comap (coefficientMap a Z)).mapDerivedCategory

/-- Scalar extension with its internal module categories exposed. The body is
exactly the existing total left derived scalar extension.
Source: Stacks 07A6; blueprint rational proper base change, paragraph (1)
(blueprint: lem-sfb-coefficient-push-filtered-legs). -/
def filteredCoefficientExtension (Z : Scheme.{u}) :
    DerivedCategory (internalModules R Z) ⥤ DerivedCategory (internalModules S Z) :=
  (fun {T : DerivedCategory (internalModules R Z) ⥤
      DerivedCategory (internalModules S Z)}
    {U : DerivedCategory (internalModules S Z) ⥤ DerivedCategory (internalModules R Z)}
    (_adj : T ⊣ U) ↦ T)
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Z))

/-- The existing balanced derived scalar tensor presentation, with its category
endpoints exposed to avoid repeatedly inferring the derived restriction data.
The symmetric structure explicitly retains the existing named sheaf braiding;
its symmetry proof is the existing sheaf symmetry. This fixes structural data,
without choosing a new monoidal structure or any comparison map.
Source: Stacks 07A6; blueprint rational proper base change, paragraph (1)
(blueprint: lem-sfb-coefficient-push-filtered-legs). -/
def filteredCoefficientTensorIso (Z : Scheme.{u}) :
    filteredCoefficientExtension a Z ⋙ filteredCoefficientRestriction a Z ≅
      (derivedTensor R Z).flip.obj
        ((DerivedCategory.singleFunctor (internalModules R Z) 0).obj
          ((Mod.comap (coefficientMap a Z)).obj (Mod.regular (condensedRingObj S Z)))) := by
  letI : SymmetricCategory (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
    { toBraidedCategory := sheafBraidedCategory Ab.{u + 1} Z
      symmetry := fun M N ↦ @SymmetricCategory.symmetry _ _ _ (sheafSymmetricCategory Z) M N }
  exact Mod.residueDerivedTensorIso (coefficientMap a Z)

/-- The recorded restriction/pushforward comparison with its endpoints exposed.
Source: Stacks 07A6; blueprint rational proper base change, paragraph (1)
(blueprint: lem-sfb-coefficient-push-filtered-legs). -/
def filteredCoefficientRestrictPushIso
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalDerivedPushforward S f ⋙ filteredCoefficientRestriction a Y ≅
      filteredCoefficientRestriction a X ⋙ internalDerivedPushforward R f :=
  derivedComapLowerStarIso a f

/-- The recorded coefficient push mate with the four functor endpoints exposed.
This definition is exactly derivedPushHom, not an unspecified map.
Source: Stacks 07A6; blueprint rational proper base change, paragraph (1)
(blueprint: lem-sfb-coefficient-push-filtered-legs). -/
def filteredCoefficientPushHom
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalDerivedPushforward R f ⋙ filteredCoefficientExtension a Y ⟶
      filteredCoefficientExtension a X ⋙ internalDerivedPushforward S f :=
  derivedPushHom a f

/-- The existing restricted-regular pullback comparison, with its total derived
pullback endpoint exposed. No comparison is chosen: this is precisely
`residueRestrictedRegularPullIso`, constructed from exact pullback/single,
restriction/pullback and the ordinary regular-module unit.
Source: Stacks 07A4 and 07A6; blueprint rational proper base change, paragraph (1)
(blueprint: lem-sfb-coefficient-push-filtered-legs). -/
def filteredCoefficientPullIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (internalDerivedPullback R f).obj
        ((DerivedCategory.singleFunctor (internalModules R Y) 0).obj
          ((Mod.comap (coefficientMap a Y)).obj (Mod.regular (condensedRingObj S Y)))) ≅
      (DerivedCategory.singleFunctor (internalModules R X) 0).obj
        ((Mod.comap (coefficientMap a X)).obj (Mod.regular (condensedRingObj S X))) := by
  unfold internalDerivedPullback comparisonSource
  exact @id _ (by
    simpa only [residueExchangeUpperStar] using residueRestrictedRegularPullIso R S a f)

attribute [local irreducible] filteredCoefficientExtension filteredCoefficientRestriction
  filteredCoefficientTensorIso filteredCoefficientPullIso
  filteredCoefficientPushHom
  filteredCoefficientRestrictPushIso internalDerivedPullback internalDerivedPushforward
  internalProjection

/-- A bounded filtered flat presentation detects the canonical flat coefficient
push comparison, and its cocone legs are the projection-formula legs.
Source: blueprint main-20261015, rational proper base change, paragraph (1);
Stacks 03DB, 03EP, 07A4, 07A6 and 0B56; Hemo--Richarz--Scholbach Lemma 5.3(1)
(blueprint: lem-sfb-coefficient-push-filtered-legs).

Proof plan, following the node's seven steps.
1. Use module_ringed_topos_derived_comparison to identify internal and ringed
modules, tensors and adjunctions. Exact restriction identifies scalar extension
with right tensor by the restricted regular coefficient; its unit inserts one.
2. Pullback preserves the presented colimit. Flat degree-zero coefficients are
K-flat. Tensor the bounded-below representative of K with the pulled stage
modules; the resulting strict diagram has one common lower bound. Tensor and
exact filtered colimits commute, as do cohomology and these colimits.
3. Apply condensed_qcqs_pushforward_continuity to that strict bounded diagram.
On the source use a K-flat representative of the derived pushforward. This gives
both cohomology-colimit comparisons with their actual cocone legs.
4. Identify derivedComapLowerStarIso with the ring-sheaf restriction comparison
on K-injective complexes. The ringed comparison tensor-adjunction lemma identifies
its conjugate with tensor pullback, normalized on pure tensors and scalar units.
5. Apply the coefficient push-counit identity and adjoint compatibility. The
restricted derivedPushHom is exactly the projection mate at the restricted
regular coefficient, after the canonical scalar tensor identifications.
6. Naturality of the projection mate in the coefficient map v_i gives the
stated equality of cocone legs and the compatible family of stage maps.
7. The invertible stage maps induce an invertible map on every cohomology
colimit. Hence the restricted push comparison is invertible. Exact restriction
reflects isomorphisms, so derivedPushHom itself is invertible. No colimit in the
ordinary triangulated derived category is asserted. -/
theorem coefficientPush_isIso_of_filtered_flat_legs
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (_hp : 0 < p) (_hne : p ≠ ℓ)
    {X Y : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [QuasiCompact f.left] [QuasiSeparated f.left]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (P : I ⥤ internalModules R Y.left)
    (_hP : ∀ i : I, ObjectProperty.flat (P.obj i))
    (_hfP : ∀ i : I, ObjectProperty.flat ((upperStar R f.left).obj (P.obj i)))
    (v : P ⟶ (Functor.const I).obj
      ((Mod.comap (coefficientMap a Y.left)).obj (Mod.regular (condensedRingObj S Y.left))))
    (_hv : IsColimit (Cocone.mk _ v))
    (K : DerivedCategory (internalModules R X.left)) (_hK : ∃ n : ℤ, K.IsGE n)
    (_hδ : ∀ i : I, IsIso (internalProjection R f.left K
      ((DerivedCategory.singleFunctor (internalModules R Y.left) 0).obj (P.obj i)))) :
    IsIso ((filteredCoefficientPushHom a f.left).app K) ∧
      ∀ i : I,
        ((derivedTensor R Y.left).obj ((internalDerivedPushforward R f.left).obj K)).map
            ((DerivedCategory.singleFunctor (internalModules R Y.left) 0).map (v.app i)) ≫
          (filteredCoefficientTensorIso a Y.left).inv.app
            ((internalDerivedPushforward R f.left).obj K) ≫
          (filteredCoefficientRestriction a Y.left).map
            ((filteredCoefficientPushHom a f.left).app K) ≫
          (filteredCoefficientRestrictPushIso a f.left).hom.app
            ((filteredCoefficientExtension a X.left).obj K) =
        internalProjection R f.left K
            ((DerivedCategory.singleFunctor (internalModules R Y.left) 0).obj (P.obj i)) ≫
          (internalDerivedPushforward R f.left).map
            (((derivedTensor R X.left).obj K).map
                ((internalDerivedPullback R f.left).map
                  ((DerivedCategory.singleFunctor (internalModules R Y.left) 0).map (v.app i))) ≫
              ((derivedTensor R X.left).obj K).map (filteredCoefficientPullIso a f.left).hom ≫
              (filteredCoefficientTensorIso a X.left).inv.app K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
