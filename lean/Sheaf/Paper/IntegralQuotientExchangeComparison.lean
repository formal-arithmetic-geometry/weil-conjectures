/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Paper.IntegralQuotientDirectImageComparison
public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.Paper.SectionDerivedPushpullNormalization
public import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
import Sheaf.CategoryTheory.ExchangeMateCube
import Sheaf.Paper.FiniteReductionExchangeRectangle
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

import Sheaf.Paper.FourArrows
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

/-! # Reduction of the actual unbounded integral exchange

Source: blueprint main-20261015, integral proper-base-change proof, paragraph (3);
Stacks Project, Tags 07A7, 0E47 and 0E48
(blueprint: lem-sfb-integral-quotient-exchange-comparison).

The equality is an equality of natural transformations. Its section-module realization
uses the independently specified ringed adjunctions and geometric compositors. Scalar
comparisons retain their balanced-generator and K-flat computation normalizations.
As in the direct-image comparison, n denotes quotient exponent n + 1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale.QuotientChange
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory

open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct ChangeOfRings

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

section Ambient

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The recorded actual ambient exchange, with the direct-image comparison's typed
interfaces. Source: Stacks 07A7
(blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
def ambient (sq : ChosenCartesianSquare h f' f g) :
    F Λ f ⋙ L Λ g ⟶ L Λ h ⋙ F Λ f' := by
  unfold F L CondensedRing.moduleObjectDerivedPushforward
    CondensedRing.moduleObjectDerivedPullback
  exact CondensedRing.condensedAmbientExchange Λ sq

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]

/-- The independently specified section-module geometric square: compose the actual
ringed derived pullbacks along the two equal scheme composites.
Source: Stacks 0D6D and 07A7
(blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
def sectionSquare (sq : ChosenCartesianSquare h f' f g) :
    ModuleRingedComparison.derivedPullback Λ g ⋙
        ModuleRingedComparison.derivedPullback Λ f' ≅
      ModuleRingedComparison.derivedPullback Λ f ⋙
        ModuleRingedComparison.derivedPullback Λ h :=
  (ModuleRingedComparison.derivedPullbackComposition Λ f' g).symm ≪≫
    eqToIso (congrArg
      (fun k : X' ⟶ Y ↦ ModuleRingedComparison.derivedPullback Λ k)
      sq.toCommSq.w.symm) ≪≫
    ModuleRingedComparison.derivedPullbackComposition Λ h f

/-- The actual ringed exchange, formed with the independently derived section-module
adjunctions and the geometric square, before any completeness condition.
Source: Stacks 07A7 (blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
def sectionExchange (sq : ChosenCartesianSquare h f' f g) :
    ModuleRingedComparison.derivedPushforward Λ f ⋙
        ModuleRingedComparison.derivedPullback Λ g ⟶
      ModuleRingedComparison.derivedPullback Λ h ⋙
        ModuleRingedComparison.derivedPushforward Λ f' :=
  (mateEquiv (ModuleRingedComparison.derivedAdjunction Λ f)
    (ModuleRingedComparison.derivedAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (sectionSquare Λ sq).hom)).natTrans

/-- The existing normalized pullback comparison, with its internal endpoint made explicit.
Source: Stacks 07A6 (blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
def pullSection {U V : Scheme.{u}} (u : U ⟶ V) :
    L Λ u ⋙ ModuleRingedComparison.derivedFunctor Λ U ≅
      ModuleRingedComparison.derivedFunctor Λ V ⋙ ModuleRingedComparison.derivedPullback Λ u := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact ModuleRingedComparison.derivedPullComparison Λ u

/-- The existing normalized pushforward comparison, with its internal endpoint explicit.
Source: Stacks 07A6 (blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
def pushSection {U V : Scheme.{u}} (u : U ⟶ V) :
    F Λ u ⋙ ModuleRingedComparison.derivedFunctor Λ V ≅
      ModuleRingedComparison.derivedFunctor Λ U ⋙
        ModuleRingedComparison.derivedPushforward Λ u := by
  unfold F CondensedRing.moduleObjectDerivedPushforward
  exact ModuleRingedComparison.derivedPushComparison Λ u

/-- Identification of the actual exchanges under the fixed termwise section equivalences
and their normalized push/pull comparisons. This asserts equality of the transformations,
including the unit, geometric square and counit, rather than just their endpoints.
Source: Stacks 07A7 and 09T5
(blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
def ExchangeRealized (sq : ChosenCartesianSquare h f' f g) : Prop :=
  ∀ K : DerivedCategory (Modules Λ X),
    (pullSection Λ g).hom.app ((F Λ f).obj K) ≫
        (ModuleRingedComparison.derivedPullback Λ g).map
          ((pushSection Λ f).hom.app K) ≫
        (sectionExchange Λ sq).app
          ((ModuleRingedComparison.derivedFunctor Λ X).obj K) =
      (ModuleRingedComparison.derivedFunctor Λ Y').map ((ambient Λ sq).app K) ≫
        (pushSection Λ f').hom.app ((L Λ h).obj K) ≫
        (ModuleRingedComparison.derivedPushforward Λ f').map
          ((pullSection Λ h).hom.app K)

end Ambient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual finite projection reconstructed as a section-ring map.
Source: blueprint integral proof (3); Stacks 03EK
(blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
abbrev sectionReduction (T : Scheme.{u}) (n : ℕ) :
    ModuleRingedComparison.ring (integral l E) T ⟶
      ModuleRingedComparison.ring (finite l E n) T :=
  InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
    (coefficientMap (reduction l E n) T)

variable (n : ℕ)
  [∀ T : Scheme.{u},
    HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules (integral l E) T)]
  [∀ T : Scheme.{u},
    HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules (finite l E n) T)]

/-- The complete normalization of the scalar realization: unchanged balanced generators
on ordinary sheafification and the universal comparison on flat-term K-flat complexes.
Thus the section scalar functor is the actual uncompleted derived extension, and the
comparison has no scalar twist. Source: Stacks 03EK, 06YY and 09T5
(blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
def ScalarRealized (T : Scheme.{u})
    (q : SheafOfModules.ScalarDerivedPair
      (J := Scheme.ProEt.topology T)
      (R := ModuleRingedComparison.ring (integral l E) T)
      (S := ModuleRingedComparison.ring (finite l E n) T) (sectionReduction l E T n))
    (e₀ : extension (reduction l E n) T ⋙
        (ModuleRingedComparison.equivalence (finite l E n) T).functor ≅
      (ModuleRingedComparison.equivalence (integral l E) T).functor ⋙ q.extension)
    (e : D (reduction l E n) T ⋙
        ModuleRingedComparison.derivedFunctor (finite l E n) T ≅
      ModuleRingedComparison.derivedFunctor (integral l E) T ⋙ q.derived) : Prop :=
  (∀ (M : Modules (integral l E) T) (U : T.ProEtᵒᵖ)
      (s : (condensedRingObj (finite l E n) T).obj.obj U) (m : M.X.obj.obj U),
    ((eqToHom (q.extension_obj
      ((ModuleRingedComparison.equivalence (integral l E) T).functor.obj M))).val.app U)
        ((e₀.hom.app M).val.app U
          (InternalAbelianSheafModule.internalScalarGenerator (Scheme.ProEt.topology T)
            (coefficientMap (reduction l E n) T) M U s m)) =
      (toSheafify (Scheme.ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf (sectionReduction l E T n)
          ((ModuleRingedComparison.equivalence (integral l E) T).functor.obj M)).presheaf).app U
        (s ⊗ₜ[(ModuleRingedComparison.ring (integral l E) T).obj.obj U,
            ((sectionReduction l E T n).hom.app U).hom] m)) ∧
  (∀ P : CochainComplex (Modules (integral l E) T) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients
        (R := ModuleRingedComparison.ring (integral l E) T)
        (((ModuleRingedComparison.equivalence (integral l E) T).functor.mapHomologicalComplex
          (.up ℤ)).obj P) →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology T)
      (R := ModuleRingedComparison.ring (integral l E) T)
      ((ModuleRingedComparison.equivalence (integral l E) T).functor.obj (P.X i))) →
    (ModuleRingedComparison.derivedFunctor (finite l E n) T).map
        (compute (reduction l E n) T P) ≫
        (Functor.mapDerivedCategoryFactors
          (ModuleRingedComparison.equivalence (finite l E n) T).functor).hom.app
            (((extension (reduction l E n) T).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e₀ (.up ℤ)).hom.app P) =
      e.hom.app (DerivedCategory.Q.obj P) ≫
        q.derived.map
          (ModuleRingedComparison.sectionLocalizationComparison (integral l E) T P).hom ≫
        SheafOfModules.scalarPairComplexComparison q.extension q.extension_additive
          q.derived q.counit
          (((ModuleRingedComparison.equivalence (integral l E) T).functor.mapHomologicalComplex
          (.up ℤ)).obj P))

/-- The specified finite projection in section coordinates: it is the counit-adjunct
mate of the normalized scalar/pullback comparison under the actual ringed adjunctions.
Source: Stacks 07A7 and 0E48
(blueprint: lem-sfb-integral-quotient-exchange-comparison). -/
def sectionProjection
    (q : ∀ T : Scheme.{u}, SheafOfModules.ScalarDerivedPair
      (J := Scheme.ProEt.topology T)
      (R := ModuleRingedComparison.ring (integral l E) T)
      (S := ModuleRingedComparison.ring (finite l E n) T) (sectionReduction l E T n))
    {U V : Scheme.{u}} (u : U ⟶ V)
    (χ : (q V).derived ⋙ ModuleRingedComparison.derivedPullback (finite l E n) u ≅
      ModuleRingedComparison.derivedPullback (integral l E) u ⋙ (q U).derived) :
    ModuleRingedComparison.derivedPushforward (integral l E) u ⋙ (q V).derived ⟶
      (q U).derived ⋙ ModuleRingedComparison.derivedPushforward (finite l E n) u :=
  (mateEquiv (ModuleRingedComparison.derivedAdjunction (integral l E) u)
    (ModuleRingedComparison.derivedAdjunction (finite l E n) u)
    (TwoSquare.mk _ _ _ _ χ.hom)).natTrans

variable
    (b : ∀ {U V : Scheme.{u}} (u : U ⟶ V),
      D (reduction l E n) V ⋙ L (finite l E n) u ≅
        L (integral l E) u ⋙ D (reduction l E n) U)
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The normalized unbounded integral exchange equality and its actual section-module
finite-rectangle realization, naturally in the input complex.

Source: blueprint main-20261015, integral proper-base-change proof, paragraph (3),
"the reduction of each canonical map is the corresponding canonical map for the torsion
reductions"; Stacks Tags 07A7, 0E47 and 0E48
(blueprint: lem-sfb-integral-quotient-exchange-comparison).

Proof:
1. Use sectionDerivedPushpullNormalization and internal_section_scalar_adjunction to
identify the actual internal and section module operations, units, counits and geometric
compositors. The balanced-generator and K-flat scalar equations below retain the actual
projection and the uncompleted relative tensor; internal_section_tensor_comparison
preserves the flat-term K-flat representatives.
2. The integral coefficient limit and profinite-coefficient inverse-image comparison
identify both geometric coefficient maps with pullback of continuous sections. Their
finite projections commute with every edge and with both square composites.
3. Compute on a flat-term K-flat representative. Scalar extension preserves this class:
tensoring with an acyclic quotient-coefficient complex is tensoring the original complex
with its restriction. Both pullback/reduction routes send a balanced tensor to pullback
of its two factors. The geometric compositors therefore give the same inverse-image cube.
4. By definition rho is the adjunct of balancing followed by reduction of the integral
counit. Both ambient exchanges are likewise mates of the actual geometric square.
5. Apply exchangeMate_cube to the cube of Step 3 with inverse balancing comparisons.
Precompose with lambda_g and postcompose with direct image of lambda_h. Cancel inverse
pairs. This is the first equality below, in the quotient derived category itself.
6. In section coordinates chi is the same normalized balanced pullback map, and its
specified finite projection is the same counit-adjunct mate. The displayed realization
equations identify rho and both exchanges with these independently specified ringed
maps. The resulting section natural-transformation equality is exactly the rectangle
of finiteReductionExchange_rectangle, with the direct image of inverse chi_h last.
Postcomposing with direct image of chi_h recovers Step 5.
7. integral_quotient_direct_image_comparison makes both specified rho maps invertible;
lambda is already an isomorphism. Thus this equality identifies the reduced actual
exchange with the actual quotient exchange. All statements are natural-transformation
equalities, without properness, completeness, boundedness, constructibility, or an
invertibility assumption on either exchange. Positive exponent one, identity squares,
zero complexes and empty schemes are included. -/
theorem integral_quotient_exchange_comparison
    (hb : ∀ {U V : Scheme.{u}} (u : U ⟶ V),
      PullNormalized (reduction l E n) u (b u))
    (sq : ChosenCartesianSquare h f' f g) :
    (Functor.whiskerRight (rho (reduction l E n) f (b f)) (L (finite l E n) g) ≫
        Functor.whiskerLeft (D (reduction l E n) X) (ambient (finite l E n) sq) ≫
        Functor.whiskerRight (b h).hom (F (finite l E n) f') =
      Functor.whiskerLeft (F (integral l E) f) (b g).hom ≫
        Functor.whiskerRight (ambient (integral l E) sq) (D (reduction l E n) Y') ≫
        Functor.whiskerLeft (L (integral l E) h) (rho (reduction l E n) f' (b f'))) ∧
    IsIso (rho (reduction l E n) f (b f)) ∧
    IsIso (rho (reduction l E n) f' (b f')) ∧
    ExchangeRealized (integral l E) sq ∧ ExchangeRealized (finite l E n) sq ∧
    ∃ q : ∀ T : Scheme.{u}, SheafOfModules.ScalarDerivedPair
      (J := Scheme.ProEt.topology T)
      (R := ModuleRingedComparison.ring (integral l E) T)
      (S := ModuleRingedComparison.ring (finite l E n) T) (sectionReduction l E T n),
    ∃ e₀ : ∀ T : Scheme.{u},
        extension (reduction l E n) T ⋙
            (ModuleRingedComparison.equivalence (finite l E n) T).functor ≅
          (ModuleRingedComparison.equivalence (integral l E) T).functor ⋙ (q T).extension,
    ∃ e : ∀ T : Scheme.{u},
        D (reduction l E n) T ⋙ ModuleRingedComparison.derivedFunctor (finite l E n) T ≅
          ModuleRingedComparison.derivedFunctor (integral l E) T ⋙ (q T).derived,
      (∀ T : Scheme.{u}, ScalarRealized l E n T (q T) (e₀ T) (e T)) ∧
    ∃ χ : ∀ {U V : Scheme.{u}} (u : U ⟶ V),
        (q V).derived ⋙ ModuleRingedComparison.derivedPullback (finite l E n) u ≅
          ModuleRingedComparison.derivedPullback (integral l E) u ⋙ (q U).derived,
      (∀ {U V : Scheme.{u}} (u : U ⟶ V) (M : DerivedCategory (Modules (integral l E) V)),
        (pullSection (finite l E n) u).hom.app
            ((D (reduction l E n) V).obj M) ≫
            (ModuleRingedComparison.derivedPullback (finite l E n) u).map
              ((e V).hom.app M) ≫
            (χ u).hom.app ((ModuleRingedComparison.derivedFunctor (integral l E) V).obj M) =
          (ModuleRingedComparison.derivedFunctor (finite l E n) U).map ((b u).hom.app M) ≫
            (e U).hom.app ((L (integral l E) u).obj M) ≫
            (q U).derived.map
              ((pullSection (integral l E) u).hom.app M)) ∧
      (∀ {U V : Scheme.{u}} (u : U ⟶ V) (K : DerivedCategory (Modules (integral l E) U)),
        (ModuleRingedComparison.derivedFunctor (finite l E n) V).map
            ((rho (reduction l E n) u (b u)).app K) ≫
            (pushSection (finite l E n) u).hom.app
              ((D (reduction l E n) U).obj K) ≫
            (ModuleRingedComparison.derivedPushforward (finite l E n) u).map
              ((e U).hom.app K) =
          (e V).hom.app ((F (integral l E) u).obj K) ≫
            (q V).derived.map
              ((pushSection (integral l E) u).hom.app K) ≫
            (sectionProjection l E n q u (χ u)).app
              ((ModuleRingedComparison.derivedFunctor (integral l E) U).obj K)) ∧
      (Functor.whiskerRight (sectionProjection l E n q f (χ f))
          (ModuleRingedComparison.derivedPullback (finite l E n) g) ≫
        Functor.whiskerLeft (q X).derived (sectionExchange (finite l E n) sq) =
      Functor.whiskerLeft (ModuleRingedComparison.derivedPushforward (integral l E) f)
          (χ g).hom ≫
        Functor.whiskerRight (sectionExchange (integral l E) sq) (q Y').derived ≫
        Functor.whiskerLeft (ModuleRingedComparison.derivedPullback (integral l E) h)
          (sectionProjection l E n q f' (χ f')) ≫
        Functor.whiskerRight (χ h).inv
          (ModuleRingedComparison.derivedPushforward (finite l E n) f')) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralQuotient
