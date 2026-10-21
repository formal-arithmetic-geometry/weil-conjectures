/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26, SHEAF group K2
-/
module

public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.ResidueLissePerfectLift
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Paper.CompletedConstantAlgebraFlatQuotients

/-!
# Completed integral constant models

(blueprint: def-weil-pbc-integral-stratified-perfect-models).

Definitions and exact realization for the integral stratified-perfect characterization.
Source: Bhatt--Scholze, Propositions 6.6.11 and 6.8.11(3)
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.Scheme

/-- The ordinary realization N ↦ A_T ⊗_A N, using the normalized coefficient comparison.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def integralConstantModule (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : ModuleCat.{u + 1} A ⥤
      pbcModules T (pbcAdicCompletion T d) :=
  completedKoszulConstant T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite } ⋙
    pbcRestrict (pbcCompletedComparison T d).inv

/-- Exactness of the ordinary completed-constant realization.
Source: Bhatt--Scholze, Lemma 6.5.8 and Proposition 6.6.11
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization).
Proof: constant module sheafification is exact. The completed ring is flat over
constant A by lem-weil-pbc-completed-constant-sheaf-reduction, since d is Noetherian.
Thus tensoring with it preserves finite limits and colimits. Restriction along the
normalized coefficient isomorphism is an exact equivalence. -/
theorem integralConstantModule_exact (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    PreservesFiniteLimits (integralConstantModule T d) ∧
      PreservesFiniteColimits (integralConstantModule T d) := by
  let dd : ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  let K := adicLisseConstantModules T A
  let E := completedConstantExtension T (adicDatumScalar T dd)
  let R := pbcRestrict (pbcCompletedComparison T d).inv
  have hK : PreservesFiniteLimits K ∧ PreservesFiniteColimits K := by
    let P : ModuleCat.{u + 1} A ⥤
      _root_.PresheafOfModules.{u + 1}
        ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) :=
      siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
        PresheafOfModules.pushforward₀
          ((Functor.const T.ProEt).obj (Discrete.mk (ULift.up ())))
          ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))
    have hP : PreservesFiniteLimits P := by
      constructor
      intro J _ _
      constructor
      intro F
      constructor
      intro c hc
      exact ⟨_root_.PresheafOfModules.evaluationJointlyReflectsLimits _ _
        (fun X ↦ hc)⟩
    have hP' : PreservesFiniteColimits P := by
      constructor
      intro J _ _
      constructor
      intro F
      constructor
      intro c hc
      exact ⟨_root_.PresheafOfModules.evaluationJointlyReflectsColimits _ _
        (fun X ↦ hc)⟩
    exact ⟨comp_preservesFiniteLimits P
      (PresheafOfModules.sheafification (adicLisseConstantUnit T A)),
      comp_preservesFiniteColimits P
        (PresheafOfModules.sheafification (adicLisseConstantUnit T A))⟩
  have hE : PreservesFiniteLimits E ∧ PreservesFiniteColimits E := by
    let := dd.toCompleteCoefficientDatum.noetherian
    have h := completed_constant_algebra_flat_quotients T dd.ideal
      _ (Iso.refl _) (adicDatumScalar T dd) (by
        intro n
        exact (adicDatumScalar_exists T dd).exists.choose_spec n)
    have he := (exactFunctor_iff E).1 h.2.1
    exact ⟨he.1, he.2⟩
  let := hK.1
  let := hK.2
  let := hE.1
  let := hE.2
  exact ⟨comp_preservesFiniteLimits (K ⋙ E) R,
    comp_preservesFiniteColimits (K ⋙ E) R⟩

/-- Additivity of completed-constant realization, inherited from its two factors.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
instance integralConstantModule_additive (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : (integralConstantModule T d).Additive :=
  letI := (integralConstantModule_exact T d).1
  Functor.additive_of_preserves_binary_products _

/-- The derived realization P ↦ A_T ⊗^L_A P, obtained by localizing the exact
ordinary constant-module realization. On bounded finite projective complexes this
is its termwise tensor realization.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def integralConstantDerived (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : completedConstantDerived (ModuleCat.{u + 1} A) ⥤
      DerivedCategory (pbcModules T (pbcAdicCompletion T d)) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  letI := (integralConstantModule_exact T d).1
  letI := (integralConstantModule_exact T d).2
  (integralConstantModule T d).mapDerivedCategory

/-- Restrict a derived object first to a stratum and then to a covering site object.
The slice coefficient sheaf is the restriction of the actual inverse-image ring.
Source: Bhatt--Scholze, Proposition 6.6.11; Stacks Tags 0997 and 0998
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def integralLocalDerived {T S : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt)
    (K : DerivedCategory (pbcModules T R)) :
    completedConstantDerived (SheafOfModules.{u + 1}
      (((adicLisseForget S).obj ((adicTowerInverseImage g).obj R)).over U)) :=
  ringedSiteDerivedRestrictionOfUniverses
    ((adicLisseForget S).obj ((adicTowerInverseImage g).obj R)) U
    ((adicTowerPullback g R).obj K)

/-- Condition (ii): finite strata, on each a pro-etale covering sieve, and on each
cover member an actual perfect A-complex whose completed realization is K there.
IsPerfectRingComplex is the recorded bounded finite-projective notion.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def IsIntegralStratifiedPerfect (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) : Prop :=
  ∃ s : Stratification T, ∀ i : Fin s.n,
    ∃ V : Sieve (⊤_ (s.domain i).ProEt),
      V ∈ ProEt.topology (s.domain i) (⊤_ (s.domain i).ProEt) ∧
        ∀ (U : (s.domain i).ProEt) (f : U ⟶ ⊤_ (s.domain i).ProEt), V f →
          ∃ P : completedConstantDerived (ModuleCat.{u + 1} A),
            @DerivedCategory.IsPerfectRingComplex A _
              (HasDerivedCategory.standard (ModuleCat.{u + 1} A)) P ∧
              Nonempty (integralLocalDerived (s.immersion i) (pbcAdicCompletion T d) U K ≅
                integralLocalDerived (s.immersion i) (pbcAdicCompletion T d) U
                  ((integralConstantDerived T d).obj P))

/-- The constructible integral sheaf condition: finite strata and locally the ordinary
completed realization of a finitely presented A-module, including the zero module.
Source: Bhatt--Scholze, Definition 6.8.10
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def IsIntegralStratifiedFinitelyPresented (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (F : pbcModules T (pbcAdicCompletion T d)) : Prop :=
  ∃ s : Stratification T, ∀ i : Fin s.n,
    ∃ V : Sieve (⊤_ (s.domain i).ProEt),
      V ∈ ProEt.topology (s.domain i) (⊤_ (s.domain i).ProEt) ∧
        ∀ (U : (s.domain i).ProEt) (f : U ⟶ ⊤_ (s.domain i).ProEt), V f →
          ∃ N : ModuleCat.{u + 1} A, Module.FinitePresentation A N ∧
            Nonempty ((SheafOfModules.overFunctor _ U).obj
              ((proEtaleModuleInverseImage (s.immersion i) (pbcAdicCompletion T d)).obj F) ≅
              (SheafOfModules.overFunctor _ U).obj
                ((proEtaleModuleInverseImage (s.immersion i) (pbcAdicCompletion T d)).obj
                  ((integralConstantModule T d).obj N)))

/-- Condition (iii): boundedness and the stated finitely presented local models for
all cohomology sheaves. The finite stratification may depend on the cohomological degree.
Source: Bhatt--Scholze, Proposition 6.8.11(3)
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def IsIntegralBoundedConstructibleCohomology (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) : Prop :=
  (∃ a b : ℤ, a ≤ b ∧ K.IsGE a ∧ K.IsLE b) ∧
    ∀ q : ℤ, IsIntegralStratifiedFinitelyPresented T d
      ((DerivedCategory.homologyFunctor (pbcModules T (pbcAdicCompletion T d)) q).obj K)

end AlgebraicGeometry.Scheme
