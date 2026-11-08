/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingTensorTor
import Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import Mathlib.AlgebraicGeometry.Noetherian
import Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingPullbackFixed
import Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteScalarConstantModels
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackEncoding
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import all Mathlib.Algebra.Category.Ring.Colimits
import all Mathlib.FieldTheory.IsAlgClosed.Basic
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Point.Over
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import all Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all Mathlib.CategoryTheory.Functor.TypeValuedFlat
import all Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Finite constant models and finite-stalk constructibility

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-integral-criterion-reductions.proof.md, second paragraph; Stacks Tags 099Y and 09AJ
(blueprint: lem-pe-finite-coefficient-model-comparison).

The coefficient encoding is the normalized section-action equivalence already supplied by
FiniteDiscreteOrdinary. The witness clauses retain each stratum and each cover. Arbitrary
constant values on empty covering objects are discarded before asserting their finiteness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The finite geometric-stalk clause of the existing ordinary constructibility definition,
without its separate local-constancy clause. No field characteristic is excluded.
Source: Stacks Tag 09AJ, definition-constructible
(blueprint: lem-pe-finite-coefficient-model-comparison). -/
def ordinaryFiniteStalks (T : Scheme.{u}) (F : Ordinary A T) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T),
    Finite (Scheme.proEtaleGeometricModuleStalk x (Scheme.proEtaleConstantRing T A) F)

/-- The ordinary local condition on one stratum, using the recorded localized-site
local constancy and actual geometric stalks, rather than etale origin or finite Tor amplitude.
Source: Stacks Tag 09AJ, definition-constructible
(blueprint: lem-pe-finite-coefficient-model-comparison). -/
def ordinaryFiniteLocalCondition (T : Scheme.{u}) (F : Ordinary A T) : Prop :=
  Scheme.IsLocallyConstantProEtaleModuleSheaf T A F ∧ ordinaryFiniteStalks A T F

/-- Finite constant ordinary models on a specified cover. Module pullback uses the canonical
constant-coefficient comparison, and the constant model is simultaneous ring/module
sheafification. This spells out the ordinary side of the same-cover comparison.
Source: Stacks Tag 099Y, lemma-compare-locally-constant
(blueprint: lem-pe-finite-coefficient-model-comparison). -/
def ordinaryFiniteCoverModels (T : Scheme.{u}) (F : Ordinary A T)
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage T) : Prop :=
  ∀ i : C.I₀, ∃ P : ModuleCat.{u + 1} (ULift.{u + 1} A), Finite P ∧
    Nonempty (Scheme.proEtaleConstantModulePullback (C.f i) A F ≅
      Scheme.proEtaleConstantModuleSheaf (C.X i) A P)

/-- Bounded constructibility in the intrinsic ordinary constant-ring module category:
standard bounded cohomology and the existing finite-stalk constructibility predicate in
every degree. This is the ordinary target of the comparison, with no Tor restriction.
Source: blueprint sk-def-sfb-constructible, final paragraph; Stacks Tag 09AL
(blueprint: lem-pe-finite-coefficient-model-comparison). -/
def ordinaryIntrinsicBoundedConstructible [Finite A] (T : Scheme.{u}) :
    ObjectProperty (Scheme.proEtaleDerivedCategory T A) :=
  DerivedCategory.TStructure.t.bounded ⊓ fun K ↦ ∀ q : ℤ,
    Scheme.IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor (Ordinary A T) q).obj K)

/-- All clauses of the finite-coefficient comparison for the specified normalized encoding.
The stratum clauses are pointwise, so zero strata and empty strata are included. The global
ordinary predicate retains its recorded convention of a positive number of strata.
Source: blueprint sk-prop-integral-criterion-reductions.proof.md, second paragraph;
Stacks Tags 099Y and 09AJ (blueprint: lem-pe-finite-coefficient-model-comparison). -/
structure FiniteCoefficientModelComparison [Finite A] (X : Scheme.{u}) (e : Encoding A X) :
    Prop where
  /-- Constructibility agrees for the original sheaf and its section-action image. -/
  constructible : ∀ M : Internal A X,
    IsConstantModelConstructible (coefficient A) X M ↔
      Scheme.IsConstructibleProEtaleModuleSheaf X A (e.ordinary.functor.obj M)
  /-- On every fixed stratification, exactly the same strata satisfy the local conditions. -/
  strata : ∀ (M : Internal A X) (S : Scheme.Stratification X),
    (∀ i : Fin S.n, HasFiniteConstantLocalModel (coefficient A) (S.domain i)
      ((CondensedRing.upperStar (coefficient A) (S.immersion i)).obj M)) ↔
    ∀ i : Fin S.n, ordinaryFiniteLocalCondition A (S.domain i)
      (Scheme.proEtaleConstantModulePullback (S.immersion i) A (e.ordinary.functor.obj M))
  /-- A finite model cover remains the very same finite model cover in ordinary coordinates. -/
  covers : ∀ (M : Internal A X) (S : Scheme.Stratification X) (i : Fin S.n)
      (C : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain i)),
    HasFiniteConstantLocalModelOnCover (coefficient A)
      ((CondensedRing.upperStar (coefficient A) (S.immersion i)).obj M) C ↔
    ordinaryFiniteCoverModels A (S.domain i)
      (Scheme.proEtaleConstantModulePullback (S.immersion i) A (e.ordinary.functor.obj M)) C
  /-- Every localized-site trivialization is retained on its nonempty members. This uses
  the full index universe of the recorded ordinary local-constancy definition. -/
  discardEmpty : ∀ (M : Internal A X) (S : Scheme.Stratification X) (i : Fin S.n)
      (I : Type (u + 1)) (W : I → (S.domain i).ProEt)
      (f : ∀ j : I, W j ⟶ Scheme.ProEt.mk (𝟙 (S.domain i)))
      (P : I → ModuleCat.{u + 1} (ULift.{u + 1} A)),
    Presieve.ofArrows W f ∈ (Scheme.ProEt.precoverage (S.domain i)).coverings _ →
    (∀ j : I,
      Nonempty ((Scheme.proEtaleConstantModulePullback (S.immersion i) A
        (e.ordinary.functor.obj M)).over (W j) ≅
          Scheme.proEtaleConstantModuleSheafOver (S.domain i) A (W j) (P j))) →
    ordinaryFiniteStalks A (S.domain i)
      (Scheme.proEtaleConstantModulePullback (S.immersion i) A (e.ordinary.functor.obj M)) →
    (Presieve.ofArrows (fun j : {j : I // Nonempty (W j).left} ↦ W j.val)
      (fun j ↦ f j.val) ∈ (Scheme.ProEt.precoverage (S.domain i)).coverings _) ∧
    ∀ j : I, Nonempty (W j).left → Finite (P j) ∧
      ∃ Q : Mod Ab.{u + 1} (scalarRingObj (coefficient A)),
        Mod.IsFinitelyPresented (scalarRingObj (coefficient A)) Q ∧
        Nonempty ((CondensedRing.upperStar (coefficient A) (W j).hom).obj
          ((CondensedRing.upperStar (coefficient A) (S.immersion i)).obj M) ≅
            (finiteConstantScalarExtension (coefficient A) (W j).left).obj Q)
  -- STATEMENT-DISPUTED: the former unparenthesized equivalence was false for b < a.
  /-- The actual termwise derived equivalence preserves and reflects each vanishing interval. -/
  intervals : ∀ (K : DerivedCategory (Internal A X)) (a b : ℤ), a ≤ b →
    ((∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor (Internal A X) q).obj K)) ↔
    (∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor (Ordinary A X) q).obj
        (e.ordinaryDerived.functor.obj K))))
  /-- Both bounded-constructible membership tests agree, without a finite-Tor condition. -/
  boundedConstructible : ∀ K : DerivedCategory (Internal A X),
    constantModelBoundedConstructible (coefficient A) X K ↔
      ordinaryIntrinsicBoundedConstructible A X (e.ordinaryDerived.functor.obj K)
  /-- The equivalence on the full subcategories is induced by the specified ambient functor. -/
  boundedEquivalence : ∃ d : ConstantModelBoundedConstructible (coefficient A) X ≌
      (ordinaryIntrinsicBoundedConstructible A X).FullSubcategory,
    Nonempty (d.functor ⋙ (ordinaryIntrinsicBoundedConstructible A X).ι ≅
      (constantModelBoundedConstructible (coefficient A) X).ι ⋙ e.ordinaryDerived.functor)

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem constructible_of_iso [Finite A] (T : Scheme.{u})
    {F G : Ordinary A T} (e : F ≅ G)
    (hF : Scheme.IsConstructibleProEtaleModuleSheaf T A F) :
    Scheme.IsConstructibleProEtaleModuleSheaf T A G := by
  obtain ⟨S, hn, hS⟩ := hF
  refine ⟨S, hn, fun i ↦ ?_⟩
  let e' := (Scheme.proEtaleConstantRingPullback A (S.immersion i)).mapIso e
  obtain ⟨I, U, f, hc, ht⟩ := (hS i).1
  refine ⟨⟨I, U, f, hc, fun j ↦ ?_⟩, ?_⟩
  · obtain ⟨P, ⟨hP⟩⟩ := ht j
    exact ⟨P, ⟨(SheafOfModules.overFunctor _ (U j)).mapIso e'.symm ≪≫ hP⟩⟩
  · intro Ω _ _ y
    let E := Scheme.geometricRingModuleStalkFunctor y
      (Scheme.proEtaleConstantRing (S.domain i) A)
    have : Finite (E.obj ((Scheme.proEtaleConstantRingPullback A
        (S.immersion i)).obj F)) := (hS i).2 Ω y
    exact Finite.of_injective (E.mapIso e'.symm).toLinearEquiv
      (E.mapIso e'.symm).toLinearEquiv.injective

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
