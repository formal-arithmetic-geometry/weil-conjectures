/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.IntegralConstructibleCompactness
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Sheaf.Paper.CartesianCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.Paper.DerivedNakayamaResolution
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import Sheaf.AlgebraicGeometry.DimensionBaseChange
import Sheaf.AlgebraicGeometry.DimensionAffineOpenCover
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence
import Sheaf.AlgebraicGeometry.ProperHeartContinuityDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Sheaf.AlgebraicGeometry.ProEtaleLeftComplete
import Sheaf.CategoryTheory.Triangulated.LeftCompleteHeartUpperBound
import Sheaf.Paper.LocalizingClosureExistence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Paper.IntegralCohomologicalAdicCriterion
import Sheaf.Paper.IntegralProperBaseChange
import Sheaf.Paper.IntegralConstructibleHeart

/-!
# Integral proper direct image on localizing categories

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-int-compactness,
sk-prop-int-compactness-direct-sums.md and its proof
(blueprint: det-prop-int-compactness-direct-sums).

The assertion bundle only expands the three conclusions. The theorem specializes it
at the actual ordinary unbounded module-object derived pushforward and the recorded
finite constant-model constructible predicates. IndCons is `ObjectProperty.ind`;
Dic is expanded by testing all cohomology objects. Coproduct preservation uses mapped
cofans, so all their legs are the images of the original coprojections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u₁ u₂ u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The three integral proper direct-image assertions, expanded in ordinary derived
categories. `H₁.ind` and `H₂.ind` are ambient small filtered-colimit closures.
The two `IsIso` statements use the canonical arrows of the truncation zigzag.
For sums, a colimit cofan exists and remains a colimit after applying `F`; its
legs are exactly `F.map` of the source injections. Uniqueness of coproducts makes
this equivalent to invertibility of the canonical coproduct comparison.
Source: blueprint main-20261015, sk-prop-int-compactness-direct-sums, clauses 1--3
(blueprint: det-prop-int-compactness-direct-sums). -/
def IntegralProperDirectImageAssertions
    {A : Type u₁} {B : Type u₂} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{v} A] [HasDerivedCategory.{v} B]
    (H₁ : ObjectProperty A) (H₂ : ObjectProperty B)
    (C₁ : ObjectProperty (DerivedCategory A)) (C₂ : ObjectProperty (DerivedCategory B))
    (F : DerivedCategory A ⥤ DerivedCategory B) (d : ℕ) : Prop :=
  (∀ N : A, H₁ N →
    C₂ (F.obj ((DerivedCategory.singleFunctor A 0).obj N)) ∧
    (F.obj ((DerivedCategory.singleFunctor A 0).obj N)).IsGE 0 ∧
    (F.obj ((DerivedCategory.singleFunctor A 0).obj N)).IsLE (2 * (d : ℤ) + 1)) ∧
  (∀ N : A, H₁.ind.{v} N →
    (∀ q : ℤ, H₂.ind.{v} ((DerivedCategory.homologyFunctor B q).obj
      (F.obj ((DerivedCategory.singleFunctor A 0).obj N)))) ∧
    (F.obj ((DerivedCategory.singleFunctor A 0).obj N)).IsGE 0 ∧
    (F.obj ((DerivedCategory.singleFunctor A 0).obj N)).IsLE (2 * (d : ℤ) + 1)) ∧
  (∀ K : DerivedCategory A,
    (∀ n : ℤ, H₁.ind.{v} ((DerivedCategory.homologyFunctor A n).obj K)) →
    ∀ q : ℤ,
      IsIso ((DerivedCategory.homologyFunctor B q).map
        (F.map ((DerivedCategory.TStructure.t.truncLEι q).app K))) ∧
      IsIso ((DerivedCategory.homologyFunctor B q).map
        (F.map ((DerivedCategory.TStructure.t.truncGEπ (q - 2 * (d : ℤ) - 1)).app
          ((DerivedCategory.TStructure.t.truncLE q).obj K))))) ∧
  (∀ (I : Type v) (K : I → DerivedCategory A),
    (∀ (i : I) (n : ℤ), H₁.ind.{v} ((DerivedCategory.homologyFunctor A n).obj (K i))) →
    ∃ c : Cofan K, Nonempty (IsColimit c) ∧ Nonempty (IsColimit (F.mapCocone c))) ∧
  (∀ K : DerivedCategory A, localizingClosure C₁ K → localizingClosure C₂ (F.obj K)) ∧
  (∀ (I : Type v) (K : I → DerivedCategory A),
    (∀ i : I, localizingClosure C₁ (K i)) →
    ∃ c : Cofan K, Nonempty (IsColimit c) ∧ Nonempty (IsColimit (F.mapCocone c)))

/-- Integral proper direct image has the heart bound `[0,2d+1]`, the canonical
finite-window property, and preserves arbitrary sums on Dic and on Loc(Dbc).
Source: blueprint main-20261015, sk-prop-int-compactness-direct-sums, all three clauses
(blueprint: det-prop-int-compactness-direct-sums).

Proof plan, following the eleven steps of the DAG:
1. Properness gives finite type and separatedness, hence qcqs. The module pushforward
   is left exact, and the exact coefficient-compatible pullback gives the derived
   adjunction. Thus F = Rp_* preserves products, is triangulated, and preserves
   lower cohomological bounds. Internal modules identify with sectionwise module
   sheaves, which are Grothendieck abelian and have unbounded K-injective resolutions.
2. The integral heart and proper-base-change preservation put FN in Dbc for N in Cons.
   Finite type over the Noetherian field makes X Noetherian. The integral adic criterion,
   integral coefficient limit, one-generator Koszul-completion reflector and two-term
   quotient resolution identify N with the reduction tower's derived limit. The strict
   tower theorem supplies its Roos triangle with the prescribed transitions.
3. Each reduction N_n is the cone of pi^n on N and has cohomology in [-1,0].
   Its first reduction is classical by the adic criterion. Quotient-resolution triangles
   and the exact fully faithful classical comparison lift all reductions to etale
   torsion complexes C_n with cohomology in [-1,0]. No flatness of N is assumed.
4. The proper torsion bound gives upper bound 2d for Rp_et,* C_n. Dimension base change
   and affine-cover dimension turn the geometric-fibre hypothesis into its fibre bound.
   Discrete direct-image comparison and ringed-topos composition with exact coefficient
   restriction identify the underlying abelian images, hence FN_n is at most 2d.
5. Apply F to the Roos triangle; product preservation retains its projections and
   transitions. Exact countable products and the derived-product theorem compute
   these products termwise. Represent the image tower by a strict K-injective tower;
   TR3 identifies its product cone with FN. The Milnor sequence gives upper bound
   2d+1, and negative vanishing gives the lower bound zero.
6. Present N in IndCons as a small filtered colimit of constructibles. Proper heart
   continuity, then exact colimit-preserving restriction along O_Y -> p_*O_X,
   identifies H^q FN with the filtered colimit of H^q FN_i. This proves both membership
   in IndCons and the bound, and supplies sheaf-level direct-sum continuity.
7. Exact countable products, the derived-product theorem and pro-etale left completeness
   allow the class-relative heart-upper-bound lemma to extend this bound to any
   bounded-above L in Dic, including an unbounded negative tail. Good truncations
   remain in Dic by integral constructible compactness.
8. Apply the upper truncation triangle at q: lower-bound preservation kills its tail
   in degrees q-1 and q. Apply the lower triangle at q-2d-1: step 7 puts its tail
   at most q-1. The long exact sequences give precisely the two asserted IsIso maps.
9. Induct on a common finite cohomological interval for a family. The one-degree case
   is step 6; summed truncation triangles and the five lemma give the induction step.
   Exact filtered colimits make sums exact, commuting with cohomology and truncations.
10. In each output degree q replace every summand and its sum by the common window
    [q-2d-1,q]. Step 9 handles that bounded family. Naturality of both actual truncation
    arrows identifies the canonical comparison, hence it is an iso in every degree
    and therefore an iso in the derived category.
11. Integral compactness puts Loc(Dbc_X) inside Dic. The full subcategory of objects
    in Loc(Dbc_X) whose F-images belong to Loc(Dbc_Y) contains Dbc_X by proper
    preservation and is replete, triangulated and sum closed by steps 1 and 10.
    Minimality of the localizing closure proves preservation; step 10 gives its sums. -/
theorem integralProperDirectSums
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞)) :
    IntegralProperDirectImageAssertions
      (IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X)
      (IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) Y)
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X)
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) Y)
      (CondensedRing.lowerStar (Profinite.padicIntegersRingObj ℓ E) p).rightDerivedFunctor d := by
  sorry

end AlgebraicGeometry.ProEtale
