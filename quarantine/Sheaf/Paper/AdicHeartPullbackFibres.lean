/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Sheaf.Paper.LocalizedTStructure
public import Sheaf.Paper.PbcQbarCategory
public import Sheaf.Paper.LisseAdicSheaves
public import Sheaf.Paper.PbcActualStrictPullback
public import Sheaf.Paper.PbcDescentFunctors
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.Constructible
public import Mathlib.CategoryTheory.Whiskering
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.Paper.CompletedPullbackTriangles

import Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import Sheaf.CategoryTheory.SemilinearScalarLocalization
import Sheaf.CategoryTheory.StageSystemFunctorDescent
import Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Sheaf.Paper.ContinuousAffineEtaleLattice
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.GaloisLisseRepresentations
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.RepresentationTheory.Rep.Basic
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.Paper.LisseAdicFiberFunctors
import Sheaf.Paper.LisseModuleSheaves
import Sheaf.RepresentationTheory.LAdic
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Paper.IntegralTStructure
import Sheaf.Paper.LisseTensorScalarExtension
import Sheaf.Paper.PbcRationalCategory
import Sheaf.Paper.PbcScalarExtension
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-! # Constructible adic hearts, pullback, and geometric coefficient fibres

Source: Bhatt--Scholze, The pro-etale topology for schemes, Section 6.8,
Lemmas 6.8.2 and 6.8.7, Definitions 6.8.3, 6.8.6, 6.8.8 and 6.8.10,
Propositions 6.8.4, 6.8.11 and 6.8.14, and Remark 6.8.15
(blueprint: lem-per-adic-heart-pullback-fibres).

The finite-stage categories are the recorded raw localizations, and the algebraic
coefficient category is the recorded common-stage pair category. The fibres below
are normalized by completed geometric pullback, degree-zero cohomology, evaluation
at the final pro-etale object, and inversion of the uniformizer.

## Main definitions

* `rationalT`, `commonT`: the prescribed finite and common-stage standard t-structures.
* `rationalPull`, `commonPull`: the normalized actual completed pullback functors.
* `integralFiber`, `integralLimitFiber`, `fiber`: completed-section and adic-limit fibres.

## Main statement

* `adicHeartPullbackFibres`: all standard-heart, scalar, pullback and geometric-fibre clauses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v r s
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.PerAdic

/-- A separated finite-type k-scheme; no geometric connectedness or nonemptiness is imposed.
Source: BS 6.8, geometric hypotheses (blueprint: lem-per-adic-heart-pullback-fibres). -/
structure Base (k : Type u) [Field k] where
  scheme : Scheme.{u}
  [over : scheme.Over (Spec (.of k))]
  [finiteTypeLocal : LocallyOfFiniteType (scheme ↘ Spec (.of k))]
  [finiteTypeCompact : QuasiCompact (scheme ↘ Spec (.of k))]
  [separated : IsSeparated (scheme ↘ Spec (.of k))]

attribute [instance] Base.over Base.finiteTypeLocal Base.finiteTypeCompact Base.separated

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [hl : Fact (IsUnit (l : k))]

include hl in
/-- Finite type over a field gives exactly the hypotheses of the recorded adic categories.
Source: BS 6.8.11 and 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres).
Proof: finite type over the noetherian one-point scheme Spec k gives noetherianity.
The finite-type fibre-dimension bound on its unique fibre gives a finite dimension bound.
The unit l in k maps to a unit in every local ring of the scheme. -/
theorem base_properties (W : Base k) :
    IsNoetherian W.scheme ∧ (∃ n : ℕ, topologicalKrullDim W.scheme ≤ n) ∧
      (∀ x : W.scheme, IsUnit (l : W.scheme.presheaf.stalk x)) := by
  sorry

/-- The two geometric finiteness properties do not depend on the coefficient prime.
Source: BS 6.8 (blueprint: lem-per-adic-heart-pullback-fibres).
Proof: finite type over the noetherian affine point gives noetherianity; the sole
fibre of the structure morphism has a finite dimension bound by
lem-fin-finite-type-fibre-dimension-bound. -/
theorem base_geometric_properties (W : Base k) :
    IsNoetherian W.scheme ∧ (∃ n : ℕ, topologicalKrullDim W.scheme ≤ n) := by
  sorry

/-- The noetherian structure supplied by the finite-type hypothesis.
Source: BS 6.8 (blueprint: lem-per-adic-heart-pullback-fibres). -/
instance baseNoetherian (W : Base k) : IsNoetherian W.scheme :=
  (base_geometric_properties W).1

/-- The finite dimension bound supplied by the finite-type hypothesis.
Source: BS 6.8 (blueprint: lem-per-adic-heart-pullback-fibres). -/
instance baseDimension (W : Base k) : Fact (∃ n : ℕ, topologicalKrullDim W.scheme ≤ n) :=
  ⟨(base_geometric_properties W).2⟩

/-- Invertibility of the coefficient prime on every local ring.
Source: BS 6.8 (blueprint: lem-per-adic-heart-pullback-fibres). -/
instance basePrimeUnit (W : Base k) : Fact (∀ x : W.scheme,
    IsUnit (l : W.scheme.presheaf.stalk x)) :=
  ⟨(base_properties l W).2.2⟩

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The recorded localized standard t-structure; its classes are fixed by integral images.
Source: BS 6.8.11 and 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def rationalT (W : Base k) :
    Triangulated.TStructure
      (PbcRationalCategory W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)) :=
  @Classical.choose _ _ (pbc_localized_tstructure W.scheme l E
    (hNoeth := baseNoetherian W) (hDim := baseDimension W)
    (hInv := basePrimeUnit l W))

/-- The recorded finite-stage aisle, exposed as an object predicate independently
of competing stage shift instances. Source: BS 6.8.11
(blueprint: lem-per-adic-heart-pullback-fibres). -/
abbrev rationalLE (W : Base k) (n : ℤ) :
    ObjectProperty (PbcRationalCategory W.scheme (pbcIntegralDatum l E)
      (pbcUniformizer l E)) := (rationalT l E W).le n

/-- The recorded finite-stage coaisle, exposed as an object predicate.
Source: BS 6.8.11 (blueprint: lem-per-adic-heart-pullback-fibres). -/
abbrev rationalGE (W : Base k) (n : ℤ) :
    ObjectProperty (PbcRationalCategory W.scheme (pbcIntegralDatum l E)
      (pbcUniformizer l E)) := (rationalT l E W).ge n

/-- The recorded finite-stage upper truncation, with its actual shift instance fixed.
Source: BS 6.8.11 (blueprint: lem-per-adic-heart-pullback-fibres). -/
abbrev rationalTruncLE (W : Base k) (n : ℤ) :
    PbcRationalCategory W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤
      PbcRationalCategory W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) :=
  (rationalT l E W).truncLE n

/-- The recorded finite-stage lower truncation, with its actual shift instance fixed.
Source: BS 6.8.11 (blueprint: lem-per-adic-heart-pullback-fibres). -/
abbrev rationalTruncGE (W : Base k) (n : ℤ) :
    PbcRationalCategory W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤
      PbcRationalCategory W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) :=
  (rationalT l E W).truncGE n

/-- The finite-coefficient constructible heart is the actual full t-heart.
Source: BS 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
abbrev Heart (W : Base k) := (rationalT l E W).heart.FullSubcategory

/-- The literal cohomology-in-degree-zero formula, for any indexed standard t-structure.
Source: BS 6.8.11, standard cohomology (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def cohomology {C : Type r} [Category.{s} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (t : Triangulated.TStructure C) (r : ℤ) : C ⥤ C :=
  t.truncLE r ⋙ t.truncGE r ⋙ shiftFunctor C r

/-- Finite-stage cohomology with the recorded localized shift fixed explicitly.
Source: BS 6.8.11 (blueprint: lem-per-adic-heart-pullback-fibres). -/
abbrev rationalCohomology (W : Base k) (n : ℤ) :
    PbcRationalCategory W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤
      PbcRationalCategory W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) :=
  cohomology (rationalT l E W) n

include hl in
/-- Completed pullback preserves the integral constructible category, including its origins.
Source: BS 6.8.2 and Remark 6.8.15 (blueprint: lem-per-adic-heart-pullback-fibres).
Proof: use the completed-pullback comparison on finite reductions. Pull back the finite
locally closed stratification and its bounded finite local models. Finite etale origins
pull back to compatible origins, and derived completion supplies completeness. The
finite-level quotient comparisons preserve the transition and normalization equations. -/
theorem integralPull_mem {V T : Base k} (h : V.scheme ⟶ T.scheme)
    (K : PbcBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)) :
    PbcIsBoundedConstructibleComplete V.scheme (pbcIntegralDatum l E)
      ((pbcActualCompletedPull h (pbcIntegralDatum l E)).obj K.obj) := by
  sorry

/-- The actual completed pullback on integral objects and arrows, rationalized on tensor Homs.
Source: BS Remark 6.8.15 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def rationalPull {V T : Base k} (h : V.scheme ⟶ T.scheme) :
    PbcRationalCategory T.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤
      PbcRationalCategory V.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) :=
  pbcConditionalRational (pbcIntegralDatum l E)
    (pbcActualCompletedPull h (pbcIntegralDatum l E)) (integralPull_mem l E h)
      (pbcUniformizer l E)

/-- The integer ring acts on geometric point sections through its constant sections.
Source: BS 6.8.4 and 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def pointSections (Ω : Type u) [Field Ω] :
    pbcModules (Spec (.of Ω)) (pbcAdicCompletion (Spec (.of Ω)) (pbcIntegralDatum l E)) ⥤
      ModuleCat.{u + 1} (PbcIntegralRing l E) :=
  SheafOfModules.evaluation _ (op (ProEt.mk (𝟙 (Spec (.of Ω))))) ⋙
    ModuleCat.restrictScalars (pbcCompletedSection (Spec (.of Ω)) (pbcIntegralDatum l E)
      (op (ProEt.mk (𝟙 (Spec (.of Ω))))))

/-- The actual inclusion of the lifted integer ring in its coefficient field.
Source: BS 6.8.14, rationalization (blueprint: lem-per-adic-heart-pullback-fibres). -/
def integerToField : PbcIntegralRing l E →+* E :=
  (Padic.coefficientExtensionIntegers l E).subtype.comp ULift.ringEquiv.toRingHom

/-- The finite-stage geometric fibre on integral representatives, before descending fractions.
Source: BS 6.8.4 and 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def integralFiber (W : Scheme.{u}) {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ W) : PbcBoundedConstructibleComplete W (pbcIntegralDatum l E) ⥤
      ModuleCat.{u + 1} E :=
  ObjectProperty.ι (PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E)) ⋙
    pbcActualCompletedPull x (pbcIntegralDatum l E) ⋙
    DerivedCategory.homologyFunctor _ 0 ⋙ pointSections l E Ω ⋙
    ModuleCat.extendScalars (integerToField l E)

/-- The strict finite-quotient fibre tower, followed by its ordinary inverse limit
and inversion of the uniformizer. The strict tower retains every quotient transition.
Source: BS 6.8.4; the inverse-limit prescription of def-pod-lisse-l-adic-sheaves
(blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def integralLimitFiber (W : Scheme.{u}) {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ W) : PbcBoundedConstructibleComplete W (pbcIntegralDatum l E) ⥤
      ModuleCat.{u + 1} E :=
  ObjectProperty.ι (PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E)) ⋙
    pbcActualCompletedPull x (pbcIntegralDatum l E) ⋙
    completedReductionTower (Spec (.of Ω)) (pbcIntegralDatum l E) ⋙
    DerivedCategory.homologyFunctor _ 0 ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pointSections l E Ω) ⋙
    (lim : (ℕᵒᵖ ⥤ ModuleCat.{u + 1} (PbcIntegralRing l E)) ⥤
      ModuleCat.{u + 1} (PbcIntegralRing l E)) ⋙
    ModuleCat.extendScalars (integerToField l E)

/-- The integral geometric fibre descends uniquely on all rational arrows.
Source: BS 6.8.4 and 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres).
Proof: every integral arrow acts on completed point sections. Uniformizer multiplication
becomes invertible after tensoring with E. The localization universal property therefore
extends the functor uniquely, with f/pi^n acting as pi^(-n) times the integral fibre map.
The pure-fraction formula proves uniqueness and preserves the functor laws. -/
theorem fiber_existsUnique (W : Scheme.{u}) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ W) :
    ∃! F : PbcRationalCategory W (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤
        ModuleCat.{u + 1} E,
      pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙ F =
        integralFiber l E W x := by
  sorry

/-- The geometric coefficient fibre determined by actual completed pullback and rationalization.
Source: BS 6.8.4 and 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def fiber (W : Scheme.{u}) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ W) :
    PbcRationalCategory W (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤
      ModuleCat.{u + 1} E :=
  (fiber_existsUnique l E W x).exists.choose

/-- The degree-zero finite-stage heart fibre functor.
Source: BS 6.8.4 and 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def heartFiber (W : Base k) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ W.scheme) : Heart l E W ⥤ ModuleCat.{u + 1} E :=
  ObjectProperty.ι (rationalT l E W).heart ⋙ fiber l E W.scheme x


/-- Rationalized ambient restriction along a scheme map, on its actual integral model.
Source: BS Remark 6.8.15 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def ambientPull {X W : Scheme.{u}} (h : X ⟶ W)
    (K : PbcRationalCategory W (pbcIntegralDatum l E) (pbcUniformizer l E)) :=
  (ScalarLocalization.localization (PbcIntegralRing l E)
    (PbcCompletedDerived X (pbcIntegralDatum l E)) (pbcUniformizer l E)).obj
      ((pbcActualCompletedPull h (pbcIntegralDatum l E)).obj K.obj.obj)

/-- The finite free completed coefficient sheaf, in degree zero and then rationalized.
Source: BS Definition 6.8.3 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def freeObject (W : Scheme.{u}) (n : ℕ) :=
  (ScalarLocalization.localization (PbcIntegralRing l E)
    (PbcCompletedDerived W (pbcIntegralDatum l E)) (pbcUniformizer l E)).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.free (R := (adicLisseForget W).obj
          (pbcAdicCompletion W (pbcIntegralDatum l E))) (ULift.{u + 1} (Fin n))))

/-- Lissity on a finite locally closed stratification: actual completed restriction is
pro-etale locally a finite free coefficient object in degree zero, after rationalization.
Source: BS Definitions 6.8.3 and 6.8.6 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def LisseStrata (W : Scheme.{u})
    (K : PbcRationalCategory W (pbcIntegralDatum l E) (pbcUniformizer l E))
    (S : FiniteLocallyClosedStratification W) : Prop :=
  ∀ i : Fin S.n, ∃ C : (S.domain i).Cover.{u} proetalePrecoverage,
    ∀ j : C.I₀, ∃ n : ℕ,
      Nonempty (ambientPull l E (C.f j ≫ S.immersion i) K ≅ freeObject l E (C.X j) n)

/-- The finite-coefficient clauses, stated on the actual rational category, pullback,
and point-normalized fibre functors. Source: BS Section 6.8
(blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def RationalStandardAssertions (W : Base k) : Prop :=
  (rationalT l E W).bounded = ⊤ ∧
    (∀ X : PbcRationalCategory W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E),
      ((rationalT l E W).le 0 X ↔
        ∃ L : PbcBoundedConstructibleComplete W.scheme (pbcIntegralDatum l E),
          (pbcIntegralTStructure W.scheme l E).le 0 L ∧
            Nonempty (X ≅ (pbcRationalization W.scheme (pbcIntegralDatum l E)
              (pbcUniformizer l E)).obj L)) ∧
      ((rationalT l E W).ge 0 X ↔
        ∃ L : PbcBoundedConstructibleComplete W.scheme (pbcIntegralDatum l E),
          (pbcIntegralTStructure W.scheme l E).ge 0 L ∧
            Nonempty (X ≅ (pbcRationalization W.scheme (pbcIntegralDatum l E)
              (pbcUniformizer l E)).obj L)) ∧
      ((rationalT l E W).heart X ↔
        ∃ L : PbcBoundedConstructibleComplete W.scheme (pbcIntegralDatum l E),
          (pbcIntegralTStructure W.scheme l E).heart L ∧
            Nonempty (X ≅ (pbcRationalization W.scheme (pbcIntegralDatum l E)
              (pbcUniformizer l E)).obj L))) ∧
    (∀ r : ℤ, Nonempty
      (pbcRationalization W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
          cohomology (rationalT l E W) r ≅
        cohomology (pbcIntegralTStructure W.scheme l E) r ⋙
          pbcRationalization W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E))) ∧
    (∀ (K : PbcBoundedConstructibleComplete W.scheme (pbcIntegralDatum l E)) (r : ℤ),
      Nonempty (((cohomology (pbcIntegralTStructure W.scheme l E) r).obj K).obj ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ r).obj K.obj))) ∧
    (∀ K : PbcBoundedConstructibleComplete W.scheme (pbcIntegralDatum l E),
      (∀ i : ℤ, i ≠ 0 → ∃ N : ℕ, (pbcUniformizer l E) ^ N •
        𝟙 ((DerivedCategory.homologyFunctor _ i).obj K.obj) = 0) →
      (rationalT l E W).heart
        ((pbcRationalization W.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K))

/-- Exact triangulated pullback and preservation of the two standard classes.
Source: BS Remark 6.8.15 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def RationalPullAssertions (V T : Base k) (h : V.scheme ⟶ T.scheme) : Prop :=
  (∃ s : (rationalPull l E h).CommShift ℤ,
    (fun [_shift : (rationalPull l E h).CommShift ℤ] ↦
      (rationalPull l E h).IsTriangulated) (_shift := s)) ∧
  (∀ n : ℤ, ∀ X : PbcRationalCategory T.scheme (pbcIntegralDatum l E) (pbcUniformizer l E),
    ((rationalT l E T).le n X → (rationalT l E V).le n ((rationalPull l E h).obj X)) ∧
    ((rationalT l E T).ge n X → (rationalT l E V).ge n ((rationalPull l E h).obj X))) 

/-- Exact geometric coefficient fibres and joint conservativity on the heart.
Source: BS 6.8.4--6.8.7 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def RationalFiberAssertions : Prop :=
  (∀ (W : Base k) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x : Spec (.of Ω) ⟶ W.scheme),
    PreservesFiniteLimits (heartFiber l E W x) ∧
      PreservesFiniteColimits (heartFiber l E W x)) ∧
  (∀ (W : Base k) (A B : Heart l E W) (f : A ⟶ B),
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ W.scheme),
      IsIso ((heartFiber l E W x).map f)) → IsIso f) 

/-- Natural pullback comparison and independence of geometric lifts of one point.
Source: BS 6.8.4 and Remark 6.8.15 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def RationalComparisonAssertions (V T : Base k) (h : V.scheme ⟶ T.scheme) : Prop :=
  (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V.scheme),
    Nonempty (rationalPull l E h ⋙ fiber l E V.scheme v ≅
      fiber l E T.scheme (v ≫ h))) ∧
  (∀ (W : Base k) (K : Heart l E W)
      (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
      (x : Spec (.of Ω) ⟶ W.scheme) (y : Spec (.of Ω') ⟶ W.scheme),
    (SpecToEquivOfField Ω W.scheme x).1 = (SpecToEquivOfField Ω' W.scheme y).1 →
      Nonempty ((heartFiber l E W x).obj K ≅ (heartFiber l E W y).obj K)) 

/-- Finite lisse stratifications, local constancy of ranks and constructible support.
Source: BS Definitions 6.8.3 and 6.8.6 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def RationalSupportAssertions : Prop :=
  (∀ (W : Base k) (K : Heart l E W),
    ∃ (S : FiniteLocallyClosedStratification W.scheme) (rank : W.scheme → ℕ),
      LisseStrata l E W.scheme K.obj S ∧
      (∀ i : Fin S.n, IsLocallyConstant (rank ∘ S.immersion i)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ W.scheme),
        FiniteDimensional E ((heartFiber l E W x).obj K) ∧
          Module.finrank E ((heartFiber l E W x).obj K) =
            rank (SpecToEquivOfField Ω W.scheme x).1) ∧
      Topology.IsConstructible {x : W.scheme | rank x ≠ 0})


/-- The completed point-section normalization is the adic inverse-limit normalization.
On a lisse integral stratum this is the limit of its finite-level etale fibres.
Source: BS Proposition 6.8.4 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def RationalLimitAssertions : Prop :=
  ∀ (W : Base k) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ W.scheme),
    Nonempty (integralFiber l E W.scheme x ≅ integralLimitFiber l E W.scheme x)

variable (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar]
  [IsAlgClosure (Padic l) Qbar]

/-- The recorded coherent scalar system at a separated finite-type base.
Source: BS 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
abbrev stages (W : Base k) :=
  pbcScalarSystem l Qbar W.scheme (baseDimension W).out (basePrimeUnit l W).out

/-- The existing inclusion of a finite coefficient field in the raw common-stage category.
Source: BS 6.8.14, common finite stages (blueprint: lem-per-adic-heart-pullback-fibres). -/
abbrev inclusion (W : Base k) (L : Padic.FiniteCoefficientFields l Qbar) :=
  (stages l Qbar W).ι L

/-- Common-stage classes are precisely the isomorphism closures of finite-stage classes.
Source: BS 6.8.14, common finite stages (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def commonClass (W : Base k) (nonpositive : Bool) (n : ℤ) :
    ObjectProperty (pbcQbarCategory l Qbar W.scheme) :=
  fun K ↦ ∃ (L : Padic.FiniteCoefficientFields l Qbar)
    (M : pbcStageCategory l Qbar W.scheme L),
    (if nonpositive then rationalLE l (pbcFiniteField.{u} l Qbar L) W n M
      else rationalGE l (pbcFiniteField.{u} l Qbar L) W n M) ∧
      Nonempty (K ≅ (inclusion l Qbar W L).obj M)

/-- The common-stage t-structure is fixed by its two finite-stage image classes.
Source: BS 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres).
Proof: finite scalar extension is t-exact by its finite free integral description.
Descend both truncations with their scalar comparisons. Orthogonality is checked
at a common field; all later Hom groups are zero, hence so is their colimit. The
finite-stage truncation triangle supplies the decomposition axiom. Finite-stage
bounds give boundedness. The prescribed indexed classes determine the t-structure. -/
theorem commonT_existsUnique (W : Base k) :
    ∃! t : Triangulated.TStructure (pbcQbarCategory l Qbar W.scheme),
      (∀ n : ℤ, t.le n = commonClass l Qbar W true n ∧
        t.ge n = commonClass l Qbar W false n) ∧ t.bounded = ⊤ := by
  sorry

/-- The bounded common-stage t-structure, determined by its specified classes.
Source: BS 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def commonT (W : Base k) :
    Triangulated.TStructure (pbcQbarCategory l Qbar W.scheme) :=
  (commonT_existsUnique l Qbar W).exists.choose

/-- The full constructible heart at algebraically closed coefficients.
Source: BS 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
abbrev CommonHeart (W : Base k) := (commonT l Qbar W).heart.FullSubcategory

/-- The scalar-compatible pullback family is normalized by the actual completed tensor maps.
Source: BS Remark 6.8.15 (blueprint: lem-per-adic-heart-pullback-fibres).
Proof: the rational pullbacks retain actual integral pullbacks and tensor Hom maps.
The scalar comparison is the localized completed scalar comparison, with orientation
reversed for the beta map. Its unit and associator equations are the completed tensor
unit and tower equations. These give a morphism of the recorded scalar systems.
The finite-stage functors and PbcPullbackBetaSpec determine its data uniquely. -/
theorem pullFamily_existsUnique {V T : Base k} (h : V.scheme ⟶ T.scheme) :
    ∃! F : StageSystem.Morphism (stages l Qbar T) (stages l Qbar V),
      (∀ L : Padic.FiniteCoefficientFields l Qbar,
        F.Φ L = rationalPull l (pbcFiniteField.{u} l Qbar L) h) ∧
      PbcPullbackBetaSpec l Qbar h
        (fun L ↦ integralPull_mem l (pbcFiniteField.{u} l Qbar L) h) F := by
  sorry

/-- The unique scalar-compatible completed pullback family.
Source: BS Remark 6.8.15 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def pullFamily {V T : Base k} (h : V.scheme ⟶ T.scheme) :
    StageSystem.Morphism (stages l Qbar T) (stages l Qbar V) :=
  (pullFamily_existsUnique l Qbar h).exists.choose

/-- Common-stage pullback uses the actual representative formula beta, pullback, beta inverse.
Source: BS Remark 6.8.15 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def commonPull {V T : Base k} (h : V.scheme ⟶ T.scheme) :
    pbcQbarCategory l Qbar T.scheme ⥤ pbcQbarCategory l Qbar V.scheme :=
  (pullFamily l Qbar h).functor

/-- The actual embedding of the canonical small coefficient model in Qbar.
Source: BS 6.8.14, finite-stage scalar extension
(blueprint: lem-per-adic-heart-pullback-fibres). -/
def stageEmbedding (L : Padic.FiniteCoefficientFields l Qbar) :
    pbcFiniteField.{u} l Qbar L →+* Qbar :=
  L.val.subtype.comp (Shrink.algEquiv (Padic l) L.val).toRingHom

/-- Finite scalar extension commutes with both truncations and with cohomology.
Source: BS 6.8.11 and 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def ScalarAssertions : Prop :=
  ∀ (W : Base k) (L M : Padic.FiniteCoefficientFields l Qbar) (a : L ≤ M) (n : ℤ),
    Nonempty (rationalTruncLE l (pbcFiniteField.{u} l Qbar L) W n ⋙
        (stages l Qbar W).T a ≅ (stages l Qbar W).T a ⋙
          rationalTruncLE l (pbcFiniteField.{u} l Qbar M) W n) ∧
    Nonempty (rationalTruncGE l (pbcFiniteField.{u} l Qbar L) W n ⋙
        (stages l Qbar W).T a ≅ (stages l Qbar W).T a ⋙
          rationalTruncGE l (pbcFiniteField.{u} l Qbar M) W n) ∧
    Nonempty (rationalCohomology l (pbcFiniteField.{u} l Qbar L) W n ⋙
        (stages l Qbar W).T a ≅ (stages l Qbar W).T a ⋙
          rationalCohomology l (pbcFiniteField.{u} l Qbar M) W n)

/-- Finite-stage geometric fibres commute naturally with finite coefficient extension.
Source: BS 6.8.4 and 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def ScalarFiberAssertions : Prop :=
  ∀ (W : Base k) (L M : Padic.FiniteCoefficientFields l Qbar) (a : L ≤ M)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ W.scheme),
    Nonempty ((stages l Qbar W).T a ⋙
        fiber l (pbcFiniteField.{u} l Qbar M) W.scheme x ≅
      fiber l (pbcFiniteField.{u} l Qbar L) W.scheme x ⋙
        ModuleCat.extendScalars (pbcFiniteFieldInclusion l Qbar a).toRingHom)

/-- Pullback-fibre comparisons commute with finite coefficient extension, including
identity extensions. The square uses the actual normalized completed scalar comparison.
Source: BS 6.8.4 and Remark 6.8.15 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def ScalarPullbackFiberAssertions (V T : Base k) (h : V.scheme ⟶ T.scheme) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V.scheme),
    ∃ c : ∀ L : Padic.FiniteCoefficientFields l Qbar,
        (pullFamily l Qbar h).Φ L ⋙
            fiber l (pbcFiniteField.{u} l Qbar L) V.scheme v ≅
          fiber l (pbcFiniteField.{u} l Qbar L) T.scheme (v ≫ h),
      ∀ (L M : Padic.FiniteCoefficientFields l Qbar) (a : L ≤ M),
        ∃ (eV : (stages l Qbar V).T a ⋙
                fiber l (pbcFiniteField.{u} l Qbar M) V.scheme v ≅
              fiber l (pbcFiniteField.{u} l Qbar L) V.scheme v ⋙
                ModuleCat.extendScalars (pbcFiniteFieldInclusion l Qbar a).toRingHom)
          (eT : (stages l Qbar T).T a ⋙
                fiber l (pbcFiniteField.{u} l Qbar M) T.scheme (v ≫ h) ≅
              fiber l (pbcFiniteField.{u} l Qbar L) T.scheme (v ≫ h) ⋙
                ModuleCat.extendScalars (pbcFiniteFieldInclusion l Qbar a).toRingHom),
          ∀ K : pbcStageCategory l Qbar T.scheme L,
            (fiber l (pbcFiniteField.{u} l Qbar M) V.scheme v).map
                  (((pullFamily l Qbar h).β a).hom.app K) ≫
                (c M).hom.app (((stages l Qbar T).T a).obj K) ≫ eT.hom.app K =
              eV.hom.app (((pullFamily l Qbar h).Φ L).obj K) ≫
                (ModuleCat.extendScalars (pbcFiniteFieldInclusion l Qbar a).toRingHom).map
                  ((c L).hom.app K)

/-- The common-stage heart and its truncations are computed at one finite coefficient field.
Source: BS 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def CommonStandardAssertions : Prop :=
  ∀ W : Base k,
    (∀ K : pbcQbarCategory l Qbar W.scheme,
      (commonT l Qbar W).heart K ↔
        ∃ (L : Padic.FiniteCoefficientFields l Qbar) (M : Heart l
            (pbcFiniteField.{u} l Qbar L) W),
          Nonempty (K ≅ (inclusion l Qbar W L).obj M.obj)) ∧
    (∀ (L : Padic.FiniteCoefficientFields l Qbar) (n : ℤ),
      Nonempty (inclusion l Qbar W L ⋙ (commonT l Qbar W).truncLE n ≅
        rationalTruncLE l (pbcFiniteField.{u} l Qbar L) W n ⋙ inclusion l Qbar W L) ∧
      Nonempty (inclusion l Qbar W L ⋙ (commonT l Qbar W).truncGE n ≅
        rationalTruncGE l (pbcFiniteField.{u} l Qbar L) W n ⋙ inclusion l Qbar W L) ∧
      Nonempty (inclusion l Qbar W L ⋙ cohomology (commonT l Qbar W) n ≅
        rationalCohomology l (pbcFiniteField.{u} l Qbar L) W n ⋙ inclusion l Qbar W L))

/-- Triangulated common-stage pullback preserves both standard classes.
Source: BS Remark 6.8.15 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def CommonPullAssertions (V T : Base k) (h : V.scheme ⟶ T.scheme) : Prop :=
  (∃ s : (commonPull l Qbar h).CommShift ℤ,
    (fun [_shift : (commonPull l Qbar h).CommShift ℤ] ↦
      (commonPull l Qbar h).IsTriangulated) (_shift := s)) ∧
  (∀ (n : ℤ) (K : pbcQbarCategory l Qbar T.scheme),
    ((commonT l Qbar T).le n K → (commonT l Qbar V).le n ((commonPull l Qbar h).obj K)) ∧
    ((commonT l Qbar T).ge n K → (commonT l Qbar V).ge n ((commonPull l Qbar h).obj K)))

/-- A common-stage fibre is normalized by extension of the actual finite-stage fibres.
The comparison is a natural isomorphism, so every finite-stage arrow is retained.
Source: BS 6.8.4 and 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def CommonFiberNormalization (W : Base k) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ W.scheme)
    (F : pbcQbarCategory l Qbar W.scheme ⥤ ModuleCat.{max (u + 1) v} Qbar) : Prop :=
  F.Linear Qbar ∧ ∀ L : Padic.FiniteCoefficientFields l Qbar,
    Nonempty (inclusion l Qbar W L ⋙ F ≅
      fiber l (pbcFiniteField.{u} l Qbar L) W.scheme x ⋙
        ModuleCat.extendScalars (stageEmbedding l Qbar L))


/-- The canonical finite-stage inclusion comparison for the descended completed pullback.
Source: BS Remark 6.8.15 (blueprint: lem-per-adic-heart-pullback-fibres). -/
def pullInclusionIso {V T : Base k} (h : V.scheme ⟶ T.scheme)
    (L : Padic.FiniteCoefficientFields l Qbar) :
    inclusion l Qbar T L ⋙ commonPull l Qbar h ≅
      rationalPull l (pbcFiniteField.{u} l Qbar L) h ⋙ inclusion l Qbar V L :=
  (by unfold commonPull; exact (pullFamily l Qbar h).ιCompFunctorIso L) ≪≫
    Functor.isoWhiskerRight
      (eqToIso (show (pullFamily l Qbar h).Φ L =
          rationalPull l (pbcFiniteField.{u} l Qbar L) h from by
        unfold pullFamily
        exact (pullFamily_existsUnique l Qbar h).exists.choose_spec.1 L))
      (inclusion l Qbar V L)

/-- Restriction of a point-normalized common-stage fibre to the actual common-stage heart.
Source: BS 6.8.4 and 6.8.14 (blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def commonHeartFiber (W : Base k)
    (F : pbcQbarCategory l Qbar W.scheme ⥤ ModuleCat.{max (u + 1) v} Qbar) :=
  ObjectProperty.ι (commonT l Qbar W).heart ⋙ F

/-- Common-stage fibres, their finite-stage normalizations, and the pullback comparisons.
All these data are conclusions; no comparison or fibre functor is assumed.
Source: BS 6.8.4, 6.8.14 and Remark 6.8.15
(blueprint: lem-per-adic-heart-pullback-fibres). -/
@[irreducible]
def CommonFiberAssertions (V T : Base k) (h : V.scheme ⟶ T.scheme) : Prop :=
  ∃ F : ∀ (W : Base k) (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
      (Spec (.of Ω) ⟶ W.scheme) →
        (pbcQbarCategory l Qbar W.scheme ⥤ ModuleCat.{max (u + 1) v} Qbar),
    (∀ (W : Base k) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ W.scheme), CommonFiberNormalization l Qbar W x (F W Ω x)) ∧
    (∀ (W : Base k) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ W.scheme),
      PreservesFiniteLimits (commonHeartFiber l Qbar W (F W Ω x)) ∧
        PreservesFiniteColimits (commonHeartFiber l Qbar W (F W Ω x))) ∧
    (∀ (W : Base k) (A B : CommonHeart l Qbar W) (f : A ⟶ B),
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ W.scheme),
        IsIso ((commonHeartFiber l Qbar W (F W Ω x)).map f)) → IsIso f) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V.scheme),
      ∃ c : commonPull l Qbar h ⋙ F V Ω v ≅ F T Ω (v ≫ h),
        ∀ L : Padic.FiniteCoefficientFields l Qbar,
          ∃ (cL : rationalPull l (pbcFiniteField.{u} l Qbar L) h ⋙
                fiber l (pbcFiniteField.{u} l Qbar L) V.scheme v ≅
              fiber l (pbcFiniteField.{u} l Qbar L) T.scheme (v ≫ h))
            (eV : inclusion l Qbar V L ⋙ F V Ω v ≅
              fiber l (pbcFiniteField.{u} l Qbar L) V.scheme v ⋙
                ModuleCat.extendScalars (stageEmbedding l Qbar L))
            (eT : inclusion l Qbar T L ⋙ F T Ω (v ≫ h) ≅
              fiber l (pbcFiniteField.{u} l Qbar L) T.scheme (v ≫ h) ⋙
                ModuleCat.extendScalars (stageEmbedding l Qbar L)),
            ∀ K : pbcStageCategory l Qbar T.scheme L,
              (F V Ω v).map ((pullInclusionIso l Qbar h L).hom.app K) ≫
                  eV.hom.app ((rationalPull l (pbcFiniteField.{u} l Qbar L) h).obj K) ≫
                  (ModuleCat.extendScalars (stageEmbedding l Qbar L)).map (cL.hom.app K) =
                c.hom.app ((inclusion l Qbar T L).obj K) ≫ eT.hom.app K) ∧
    (∀ (W : Base k) (K : CommonHeart l Qbar W)
        (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω']
        (x : Spec (.of Ω) ⟶ W.scheme) (y : Spec (.of Ω') ⟶ W.scheme),
      (SpecToEquivOfField Ω W.scheme x).1 = (SpecToEquivOfField Ω' W.scheme y).1 →
        Nonempty ((F W Ω x).obj K.obj ≅ (F W Ω' y).obj K.obj)) ∧
    (∀ (W : Base k) (K : CommonHeart l Qbar W),
      ∃ (L : Padic.FiniteCoefficientFields l Qbar)
        (M : Heart l (pbcFiniteField.{u} l Qbar L) W)
        (S : FiniteLocallyClosedStratification W.scheme) (rank : W.scheme → ℕ),
        Nonempty (K.obj ≅ (inclusion l Qbar W L).obj M.obj) ∧
        LisseStrata l (pbcFiniteField.{u} l Qbar L) W.scheme M.obj S ∧
        (∀ i : Fin S.n, IsLocallyConstant (rank ∘ S.immersion i)) ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ W.scheme),
          FiniteDimensional Qbar ((F W Ω x).obj K.obj) ∧
            Module.finrank Qbar ((F W Ω x).obj K.obj) =
              rank (SpecToEquivOfField Ω W.scheme x).1) ∧
        Topology.IsConstructible {x : W.scheme | rank x ≠ 0})

/-- Geometric fibres and degree-zero pullback for constructible adic coefficients.
Source: BS Section 6.8, especially Propositions 6.8.4, 6.8.11 and 6.8.14 and
Remark 6.8.15 (blueprint: lem-per-adic-heart-pullback-fibres).

Proof:
1. Finite-type schemes over k are noetherian and finite-dimensional and inherit the
   unit l. Use prop-weil-pbc-integral-tstructure and prop-weil-localized-tstructure.
   Their truncation comparisons give the cohomology formula. Off-zero integral
   cohomology killed by a uniformizer power becomes zero after rationalization.
2. lem-per-continuous-rational-derived-realization identifies the rational heart
   with constructible modules over the continuous coefficient field sheaf.
   det-lem-coefficient-heart-closure identifies its exact sequences with sheaf sequences.
3. Finite coefficient extension is finite free on completed integral coefficients by
   lem-weil-finite-free-completed-scalar-comparison. Hence it is t-exact and commutes
   naturally with truncations and cohomology by lem-pod-texact-truncation-comparison.
   The unit and tower equations are those of prop-weil-pbc-scalar-extension.
4. Descend truncations through lem-sbc-coherent-pair-functor-descent. At a common
   stage opposite bounds have zero Hom, and their filtered Hom colimit is zero.
   Finite-stage truncation triangles and bounds give the bounded common t-structure.
5. lem-cbc-completed-pullback-triangles gives triangulated completed pullback.
   lem-a1-integral-pullback-completed-comparison and
   lem-pur-integral-operations-preserve-constructible give its integral restriction.
   Rationalize via lem-pur-semilinear-scalar-localization and descend using
   prop-weil-pbc-descent-functors and the normalized scalar comparisons.
6. Pull back the lisse strata and their pro-etale trivializing covers. A finite free
   module in degree zero is K-flat. The completed continuous realization identifies
   its actual pullback with the same free module on the pulled-back cover.
   lem-weil-pbc-noetherian-stratum-detection kills every other cohomology sheaf.
   Bounded truncation devissage then gives t-exactness at finite and common stages.
7. On an etale integral-model chart, lem-per-lisse-completed-system-comparison
   identifies point sections with the inverse limit of finite-level geometric fibres,
   as in def-pod-lisse-l-adic-sheaves. lem-pod-adic-limit-finite-modules makes this
   finite free on a lisse stratum. Invert the uniformizer; clear denominators to
   identify all fibre maps independently of the lattice or chart.
8. Use det-lem-coefficient-heart-common-stratification and affine etale lattice charts
   for a short exact sequence. cor-galois-lisse-representations computes each fibre
   as evaluation of an exact representation sequence. Kernels and cokernels remain
   constructible, so vanishing of all fibres detects zero and hence isomorphisms.
9. At each finite etale level lemma-openclosed-stalk-upperstar identifies pullback
   fibres with the fibres at the image point, compatibly with transitions. Inverse
   limit and rationalization give the natural adic comparison. Finite scalar tensor
   commutes with these limits by lem-pod-adic-limit-finite-modules and
   lem-pod-lisse-tensor-and-scalar-extension. Descend the comparisons and equations.
10. On a connected lisse chart the representation dimension is constant. Etale
    charts are open, so the ranks descend to locally constant functions on strata.
    Geometric points over the same point have equal dimensions and thus isomorphic
    vector spaces. Refine the finite stratification by its finitely many rank loci.
    The positive-rank strata give the constructible nonzero-fibre locus, including
    the empty locus. Common-stage scalar extension preserves all ranks. -/
theorem adicHeartPullbackFibres (L : Padic.FiniteCoefficientFields l Qbar)
    (V T : Base k) (h : V.scheme ⟶ T.scheme) :
    (∀ W : Base k, RationalStandardAssertions l (pbcFiniteField.{u} l Qbar L) W) ∧
    RationalPullAssertions l (pbcFiniteField.{u} l Qbar L) V T h ∧
    RationalFiberAssertions (k := k) l (pbcFiniteField.{u} l Qbar L) ∧
    RationalComparisonAssertions l (pbcFiniteField.{u} l Qbar L) V T h ∧
    RationalSupportAssertions (k := k) l (pbcFiniteField.{u} l Qbar L) ∧
    RationalLimitAssertions (k := k) l (pbcFiniteField.{u} l Qbar L) ∧
    ScalarAssertions (k := k) l Qbar ∧
    ScalarFiberAssertions (k := k) l Qbar ∧
    ScalarPullbackFiberAssertions l Qbar V T h ∧
    CommonStandardAssertions (k := k) l Qbar ∧
    CommonPullAssertions l Qbar V T h ∧
    CommonFiberAssertions l Qbar V T h := by
  sorry

end AlgebraicGeometry.Scheme.PerAdic
