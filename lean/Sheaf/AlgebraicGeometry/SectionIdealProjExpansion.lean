/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra
public import Sheaf.AlgebraicGeometry.StablePointedCurve
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocusDual
public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic

import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero
import Sheaf.Paper.EtaleStandardCoverCech
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Sheaf.AlgebraicGeometry.SmoothSectionAffineCoordinates
import WeilConjectures.Mathlib.RingTheory.Finiteness.Descent
import Sheaf.AlgebraicGeometry.NodalCurveNormalizationEuler
import Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel
import Sheaf.TraceFormula.ProjectiveBundleProper
import Sheaf.TraceFormula.ReducedCurveNormalizationGenus
import Sheaf.AlgebraicGeometry.SmoothAtPointFibreCriterion
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.FiniteStability
import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.SymmetricAlgebraBaseChange
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
import WeilConjectures.AlgebraicGeometry.EtaleFiniteAffineCechBasis

/-!
# Expansion from the dual ideal of a section

Source: Knudsen, The projectivity of the moduli space of stable curves II, Section 2,
Lemma 2.2, Definition 2.3 and Theorem 2.4; A closer look at the stacks of stable pointed
curves, arXiv:1106.1588, Main Lemma and Sections 3--5
(blueprint: lem-sfb-section-ideal-proj-expansion).

All modules, inclusions and quotient maps below are actual constructions. The conclusion
records the geometry and naturality of their relative Proj, rather than an unspecified
replacement family.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.SectionIdealExpansion

/-- The old divisor ideal is the product of the section ideals, including the empty product.
Source: Knudsen II, Definition 2.3 (blueprint: lem-sfb-section-ideal-proj-expansion). -/
def oldIdeal {T X : Scheme.{u}} {r : ℕ} (s : Fin r → (T ⟶ X)) : X.IdealSheafData :=
  ∏ i : Fin r, (s i).ker

/-- Multiplication on an ideal, obtained by transposing its actual inclusion into O.
Source: Knudsen II, Lemma 2.2 (blueprint: lem-sfb-section-ideal-proj-expansion). -/
def inclusion {X : Scheme.{u}} (J : X.IdealSheafData) :
    𝟙_ X.Modules ⟶ J.toModulesᵛ :=
  Scheme.Modules.dualUnitIso.inv ≫ Scheme.Modules.dualMap J.toModulesι

/-- The diagonal map u ↦ (u,u), using multiplication on the two ideal sheaves.
Source: Knudsen II, Definition 2.3 (blueprint: lem-sfb-section-ideal-proj-expansion). -/
def diagonal {T X : Scheme.{u}} {r : ℕ} (s : Fin r → (T ⟶ X)) (d : T ⟶ X) :
    𝟙_ X.Modules ⟶ d.ker.toModulesᵛ ⊞ (oldIdeal s).toModulesᵛ :=
  biprod.lift (inclusion d.ker) (inclusion (oldIdeal s))

/-- The specified cokernel K, with no choice of a module satisfying an existence assertion.
Source: Knudsen II, Definition 2.3 (blueprint: lem-sfb-section-ideal-proj-expansion). -/
def moduleK {T X : Scheme.{u}} {r : ℕ} (s : Fin r → (T ⟶ X)) (d : T ⟶ X) :
    X.Modules :=
  cokernel (diagonal s d)

/-- The image map from the first summand into K.
Source: Knudsen II, Definition 2.3 (blueprint: lem-sfb-section-ideal-proj-expansion). -/
def firstToK {T X : Scheme.{u}} {r : ℕ} (s : Fin r → (T ⟶ X)) (d : T ⟶ X) :
    d.ker.toModulesᵛ ⟶ moduleK s d :=
  biprod.inl ≫ cokernel.π (diagonal s d)

/-- The image map from the old-divisor summand into K.
Source: Knudsen II, Definition 2.3 (blueprint: lem-sfb-section-ideal-proj-expansion). -/
def secondToK {T X : Scheme.{u}} {r : ℕ} (s : Fin r → (T ⟶ X)) (d : T ⟶ X) :
    (oldIdeal s).toModulesᵛ ⟶ moduleK s d :=
  biprod.inr ≫ cokernel.π (diagonal s d)

/-- The quotient supported on the old markings.
Source: Knudsen II, Definition 2.3 (blueprint: lem-sfb-section-ideal-proj-expansion). -/
def oldQuotient {T X : Scheme.{u}} {r : ℕ} (s : Fin r → (T ⟶ X)) (d : T ⟶ X) :
    X.Modules :=
  cokernel (firstToK s d)

/-- The quotient supported on the arbitrary extra section.
Source: Knudsen II, Definition 2.3 (blueprint: lem-sfb-section-ideal-proj-expansion). -/
def newQuotient {T X : Scheme.{u}} {r : ℕ} (s : Fin r → (T ⟶ X)) (d : T ⟶ X) :
    X.Modules :=
  cokernel (secondToK s d)

/-- The geometric-fibre condition, with genus computed using the structural map.
Source: Knudsen II, Section 2 (blueprint: lem-sfb-section-ideal-proj-expansion). -/
def FibreConditions {T X : Scheme.{u}} (f : X ⟶ T) (g : ℕ)
    [LocallyOfFinitePresentation f] : Prop :=
  HasNodalGeometricFibres f ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ T),
      IsReduced (pullback f a) ∧ (pullback f a).IsPureDimension 1 ∧
      @Scheme.arithmeticGenus Ω _ (pullback f a) ⟨pullback.snd f a⟩ = g

/-- The actual relative Proj of the canonical symmetric algebra of K.
Source: Knudsen II, Definition 2.3 (blueprint: lem-sfb-section-ideal-proj-expansion). -/
def schemeZ {T X : Scheme.{u}} {r : ℕ} (s : Fin r → (T ⟶ X)) (d : T ⟶ X)
    [(moduleK s d).IsQuasicoherent] : Scheme.{u} :=
  (SymmetricAlgebraSheaf.gradedAlgebraData (moduleK s d)).relProj

/-- The specified relative-Proj structural morphism.
Source: Knudsen II, Definition 2.3 (blueprint: lem-sfb-section-ideal-proj-expansion). -/
def projection {T X : Scheme.{u}} {r : ℕ} (s : Fin r → (T ⟶ X)) (d : T ⟶ X)
    [(moduleK s d).IsQuasicoherent] : schemeZ s d ⟶ X :=
  (SymmetricAlgebraSheaf.gradedAlgebraData (moduleK s d)).relProjHom

/-- The canonical invertible quotients, and their unique classifying lifts. Uniqueness is
relative to the specified quotients, not uniqueness among all lifts of a section.
Source: Knudsen II, Definition 2.3; arXiv:1106.1588, Introduction, equation (1)
(blueprint: lem-sfb-section-ideal-proj-expansion). -/
structure Lifts {T X : Scheme.{u}} {r : ℕ} (f : X ⟶ T)
    (s : Fin r → (T ⟶ X)) (d : T ⟶ X) [(moduleK s d).IsQuasicoherent] where
  tautological : ProjectiveBundleQuotientGeometry.TautologicalQuotient (moduleK s d)
  old : Fin r → (T ⟶ schemeZ s d)
  extra : T ⟶ schemeZ s d
  old_over (i : Fin r) : old i ≫ projection s d = s i
  extra_over : extra ≫ projection s d = d
  old_section (i : Fin r) : old i ≫ (projection s d ≫ f) = 𝟙 T
  extra_section : extra ≫ (projection s d ≫ f) = 𝟙 T
  old_invertible (i : Fin r) :
    ((Scheme.Modules.tensorPullback (s i)).obj (oldQuotient s d)).IsInvertible
  extra_invertible :
    ((Scheme.Modules.tensorPullback d).obj (newQuotient s d)).IsInvertible
  old_surjective (i : Fin r) :
    Epi ((Scheme.Modules.tensorPullback (s i)).map (cokernel.π (firstToK s d)))
  extra_surjective :
    Epi ((Scheme.Modules.tensorPullback d).map (cokernel.π (secondToK s d)))
  old_classifies (i : Fin r) :
    ProjectiveBundleQuotientGeometry.Classifies tautological (s i)
      ((Scheme.Modules.tensorPullback (s i)).obj (oldQuotient s d))
      ((Scheme.Modules.tensorPullback (s i)).map (cokernel.π (firstToK s d))) (old i)
  extra_classifies :
    ProjectiveBundleQuotientGeometry.Classifies tautological d
      ((Scheme.Modules.tensorPullback d).obj (newQuotient s d))
      ((Scheme.Modules.tensorPullback d).map (cokernel.π (secondToK s d))) extra
  old_unique (i : Fin r) (v : T ⟶ schemeZ s d) :
    ProjectiveBundleQuotientGeometry.Classifies tautological (s i)
      ((Scheme.Modules.tensorPullback (s i)).obj (oldQuotient s d))
      ((Scheme.Modules.tensorPullback (s i)).map (cokernel.π (firstToK s d))) v → v = old i
  extra_unique (v : T ⟶ schemeZ s d) :
    ProjectiveBundleQuotientGeometry.Classifies tautological d
      ((Scheme.Modules.tensorPullback d).obj (newQuotient s d))
      ((Scheme.Modules.tensorPullback d).map (cokernel.π (secondToK s d))) v → v = extra
  disjoint_old : Pairwise (fun i j : Fin r ↦ Disjoint (Set.range (old i)) (Set.range (old j)))
  disjoint_extra (i : Fin r) : Disjoint (Set.range (old i)) (Set.range extra)

/-- The induced map on the geometric fibres of a morphism over T.
Source: Knudsen II, Theorem 2.4 (blueprint: lem-sfb-section-ideal-proj-expansion). -/
def fibreMap {T X Z : Scheme.{u}} (f : X ⟶ T) (p : Z ⟶ X)
    {Ω : Type u} [Field Ω] (a : Spec (.of Ω) ⟶ T) :
    pullback (p ≫ f) a ⟶ pullback f a :=
  pullback.lift (pullback.fst (p ≫ f) a ≫ p) (pullback.snd (p ≫ f) a)
    (by simpa only [Category.assoc] using (pullback.condition (f := p ≫ f) (g := a)))

/-- The nodal and marked special points of a geometric fibre.
Source: Knudsen II, Theorem 2.4 (blueprint: lem-sfb-section-ideal-proj-expansion). -/
def specialPoints {Ω : Type u} [Field Ω] {C : Scheme.{u}}
    (q : C ⟶ Spec (.of Ω)) [LocallyOfFinitePresentation q] {r : ℕ}
    (m : Fin r → (Spec (.of Ω) ⟶ C)) : Set C :=
  {x | x ∉ q.smoothLocus} ∪ ⋃ i : Fin r, Set.range (m i)

/-- Unchanged old components are identified on their canonical normalizations over the
original curve. Equality of special-point preimages retains self-node branches separately
and replaces a colliding marking or a branch by the new attachment at the same preimage.
Source: Knudsen II, Theorem 2.4; arXiv:1106.1588, Section 5
(blueprint: lem-sfb-section-ideal-proj-expansion). -/
def UnchangedComponents {Ω : Type u} [Field Ω] {C B : Scheme.{u}}
    (p : B ⟶ C) (q : C ⟶ Spec (.of Ω)) (qB : B ⟶ Spec (.of Ω))
    [LocallyOfFinitePresentation q] [LocallyOfFinitePresentation qB] {r : ℕ}
    (m : Fin r → (Spec (.of Ω) ⟶ C)) (n : Fin (r + 1) → (Spec (.of Ω) ⟶ B))
    (exceptional : Set B) : Prop :=
  ∃ b : irreducibleComponents C ≃
      {W : irreducibleComponents B // W.1 ≠ exceptional},
    ∀ V : irreducibleComponents C,
      ∃ e : (B.reducedNormalizationComponent (b V).1).normalization ≅
          (C.reducedNormalizationComponent V).normalization,
        B.normalizedComponentMap (b V).1 ≫ p = e.hom ≫ C.normalizedComponentMap V ∧
        B.normalizedComponentMap (b V).1 ⁻¹' specialPoints qB n =
          e.hom ⁻¹' (C.normalizedComponentMap V ⁻¹' specialPoints q m)

/-- The exceptional fibre is a projective line component, its only singular points are
its attachments, the new point is on it, and the map is an isomorphism everywhere else.
Source: Knudsen II, Theorem 2.4; arXiv:1106.1588, Theorem 5.1
(blueprint: lem-sfb-section-ideal-proj-expansion). -/
def ExceptionalFibre {Ω : Type u} [Field Ω] {C B : Scheme.{u}}
    (p : B ⟶ C) (qB : B ⟶ Spec (.of Ω)) [LocallyOfFinitePresentation qB]
    (d : Spec (.of Ω) ⟶ C) (w : Spec (.of Ω) ⟶ B) (attachments : ℕ) : Prop :=
  IsClosedImmersion (pullback.fst p d) ∧
    Set.range (pullback.fst p d) ∈ irreducibleComponents B ∧
    (∃ e : pullback p d ≅ ℙ(ULift.{u} (Fin 2); Spec (.of Ω)),
      e.hom ≫ (ℙ(ULift.{u} (Fin 2); Spec (.of Ω)) ↘ Spec (.of Ω)) = pullback.snd p d) ∧
    Set.range w ⊆ Set.range (pullback.fst p d) ∧
    ({z : (pullback (C := Scheme.{u}) p d) | pullback.fst p d z ∉ qB.smoothLocus}).encard =
      (attachments : ℕ∞) ∧
    ∀ U : C.Opens, Disjoint (U : Set C) (Set.range d) →
      IsIso (pullback.snd p U.ι)

/-- The three fibrewise cases: no change, a single attached tail carrying both colliding
markings, or a bridge carrying the new marking and attached at the two nodal branches.
Source: Knudsen II, Theorem 2.4; arXiv:1106.1588, Section 5
(blueprint: lem-sfb-section-ideal-proj-expansion). -/
def FibreGeometry {T X : Scheme.{u}} {r : ℕ} (f : X ⟶ T)
    (s : Fin r → (T ⟶ X)) (hs : ∀ i : Fin r, s i ≫ f = 𝟙 T)
    (d : T ⟶ X) (hd : d ≫ f = 𝟙 T) [(moduleK s d).IsQuasicoherent]
    (L : Lifts f s d) [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation (projection s d ≫ f)] : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ T),
    (Set.range (f.baseChangeSection d hd a) ⊆
        ((pullback.snd f a).smoothLocus : Set _) →
      (∀ i : Fin r, f.baseChangeSection d hd a ≠ f.baseChangeSection (s i) (hs i) a) →
      IsIso (fibreMap f (projection s d) a)) ∧
    (∀ i : Fin r, f.baseChangeSection d hd a = f.baseChangeSection (s i) (hs i) a →
      ExceptionalFibre (fibreMap f (projection s d) a)
        (pullback.snd (projection s d ≫ f) a)
        (f.baseChangeSection d hd a)
        ((projection s d ≫ f).baseChangeSection L.extra L.extra_section a) 1 ∧
      Set.range ((projection s d ≫ f).baseChangeSection (L.old i) (L.old_section i) a) ⊆
        Set.range (pullback.fst (fibreMap f (projection s d) a)
          (f.baseChangeSection d hd a))) ∧
    (¬ Set.range (f.baseChangeSection d hd a) ⊆
        ((pullback.snd f a).smoothLocus : Set _) →
      ExceptionalFibre (fibreMap f (projection s d) a)
        (pullback.snd (projection s d ≫ f) a)
        (f.baseChangeSection d hd a)
        ((projection s d ≫ f).baseChangeSection L.extra L.extra_section a) 2) ∧
    ((∃ i : Fin r, f.baseChangeSection d hd a = f.baseChangeSection (s i) (hs i) a) ∨
      ¬ Set.range (f.baseChangeSection d hd a) ⊆
        ((pullback.snd f a).smoothLocus : Set _) →
      UnchangedComponents (fibreMap f (projection s d) a) (pullback.snd f a)
        (pullback.snd (projection s d ≫ f) a)
        (fun i ↦ f.baseChangeSection (s i) (hs i) a)
        (Fin.snoc (fun i ↦ (projection s d ≫ f).baseChangeSection (L.old i)
          (L.old_section i) a)
          ((projection s d ≫ f).baseChangeSection L.extra L.extra_section a))
        (Set.range (pullback.fst (fibreMap f (projection s d) a)
          (f.baseChangeSection d hd a))))

/-- The canonical tensor-pullback identification of structure sheaves.
Source: Knudsen II, base-change assertion in Lemma 2.2
(blueprint: lem-sfb-section-ideal-proj-expansion). -/
def unitComparison {X X' : Scheme.{u}} (h : X' ⟶ X) :
    (Scheme.Modules.tensorPullback h).obj (𝟙_ X.Modules) ≅ 𝟙_ X'.Modules :=
  (Scheme.Modules.boundaryPullbackComparison h).app (𝟙_ X.Modules) ≪≫
    Scheme.Modules.pullbackObjUnitIso h

/-- The canonical comparison of the full sequence, including the actual ideals and their
duals. The evaluation equations fix the dual maps, not merely their isomorphism classes.
The two summand equations fix the cokernel map. Thus this record has at most one element.
Source: Knudsen II, Lemma 2.2 and Definition 2.3; arXiv:1106.1588, Main Lemma
(blueprint: lem-sfb-section-ideal-proj-expansion). -/
structure SequenceComparison {T X T' X' : Scheme.{u}} {r : ℕ}
    (s : Fin r → (T ⟶ X)) (d : T ⟶ X)
    (s' : Fin r → (T' ⟶ X')) (d' : T' ⟶ X') (h : X' ⟶ X) where
  ideal : (Scheme.Modules.tensorPullback h).obj d.ker.toModules ≅ d'.ker.toModules
  divisor : (Scheme.Modules.tensorPullback h).obj (oldIdeal s).toModules ≅
    (oldIdeal s').toModules
  dual : (Scheme.Modules.tensorPullback h).obj d.ker.toModulesᵛ ≅ d'.ker.toModulesᵛ
  divisorDual : (Scheme.Modules.tensorPullback h).obj (oldIdeal s).toModulesᵛ ≅
    (oldIdeal s').toModulesᵛ
  quotient : (Scheme.Modules.tensorPullback h).obj (moduleK s d) ≅ moduleK s' d'
  ideal_inclusion : ideal.hom ≫ d'.ker.toModulesι =
    (Scheme.Modules.tensorPullback h).map d.ker.toModulesι ≫ (unitComparison h).hom
  divisor_inclusion : divisor.hom ≫ (oldIdeal s').toModulesι =
    (Scheme.Modules.tensorPullback h).map (oldIdeal s).toModulesι ≫ (unitComparison h).hom
  evaluation : (ideal.hom ⊗ₘ dual.hom) ≫ Scheme.Modules.dualEvaluation d'.ker.toModules =
    (Scheme.Modules.boundaryPullbackTensorIso h d.ker.toModules d.ker.toModulesᵛ).inv ≫
      (Scheme.Modules.tensorPullback h).map (Scheme.Modules.dualEvaluation d.ker.toModules) ≫
      (unitComparison h).hom
  divisor_evaluation : (divisor.hom ⊗ₘ divisorDual.hom) ≫
      Scheme.Modules.dualEvaluation (oldIdeal s').toModules =
    (Scheme.Modules.boundaryPullbackTensorIso h
      (oldIdeal s).toModules (oldIdeal s).toModulesᵛ).inv ≫
      (Scheme.Modules.tensorPullback h).map
        (Scheme.Modules.dualEvaluation (oldIdeal s).toModules) ≫ (unitComparison h).hom
  multiplication : (Scheme.Modules.tensorPullback h).map (inclusion d.ker) ≫ dual.hom =
    (unitComparison h).hom ≫ inclusion d'.ker
  divisor_multiplication :
    (Scheme.Modules.tensorPullback h).map (inclusion (oldIdeal s)) ≫ divisorDual.hom =
      (unitComparison h).hom ≫ inclusion (oldIdeal s')
  first : (Scheme.Modules.tensorPullback h).map (firstToK s d) ≫ quotient.hom =
    dual.hom ≫ firstToK s' d'
  second : (Scheme.Modules.tensorPullback h).map (secondToK s d) ≫ quotient.hom =
    divisorDual.hom ≫ secondToK s' d'
  exact_left : Mono ((Scheme.Modules.tensorPullback h).map (diagonal s d))

/-- Compatibility of relative Proj with a comparison of the specified cokernels. The line
isomorphism preserves the tautological quotient; this characterizes the comparison map.
The last two equations retain every ordered marking and the arbitrary extra section.
Source: Knudsen II, Theorem 2.4; arXiv:1106.1588, Theorem 5.2
(blueprint: lem-sfb-section-ideal-proj-expansion). -/
def Compatible {T X T' X' : Scheme.{u}} {r : ℕ}
    (f : X ⟶ T) (s : Fin r → (T ⟶ X)) (d : T ⟶ X)
    (f' : X' ⟶ T') (s' : Fin r → (T' ⟶ X')) (d' : T' ⟶ X')
    [(moduleK s d).IsQuasicoherent] [(moduleK s' d').IsQuasicoherent]
    (L : Lifts f s d) (L' : Lifts f' s' d')
    (h : X' ⟶ X) (b : T' ⟶ T) (C : SequenceComparison s d s' d' h)
    (j : schemeZ s' d' ⟶ schemeZ s d) : Prop :=
  ∃ square : IsPullback j (projection s' d') (projection s d) h,
    (∃ e : (Scheme.Modules.tensorPullback j).obj L.tautological.line ≅ L'.tautological.line,
      (Scheme.Modules.tensorPullbackSectionComp j (projection s d)).hom.app (moduleK s d) ≫
          (Scheme.Modules.tensorPullback j).map L.tautological.quotient ≫ e.hom =
        (eqToIso (congrArg (fun k ↦ (Scheme.Modules.tensorPullback k).obj (moduleK s d))
          square.w)).hom ≫
        (Scheme.Modules.tensorPullbackSectionComp (projection s' d') h).hom.app
          (moduleK s d) ≫
        (Scheme.Modules.tensorPullback (projection s' d')).map C.quotient.hom ≫
        L'.tautological.quotient) ∧
    (∀ i : Fin r, L'.old i ≫ j = b ≫ L.old i) ∧ L'.extra ≫ j = b ≫ L.extra

/-- The section-ideal Proj expansion, with its exact sequence, quotient-defined lifts,
three geometric-fibre cases, and canonical arbitrary-base-change and isomorphism comparisons.

Source: Knudsen II, Section 2, Lemma 2.2, Definition 2.3 and Theorem 2.4;
arXiv:1106.1588, Main Lemma and Sections 3--5
(blueprint: lem-sfb-section-ideal-proj-expansion).

Proof:
1. Use lem-trf-nodal-family-etale-local-model and etale base change to lift the section
   to an affine nodal chart A[x,y]/(xy-ab), with its coordinates evaluating to a,b.
2. The etale-section-clopen-immersion lemma removes the complementary components of the
   inverse image of the section. Its ideal is exactly (x-a,y-b). At a smooth point use
   lem-sc-smooth-section-affine-coordinates to obtain a regular coordinate z; near an old
   marking the extra section has equation z=c.
3. Apply lem-sfb-split-node-section-dual-presentation and etale-algebra-flat: the dual
   ideal has generators 1,e and relations a+(x-a)e=0 and -y+(y-b)e=0. Its multiplication
   inclusion is injective, its section quotient is a line, and all commute with arbitrary
   coefficient change. In the smooth chart use J=(z), J-dual=z^{-1}O.
4. First descend finite presentation of J using new-etale-finite-affine-cech-basis,
   lem-sc-etale-standard-cover-cech and finite-presentation-module-descent-flat-local.
   Then express Hom(J,O) as the kernel of a finite matrix. Flat chart change preserves
   this kernel. Faithfully flat reflection descends finite presentation of the dual,
   and its canonical comparisons after arbitrary base change, with no flatness of that
   base change assumed.
5. Properness makes the sections closed. The smooth coordinate makes the old divisor
   ideal Cartier after every base change. The diagonal is injective; its explicitly
   constructed cokernel is quasi-coherent and finitely presented, and tensor products
   preserve its presentation and the full sequence.
6. Quotienting by either summand gives O(D)/O and J-dual/O. Their restrictions to the
   respective sections are lines. lem-trf-projective-bundle-quotient-geometry gives the
   unique lifts classifying precisely these quotients.
7. Away from collisions and singular points on the extra section, eliminate a unit
   diagonal summand. K is invertible there, so its projective bundle is the base itself.
8. At a smooth collision K has relation (z-c)U+zV=0. The U-chart is A[z,w]/(zw-c).
   The complementary part of the V-chart is A[u,(u+1)^{-1}], with z=cu/(u+1).
9. At a nodal point the symmetric algebra has relations aU+(x-a)V and -yU+(y-b)V.
   Its charts are A[y,w]/(yw-b) and A[q,v,(v-1)^{-1}]/(qv+a).
10. The monomials 1,r,r^2,...,s,s^2,... form an A-basis of A[r,s]/(rs-d).
    Thus all charts are flat over any A, including nonreduced and non-Noetherian A.
11. Compose this flatness with etale chart flatness, and descend through faithfully
    flat local homomorphisms by lem-weil-pbc-flat-algebra-faithfully-flat-descent.
12. The finite-type projective-bundle-proper theorem gives properness. Finite module
    presentations give finitely many homogeneous equations, hence finite presentation
    on standard affine charts and, by properness, quasi-compactness and quasi-separatedness.
13. On a geometric fibre away from the exceptional cases K is a line and p is an
    isomorphism. At a collision the chart z(U+V)=0 inserts a P1 with the two lifted
    markings and the one distinct attachment, also in characteristic two.
14. At a node the charts insert a P1 meeting the old branches in two distinct points.
    The extra marking is the smooth point w=1. Outside this P1 the map is an isomorphism.
15. The same chart calculations prove that all lifted markings are smooth and pairwise
    disjoint. The old component normalizations and their special-point preimages agree;
    a colliding marking or an old branch is replaced by its attachment.
16. Apply nodal-curve-normalization-euler and reduced-curve-normalization-genus. Adding
    the rational component adds one vertex and one net edge, so chi(O) and H1 dimension
    are unchanged. Connectedness and reduced nodal pure dimension one follow from the charts.
17. Symmetric-algebra-base-change and relative-proj-base-change-arbitrary identify the
    constructed Proj under every base change. The ideal, dual and quotient comparisons
    preserve inclusions and evaluation; the line quotient fixes the comparison on Proj.
18. The same normalized comparisons apply to isomorphisms preserving the ordered old
    sections and the extra section. Uniqueness of the classifying maps preserves every lift. -/
theorem section_ideal_proj_expansion
    (T X : Scheme.{u}) (f : X ⟶ T) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (g : ℕ) (hg : 2 ≤ g)
    (hfibres : FibreConditions f g) (r : ℕ) (s : Fin r → (T ⟶ X))
    (hs : ∀ i : Fin r, s i ≫ f = 𝟙 T)
    (hdisjoint : Pairwise (fun i j : Fin r ↦ Disjoint (Set.range (s i)) (Set.range (s j))))
    (hsmooth : ∀ i : Fin r, Set.range (s i) ⊆ (f.smoothLocus : Set X))
    (d : T ⟶ X) (hd : d ≫ f = 𝟙 T) :
    (oldIdeal s).IsInvertible ∧ Mono (diagonal s d) ∧
      (moduleK s d).IsFinitePresentation ∧
      ∃ hqc : (moduleK s d).IsQuasicoherent,
        ∃ hfp : LocallyOfFinitePresentation (projection s d ≫ f),
          ∃ L : Lifts f s d,
            IsProper (projection s d ≫ f) ∧ Flat (projection s d ≫ f) ∧
            FibreConditions (projection s d ≫ f) g ∧
            (∀ i : Fin r,
              Set.range (L.old i) ⊆ ((projection s d ≫ f).smoothLocus : Set _)) ∧
            Set.range L.extra ⊆ ((projection s d ≫ f).smoothLocus : Set _) ∧
            FibreGeometry f s hs d hd L ∧
            ∀ (T' X' : Scheme.{u}) (f' : X' ⟶ T') (b : T' ⟶ T) (h : X' ⟶ X),
              IsPullback h f' f b →
              ∀ (s' : Fin r → (T' ⟶ X')) (d' : T' ⟶ X'),
                (∀ i : Fin r, s' i ≫ h = b ≫ s i) → d' ≫ h = b ≫ d →
                (∀ i : Fin r, s' i ≫ f' = 𝟙 T') → d' ≫ f' = 𝟙 T' →
                ∃ hqc' : (moduleK s' d').IsQuasicoherent,
                  ∃ L' : Lifts f' s' d',
                    ∃! C : SequenceComparison s d s' d' h,
                      ∃! j : schemeZ s' d' ⟶ schemeZ s d,
                        Compatible f s d f' s' d' L L' h b C j := by
  sorry

end AlgebraicGeometry.SectionIdealExpansion
