/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Sheaf.Paper.CompletedOperationTowerSubstitution
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Paper.NormalizedDVRTower
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Algebra.Homology.KFlat
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Paper.SemilinearDerivedSections
/-! # Derived limit of a strict integral comparison tower

Source: Stacks Project, Tag 0941, `lemma-derived-limit-is-ok`; Tag 07A4,
`lemma-pullback-tensor-product`, for the finite comparison application
(blueprint: lem-pur-integral-tower-limit-comparison).

Strict towers are cochain complexes on the ringed sequence site, so their maps retain
all semilinear quotient transitions. Exponent n+1 is encoded by n : ℕ. The models
are the representative-normalized presentations of the substitution dependency,
with its ComparisonLaws supplied explicitly to the theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.IntegralTowerLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Index the two given schemes, without changing either site.
Source: Stacks Tag 0941; node setup
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def sites (X Y : Scheme.{t}) : Bool → Scheme.{t}
  | false => X
  | true => Y

/-- Flat-term K-flat levels of the actual strict quotient system.
Source: Stacks Tag 0941; node hypotheses
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def Good (X : Scheme.{t}) (T : CochainComplex (coefficientSequenceModules l E X) ℤ) :
    Prop :=
  ∀ n : ℕ,
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X n)
      (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj T) ∧
    ∀ k : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X n)
      ((((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj T).X k)

/-- The termwise finite inverse image, including quotient transitions.
Source: Stacks Tag 0941; node definition of F_f(T)
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def pullback {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)

/-- The signed direct-sum total tensor, on the whole coefficient system.
Source: Stacks Tag 0941; node definition of W
(blueprint: lem-pur-integral-tower-limit-comparison).
-/
def total (X : Scheme.{t}) :=
  coefficientTotalTensor.{u, t+1, t}
    (coefficientSequenceTopology (Scheme.ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X)

/-- A quadruple from the node: three normalized strict towers with flat-term K-flat
levels and a strict chain isomorphism, whose inverse also respects every transition.
Source: Stacks Tag 0941; node hypotheses
(blueprint: lem-pur-integral-tower-limit-comparison). -/
structure Input {X Y : Scheme.{t}} (f : X ⟶ Y) where
  T : CochainComplex (coefficientSequenceModules l E Y) ℤ
  U : CochainComplex (coefficientSequenceModules l E X) ℤ
  V : CochainComplex (coefficientSequenceModules l E X) ℤ
  goodT : Good l E Y T
  goodU : Good l E X U
  goodV : Good l E X V
  normalizedT : IsNormalizedCoefficientSequence l E Y (DerivedCategory.Q.obj T)
  normalizedU : IsNormalizedCoefficientSequence l E X (DerivedCategory.Q.obj U)
  normalizedV : IsNormalizedCoefficientSequence l E X (DerivedCategory.Q.obj V)
  c : (pullback l E f).obj T ≅ (total l E X).obj (U, V)

variable {X Y : Scheme.{t}} {f : X ⟶ Y}

/-- The completed pullback of the derived limit of T.
Source: Stacks Tag 0941; node object S
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def source (A : Input l E f) :=
  (integralDerivedPullback l E f).obj
    ((coefficientSequenceLimit l E Y).obj (DerivedCategory.Q.obj A.T))

/-- The completed tensor of the derived limits of U and V.
Source: Stacks Tag 0941; node object P
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def target (A : Input l E f) :=
  (IntegralOnSlice.completedTensor l E X none).obj
    ((coefficientSequenceLimit l E X).obj (DerivedCategory.Q.obj A.U),
     (coefficientSequenceLimit l E X).obj (DerivedCategory.Q.obj A.V))

/-- The canonical substitution identifications, with their exact counit formulas.
The whole-system K-flat proofs are conclusions from levelwise K-flatness, not hypotheses.
Source: Stacks Tag 0941; node proof steps 1 and 3
(blueprint: lem-pur-integral-tower-limit-comparison). -/
structure Realization (M : CompletedOperations.Models l E (sites X Y)) (A : Input l E f) where
  kflatU : CochainComplex.IsKFlatIndependentCoefficients
    (J := coefficientSequenceTopology (Scheme.ProEt.topology X))
    (R := coefficientSequenceCommRingSheaf l E X) A.U
  kflatV : CochainComplex.IsKFlatIndependentCoefficients
    (J := coefficientSequenceTopology (Scheme.ProEt.topology X))
    (R := coefficientSequenceCommRingSheaf l E X) A.V
  a : source l E A ≅
    (coefficientSequenceLimit l E X).obj (DerivedCategory.Q.obj ((pullback l E f).obj A.T))
  b : target l E A ≅
    (coefficientSequenceLimit l E X).obj (DerivedCategory.Q.obj ((total l E X).obj (A.U, A.V)))
  a_formula : a.hom =
    CompletedOperations.pullbackComparison l E M (a := false) (b := true) f
      (DerivedCategory.Q.obj A.T) ≫
    (coefficientSequenceLimit l E X).map
      ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app A.T)
  b_formula : b.hom =
    CompletedOperations.tensorComparison l E M false
      (DerivedCategory.Q.obj A.U) (DerivedCategory.Q.obj A.V) ≫
    (coefficientSequenceLimit l E X).map
      (((M.system false).models.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (coefficientSequenceCommRingSheaf l E X) (M.system false).closed
        A.U A.V kflatU kflatV).inv)

/-- The limit of the supplied strict isomorphism, conjugated by the prescribed
substitution isomorphisms. Its inverse uses the supplied strict inverse.
Source: Stacks Tag 0941; node proof steps 2--3
(blueprint: lem-pur-integral-tower-limit-comparison).
-/
def comparison {M : CompletedOperations.Models l E (sites X Y)} {A : Input l E f}
    (r : Realization l E M A) : source l E A ≅ target l E A :=
  r.a ≪≫ (coefficientSequenceLimit l E X).mapIso (DerivedCategory.Q.mapIso A.c) ≪≫ r.b.symm

/-- A commuting diagram of strict quadruples, using the actual total tensor on maps.
Source: Stacks Tag 0941; node diagram clause
(blueprint: lem-pur-integral-tower-limit-comparison).
-/
structure Diagram (A B : Input l E f) where
  t : A.T ⟶ B.T
  u : A.U ⟶ B.U
  v : A.V ⟶ B.V
  square : (pullback l E f).map t ≫ B.c.hom =
    A.c.hom ≫ (total l E X).map (u, v)

/-- The completed source map of a strict diagram, with no arbitrary comparison arrow.
Source: Stacks Tag 0941; node proof step 5
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def sourceMap {A B : Input l E f} (d : Diagram l E A B) : source l E A ⟶ source l E B :=
  (integralDerivedPullback l E f).map
    ((coefficientSequenceLimit l E Y).map (DerivedCategory.Q.map d.t))

/-- The completed target map of the same diagram.
Source: Stacks Tag 0941; node proof step 5
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def targetMap {A B : Input l E f} (d : Diagram l E A B) : target l E A ⟶ target l E B :=
  (IntegralOnSlice.completedTensor l E X none).map
    (Prod.mkHom ((coefficientSequenceLimit l E X).map (DerivedCategory.Q.map d.u))
      ((coefficientSequenceLimit l E X).map (DerivedCategory.Q.map d.v)))

/-- Reduction of the specified source substitution, followed by the coherent counit.
Source: Stacks Tag 0941; node proof step 4
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def sourceReduction {M : CompletedOperations.Models l E (sites X Y)} {A : Input l E f}
    (r : Realization l E M A) :=
  (M.calculus false).reduction.map r.a.hom ≫
    (M.calculus false).adjunction.counit.app (DerivedCategory.Q.obj ((pullback l E f).obj A.T))

/-- Reduction of the specified target substitution, followed by the coherent counit.
Source: Stacks Tag 0941; node proof step 4
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def targetReduction {M : CompletedOperations.Models l E (sites X Y)} {A : Input l E f}
    (r : Realization l E M A) :=
  (M.calculus false).reduction.map r.b.hom ≫
    (M.calculus false).adjunction.counit.app
      (DerivedCategory.Q.obj ((total l E X).obj (A.U, A.V)))

/-- All assertions about the induced map, in the coherent system category itself.
The last clause uses quasi-isomorphisms of representatives: naturality then identifies
maps under the canonical resolution comparisons already fixed by a_formula and b_formula.
Source: Stacks Tag 0941; node conclusions
(blueprint: lem-pur-integral-tower-limit-comparison). -/
def Laws {M : CompletedOperations.Models l E (sites X Y)} {A : Input l E f}
    (r : Realization l E M A) : Prop :=
  (comparison l E r).hom ≫ (comparison l E r).inv = 𝟙 _ ∧
  (comparison l E r).inv ≫ (comparison l E r).hom = 𝟙 _ ∧
  IsIso (sourceReduction l E r) ∧ IsIso (targetReduction l E r) ∧
  (M.calculus false).reduction.map (comparison l E r).hom ≫ targetReduction l E r =
    sourceReduction l E r ≫ DerivedCategory.Q.map A.c.hom ∧
  (M.calculus false).reduction.map (comparison l E r).inv ≫ sourceReduction l E r =
    targetReduction l E r ≫ DerivedCategory.Q.map A.c.inv ∧
  ∀ (B : Input l E f) (r' : Realization l E M B) (d : Diagram l E A B),
    sourceMap l E d ≫ r'.a.hom =
      r.a.hom ≫ (coefficientSequenceLimit l E X).map
        (DerivedCategory.Q.map ((pullback l E f).map d.t)) ∧
    targetMap l E d ≫ r'.b.hom =
      r.b.hom ≫ (coefficientSequenceLimit l E X).map
        (DerivedCategory.Q.map ((total l E X).map (d.u, d.v))) ∧
    sourceMap l E d ≫ (comparison l E r').hom =
      (comparison l E r).hom ≫ targetMap l E d ∧
    targetMap l E d ≫ (comparison l E r').inv =
      (comparison l E r).inv ≫ sourceMap l E d ∧
    (QuasiIso d.t → QuasiIso d.u → QuasiIso d.v →
      IsIso (sourceMap l E d) ∧ IsIso (targetMap l E d))

/-- Derived limit of the strict integral comparison tower, including coherent reduction,
strict diagram naturality, and independence under simultaneous quasi-isomorphisms.
The presentation is equipped with the ComparisonLaws supplied by
completedOperationTowerSubstitution; bare Models data alone is not sufficient.

Source: Stacks Project, Tag 0941 and the supporting comparison extracted for Tag 07A4
(blueprint: lem-pur-integral-tower-limit-comparison).

Proof: (1) Exact finite pullback computes derived pullback, and K-flat levels compute
finite derived total tensor. Evaluation detects acyclicity, so the levelwise K-flat
hypotheses also give K-flatness on the ringed sequence site. The substitution lemma
and the supplied ComparisonLaws identify these normalized systems with the displayed
completed operations.
(2) Apply the actual total derived inverse-limit functor to c and its specified inverse;
functoriality preserves both inverse equations. (3) Conjugate by the substitution
isomorphisms whose formulas are a_formula and b_formula. (4) The normalized-DVR
counits are coherent isomorphisms. Counit naturality gives both reduction equations
in the whole system category, hence with every quotient transition.
(5) For a commuting strict diagram use naturality of substitution and L(yc)=L(c'x)
to obtain the forward square; the inverse square follows from xc⁻¹=c'⁻¹y.
(6) Simultaneous quasi-isomorphisms localize to isomorphisms. The unique compatible
resolution comparisons of integralOperationsWellDefined identify sourceMap and
targetMap with the canonical changes of representatives, giving the stated independence.
No boundedness or constructibility is used. -/
theorem integralTowerLimitComparison (f : X ⟶ Y)
    (_hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hlY : ∀ y : Y, IsUnit (l : Y.residueField y))
    (M : CompletedOperations.Models l E (sites X Y))
    (_hM : CompletedOperations.ComparisonLaws.{t, u, 0, 0} l E M) (A : Input l E f) :
    ∃ r : Realization l E M A, Laws l E r := by
  sorry

end WeilConjectures.IntegralTowerLimit
