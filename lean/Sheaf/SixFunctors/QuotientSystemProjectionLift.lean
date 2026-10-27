module

public import Sheaf.SixFunctors.QuotientSystemEvaluationData
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.ProjectionMateExact
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.CategoryTheory.DiagramRingRestrictionPushforward
import Sheaf.CategoryTheory.SystemDerivedEvaluation
import Sheaf.CategoryTheory.SequenceAdjunctionCochainTransposes

/-! # The coefficient-system lift of the augmented projection mate

Source: Stacks 0B56, equation-projection-formula-map, and 0D6E,
lemma-derived-pushforward-composition, on the small ringed diagram sites
(blueprint: lem-sfb-quotient-system-projection-lift).

## Main definitions and statements

* `beta` and `restrictedBeta`: the actual coefficient mate and its ambient restriction.
* `LiftAssertions`: the strict and evaluated comparison identities.
* `quotientSystemProjectionLift`: existence and all required compatibilities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency true

universe uC vC uD vD r wY wX wTY wTX wQY wQX wLY wLX
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open CategoryTheory.CochainPullback CategoryTheory.StrictReduction
namespace CategoryTheory.QuotientProjection
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}
variable (Q : ℕᵒᵖ ⥤ Modules R) [MonObj Q]
  [HasDerivedCategory.{wY} (Modules R)]
  [HasDerivedCategory.{wTY} (ℕᵒᵖ ⥤ Modules R)]
  [HasDerivedCategory.{wQY} (Systems Q)]
  (f : RingedPullback R S) [f.L.Monoidal]
  [PreservesFiniteLimits f.L] [PreservesFiniteColimits f.L]
  [HasDerivedCategory.{wX} (Modules S)]
  [HasDerivedCategory.{wTX} (ℕᵒᵖ ⥤ Modules S)]
  [HasDerivedCategory.{wQX} (Systems ((termwise f.L).obj Q))]
  [f.V.Additive] (k : Comparison f)
  (MY : RingedModel Q (MonObj.one (X := Q)))
  (MX : RingedModel (Q ⋙ f.L)
    (pulledUnit f.L (moduleUnit f k) Q (MonObj.one (X := Q))))
  (P : AugmentedProjectionDirectImage f.L f.V f.moduleAdj)

/-- The coefficient-linear natural projection morphism, defined by the adjunction unit,
then the normalized tensor comparison and the ambient counit. It is a morphism in the
derived category of strict systems before any evaluation.
Source: Stacks 0B56, equation-projection-formula-map
(blueprint: lem-sfb-quotient-system-projection-lift). -/
def beta (L : Lift Q f k MY MX P) : P.RG ⋙ L.Y.B ⟶ L.X.B ⋙ L.G :=
  Functor.whiskerLeft (P.RG ⋙ L.Y.B) L.adj.unit ≫
    Functor.whiskerRight (Functor.whiskerLeft P.RG L.tau.hom) L.G ≫
      Functor.whiskerRight (Functor.whiskerRight P.d.counit L.X.B) L.G

/-- Restriction of the coefficient mate, conjugated by the specified canonical
scalar and direct-image comparisons. This is still one strict-system morphism.
Source: Stacks 0D6E and 0B56
(blueprint: lem-sfb-quotient-system-projection-lift). -/
def restrictedBeta (L : Lift Q f k MY MX P) : P.RG ⋙ MY.B ⟶ MX.B ⋙ P.RT :=
  Functor.whiskerLeft P.RG L.Y.underlying.inv ≫
    Functor.whiskerRight (beta Q f k MY MX P L) (Mod.forget Q).mapDerivedCategory ≫
      Functor.whiskerLeft L.X.B L.d.hom ≫
        Functor.whiskerRight L.X.underlying.hom P.RT

/-- The underlying scalar/pullback comparison, including the exact restriction square.
Source: Stacks 0D6D (blueprint: lem-sfb-quotient-system-projection-lift). -/
def underlyingTensor (L : Lift Q f k MY MX P) :
    MY.B ⋙ (termwise f.L).mapDerivedCategory ≅ f.L.mapDerivedCategory ⋙ MX.B :=
  Functor.isoWhiskerRight L.Y.underlying.symm (termwise f.L).mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft L.Y.B (pullbackRestriction Q f) ≪≫
      Functor.isoWhiskerRight L.tau (Mod.forget ((termwise f.L).obj Q)).mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft f.L.mapDerivedCategory L.X.underlying

variable [levelY : ∀ n : ℕᵒᵖ, HasDerivedCategory.{wLY} (Level Q n)]
  [levelX : ∀ n : ℕᵒᵖ,
    HasDerivedCategory.{wLX} (Level ((termwise f.L).obj Q) n)]

/-- All assertions about the canonical coefficient mate: its actual transpose,
restriction before evaluation, coefficient-linear evaluated transposes, the evaluated
scalar-extension universal properties, augmentation, and joint conservativity.
Source: Stacks 0B56, 07A6, 0D6D and 0D6E
(blueprint: lem-sfb-quotient-system-projection-lift). -/
def LiftAssertions
    (tau : MY.B ⋙ (termwise f.L).mapDerivedCategory ≅ f.L.mapDerivedCategory ⋙ MX.B)
    (L : Lift Q f k MY MX P) : Prop :=
  underlyingTensor Q f k MY MX P L = tau ∧
  (∀ M : DerivedCategory (Modules S),
    (pullback Q f).mapDerivedCategory.map ((beta Q f k MY MX P L).app M) ≫
        L.adj.counit.app (L.X.B.obj M) =
      L.tau.hom.app (P.RG.obj M) ≫ L.X.B.map (P.d.counit.app M)) ∧
  restrictedBeta Q f k MY MX P L =
    augmentedDiagramProjection f.L f.V f.moduleAdj P MY.B MX.B tau ∧
  (∀ n : ℕᵒᵖ,
    letI := levelY n
    letI := levelX n
    Nonempty (EvaluationLift Q f k MY MX P L n)) ∧
  (∀ n : ℕᵒᵖ,
    letI := levelY n
    letI := levelX n
    ∀ (E : EvaluationLift Q f k MY MX P L n) (M : DerivedCategory (Modules S)),
    (coefficientEvaluation Q n).mapDerivedCategory.map ((beta Q f k MY MX P L).app M) ≫
        E.2.gamma.hom.app (L.X.B.obj M) =
      E.2.adj.homEquiv
        ((coefficientEvaluation Q n).mapDerivedCategory.obj (L.Y.B.obj (P.RG.obj M)))
        ((coefficientEvaluation ((termwise f.L).obj Q) n).mapDerivedCategory.obj (L.X.B.obj M))
        ((evaluationPullback Q f k n E.1).hom.app (L.Y.B.obj (P.RG.obj M)) ≫
          (coefficientEvaluation ((termwise f.L).obj Q) n).mapDerivedCategory.map
            (L.tau.hom.app (P.RG.obj M)) ≫
          (coefficientEvaluation ((termwise f.L).obj Q) n).mapDerivedCategory.map
            (L.X.B.map (P.d.counit.app M)))) ∧
  (∀ n : ℕᵒᵖ,
    letI := levelY n
    letI := levelX n
    (L.Y.B ⋙ (coefficientEvaluation Q n).mapDerivedCategory).IsLeftDerivedFunctor
      (evaluationCounit Q (MonObj.one (X := Q)) MY L.Y n)
      (HomologicalComplex.quasiIso (Modules R) (.up ℤ)) ∧
    Functor.IsLeftDerivedFunctor
      (L.X.B ⋙ (coefficientEvaluation ((termwise f.L).obj Q) n).mapDerivedCategory)
        (evaluationCounit ((termwise f.L).obj Q)
          (pulledUnit f.L (moduleUnit f k) Q (MonObj.one (X := Q))) MX L.X n)
        (HomologicalComplex.quasiIso (Modules S) (.up ℤ))) ∧
  (∀ M : DerivedCategory (Modules S),
    MY.i.app (P.RG.obj M) ≫ (restrictedBeta Q f k MY MX P L).app M =
      P.chi.hom.app M ≫ P.RT.map (MX.i.app M)) ∧
  (∀ M : DerivedCategory (Modules S),
    (∀ n : ℕᵒᵖ, IsIso (((evaluation ℕᵒᵖ (Modules R)).obj n).mapDerivedCategory.map
      ((augmentedDiagramProjection f.L f.V f.moduleAdj P MY.B MX.B tau).app M))) →
    IsIso ((beta Q f k MY MX P L).app M) ∧
      ∀ n : ℕᵒᵖ,
        letI := levelY n
        IsIso ((coefficientEvaluation Q n).mapDerivedCategory.map
        ((beta Q f k MY MX P L).app M)))

end CategoryTheory.QuotientProjection

namespace CategoryTheory.QuotientProjection

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}
  [HasDerivedCategory.{wY} (Modules R)] [HasDerivedCategory.{wX} (Modules S)]
  [HasDerivedCategory.{wTY} (ℕᵒᵖ ⥤ Modules R)]
  [HasDerivedCategory.{wTX} (ℕᵒᵖ ⥤ Modules S)]

/-- The canonical coefficient-system projection lift, on the ordinary unbounded derived
categories of strict systems. Level n represents the positive level n+1. The monoidal
presentation is supplied by the conclusion and is normalized by the recorded inverse-
image tensor and unit maps, so it imposes no extra monoidality hypothesis on f.
Source: Stacks 0B56, equation-projection-formula-map, and 0D6E,
lemma-derived-pushforward-composition, applied on the ringed diagram sites
(blueprint: lem-sfb-quotient-system-projection-lift).

Proof: Realize semilinear systems as modules over the algebra tower on the small
product site. Its exact scalar restriction has left adjoint scalar extension. Resolve
ambient complexes by flat-term K-flat complexes to obtain ScalarModel and its normalized
underlying comparison, including the braiding changing Q ⊗ P to P ⊗ Q. The canonical
inverse-image tensor/unit maps give the displayed CoreMonoidal presentation. The induced
module-object pullback is exact. Its derived right adjoint exists on these Grothendieck
module-sheaf categories. The two scalar/pullback factorizations give ordinaryTau and tau,
normalized on every flat-term K-flat representative. Derived composition on the ringed
diagram sites gives d; compatibility of the composite adjunctions is precisely its
counit equation. No faithfulness of derived scalar restriction is asserted or used.
Define beta by its actual adjunction unit, tau and the ambient counit. Taking its
transpose proves the first mate equation. Normalize tau and d as above; the transpose
of restrictedBeta is then the transpose of the recorded augmented ambient mate, proving
the strict-system equality by injectivity of the Hom equivalence. Evaluation is exact;
composition for the ringed evaluation morphism supplies EvaluationLift with its counit
equation and identifies evaluated scalar extension with the usual derived tensor.
Evaluating the actual transpose gives the coefficient-linear levelwise adjunct formula.
Every construction is on the diagram site, so it commutes with all semilinear transitions.
The ambient augmentation identity gives the displayed strict augmentation equation.
Finally, evaluations jointly detect acyclicity of strict towers. Exact scalar restriction
reflects zero homology and hence quasi-isomorphisms, so invertibility of all evaluations
of h implies invertibility of beta; exact evaluation preserves its inverse. No
perfectness, coefficient flatness, completeness or boundedness is used. -/
theorem quotientSystemProjectionLift
    (f : RingedPullback R S) [IsIso f.coefficient] [f.V.Additive]
    [PreservesFiniteLimits f.L] [PreservesFiniteColimits f.L]
    (k : Comparison f) (Q : CommMon (ℕᵒᵖ ⥤ Modules R))
    (MY : RingedModel Q.X (MonObj.one (X := Q.X)))
    (MX : RingedModel (Q.X ⋙ f.L)
      (pulledUnit f.L (moduleUnit f k) Q.X (MonObj.one (X := Q.X))))
    (tau : MY.B ⋙ (termwise f.L).mapDerivedCategory ≅ f.L.mapDerivedCategory ⋙ MX.B)
    (htau : IsNormalized f.L Q.X (MonObj.one (X := Q.X)) (moduleUnit f k)
      (flatRepresentatives R) (flatRepresentatives S) MY MX k.mu k.naturality tau)
    (P : AugmentedProjectionDirectImage f.L f.V f.moduleAdj) :
    ∃ m : f.L.CoreMonoidal,
      (∀ M N : Modules R, m.μIso M N = (k.mu M N).symm) ∧
      m.εIso = (moduleUnit f k).symm ∧
      letI := m.toMonoidal
      ∀ [HasDerivedCategory.{wQY} (Systems Q.X)]
        [HasDerivedCategory.{wQX} (Systems ((termwise f.L).obj Q.X))]
        [∀ n : ℕᵒᵖ, HasDerivedCategory.{wLY} (Level Q.X n)]
        [∀ n : ℕᵒᵖ,
          HasDerivedCategory.{wLX} (Level ((termwise f.L).obj Q.X) n)],
        (∃ L : Lift Q.X f k MY MX P, IsNormalizedLift Q.X f k MY MX P L) ∧
          ∀ L : Lift Q.X f k MY MX P,
            IsNormalizedLift Q.X f k MY MX P L → LiftAssertions Q.X f k MY MX P tau L := by
  sorry

end CategoryTheory.QuotientProjection
