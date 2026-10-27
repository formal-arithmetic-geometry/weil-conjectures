module

public import Sheaf.Paper.PointRationalFamilyCommonStageNaturality
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.PointFdQbarCategory
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.PointSectionsScalarExtension
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.PointFibreDerivedTensorBasic
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Composite point-section comparison and common-stage actions

Source: Deligne, Weil II (1.1.3), p. 150, coefficient-localization context;
the normalized comparison calculation is the agent-written DAG proof
(blueprint: lem-weil-point-composite-comparison-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

namespace WeilConjectures.PointCompositeComparison

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (g : Spec (.of D.k) ⟶ Spec (.of D.k))

/-- Package the specified rational pullback, supplying the implied invertibility.
Source: Weil II (1.1.3), normalized DAG calculation
(blueprint: lem-weil-point-composite-comparison-tower). -/
abbrev pullback (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  PointRationalFamily.rationalPullback D l hl g E

/-- H_E is the composite of the specified pullback and point sections.
Source: Weil II (1.1.3), normalized DAG calculation
(blueprint: lem-weil-point-composite-comparison-tower). -/
abbrev sectionsPullback (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  pullback D l hl g E ⋙ pointRationalFibre D l hl E

variable (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)

/-- The natural isomorphism b is F(alpha inverse), followed by phi at P.
Both factors are the specified rationalized completed comparisons.
Source: Weil II (1.1.3), normalized DAG displayed definition of b
(blueprint: lem-weil-point-composite-comparison-tower). -/
def comparison :
    sfRationalScalarExtension l E (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙ sectionsPullback D l hl g L ≅
      sectionsPullback D l hl g E ⋙ DerivedCategory.pointFdScalarExtension ι.toRingHom :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rationalPullbackScalarComparison l E L ι g).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pointRationalFibreScalarIso D l hl E L ι) ≪≫
    (Functor.associator _ _ _).symm

variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The specified pullback on literal common-stage pairs.
Source: Weil II (1.1.3), common-stage paragraph
(blueprint: lem-weil-point-composite-comparison-tower). -/
abbrev commonPullback :=
  PointRationalFamily.commonPullback D l hl Ω g

/-- Literal object formula for that pullback; no change of coefficient field.
Source: Weil II (1.1.3), common-stage paragraph
(blueprint: lem-weil-point-composite-comparison-tower). -/
abbrev pullbackPair (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :=
  PointRationalFamily.pullbackObject D l hl Ω g A

/-- The normalized alpha with the specified source-stage identifications inserted.
Source: Weil II (1.1.3), common-stage paragraph
(blueprint: lem-weil-point-composite-comparison-tower). -/
abbrev stageAlpha
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (h : A.stage ≤ N) :=
  PointRationalFamily.pullbackComparison D l hl Ω g A N h

/-- The composite comparison b with the prescribed small coefficient transports.
Source: Weil II (1.1.3), common-stage paragraph
(blueprint: lem-weil-point-composite-comparison-tower). -/
abbrev stageComparison
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (h : A.stage ≤ N) :=
  PointRationalFamily.stageB D l hl Ω g A N h

variable
  (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
  (N : Index l Ω) (hA : A.stage ≤ N) (hB : B.stage ≤ N)
  (f : A.toStage hA ⟶ B.toStage hB)

/-- The first displayed action A_N(f), with phi in its specified direction.
Source: Weil II (1.1.3), DAG common-stage formula
(blueprint: lem-weil-point-composite-comparison-tower). -/
abbrev sectionsArrow :=
  PointRationalFamily.fibreArrow D l hl Ω A B N hA hB f

/-- The second displayed action B_N(f), using precisely the composite b.
Source: Weil II (1.1.3), DAG common-stage formula
(blueprint: lem-weil-point-composite-comparison-tower). -/
abbrev compositeArrow :=
  PointRationalFamily.pullbackArrow D l hl Ω g A B N hA hB f

/-- The finite-stage class in the specified point-complex category.
Source: Weil II (1.1.3), DAG common-stage interpretation
(blueprint: lem-weil-point-composite-comparison-tower). -/
abbrev representativeClass (X Y : DerivedCategory.PointFdQbar l Ω)
    (M : Index l Ω) (hX : X.1 ≤ M) (hY : Y.1 ≤ M)
    (v : (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hX).toRingHom).obj X.2 ⟶
      (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hY).toRingHom).obj Y.2) : X ⟶ Y :=
  PointRationalFamily.pointClass l Ω X Y M hX hY v

/-- The class of A_N(f), retaining exactly the source representative field N.
Source: Weil II (1.1.3), DAG common-stage interpretation
(blueprint: lem-weil-point-composite-comparison-tower). -/
abbrev sectionsClass :=
  PointRationalFamily.fibreClass D l hl Ω A B N hA hB f

/-- The class of B_N(f), retaining exactly the source representative field N.
Source: Weil II (1.1.3), DAG common-stage interpretation
(blueprint: lem-weil-point-composite-comparison-tower). -/
abbrev compositeClass :=
  PointRationalFamily.pullbackClass D l hl Ω g A B N hA hB f

/-- Target transport is scalar extension conjugated by the specified tensor associators.
Source: Weil II (1.1.3), DAG further-extension formula
(blueprint: lem-weil-point-composite-comparison-tower). -/
abbrev targetTransport (X Y : DerivedCategory.PointFdQbar l Ω)
    (N M : Index l Ω) (hX : X.1 ≤ N) (hY : Y.1 ≤ N) (h : N ≤ M)
    (v : (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hX).toRingHom).obj X.2 ⟶
      (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hY).toRingHom).obj Y.2) :=
  PointRationalFamily.pointTransport l Ω X Y N M hX hY h v

/-- Every rational arrow satisfies naturality; the unit is the specified scalar unit.
The underlying derived equality avoids introducing a second point-unit construction.
Source: Weil II (1.1.3), DAG naturality and identity-extension clauses
(blueprint: lem-weil-point-composite-comparison-tower). -/
def NaturalityAndUnit : Prop :=
  (∀ (F G : Index l Ω) (h : F ≤ G)
    (K J : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))) (v : K ⟶ J),
    (sectionsPullback D l hl g (Coefficient.{u} l Ω G)).map
        ((sfRationalScalarExtension l (Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h)).map v) ≫
      (comparison D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G) (coefficientInclusion l Ω
        F G h)).hom.app J =
    (comparison D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G) (coefficientInclusion l Ω F
      G h)).hom.app K ≫
      (DerivedCategory.pointFdScalarExtension (coefficientInclusion l Ω F G h).toRingHom).map
        ((sectionsPullback D l hl g (Coefficient.{u} l Ω F)).map v)) ∧
  (∀ (F : Index l Ω) (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of
    D.k))),
    ((comparison D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω F) (AlgHom.id ℚ_[l]
      (Coefficient.{u} l Ω F))).hom.app K).hom ≫
        (DerivedCategory.fieldScalarUnit (Coefficient.{u} l Ω F)).hom.app
          ((sectionsPullback D l hl g (Coefficient.{u} l Ω F)).obj K).obj =
      ((sectionsPullback D l hl g (Coefficient.{u} l Ω F)).map
        ((sfRationalScalarUnit l (Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app K)).hom)

/-- The displayed b tower equation, with both specified associators in their directions.
Source: Weil II (1.1.3), DAG tower equation
(blueprint: lem-weil-point-composite-comparison-tower). -/
def Tower : Prop :=
  ∀ (F G H : Index l Ω) (h : F ≤ G) (k : G ≤ H)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    (sectionsPullback D l hl g (Coefficient.{u} l Ω H)).map
        ((sfRationalScalarComp l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h)
          (Spec (.of D.k)) 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω H)
          (coefficientInclusion l Ω G H k)).hom.app K) ≫
      (comparison D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω H)
        ((coefficientInclusion l Ω G H k).comp (coefficientInclusion l Ω F G h))).hom.app K =
    (comparison D l hl g (Coefficient.{u} l Ω G) (Coefficient.{u} l Ω H) (coefficientInclusion l Ω G
      H k)).hom.app
        ((sfRationalScalarExtension l (Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h)).obj K) ≫
      (DerivedCategory.pointFdScalarExtension (coefficientInclusion l Ω G H k).toRingHom).map
        ((comparison D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G) (coefficientInclusion
          l Ω F G h)).hom.app K) ≫
      (pointFibreFdTensorTower (coefficientInclusion l Ω F G h).toRingHom
        (coefficientInclusion l Ω G H k).toRingHom).hom.app
          ((sectionsPullback D l hl g (Coefficient.{u} l Ω F)).obj K)

/-- The formulas compute the two actual functors, and B is the point image of the
prescribed pullback representative, before taking its class.
Source: Weil II (1.1.3), DAG actual-action clauses
(blueprint: lem-weil-point-composite-comparison-tower). -/
def ActualActions : Prop :=
  ∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (hA : A.stage ≤ N) (hB : B.stage ≤ N)
    (f : A.toStage hA ⟶ B.toStage hB),
    HEq ((pointQbarFibre D l hl Ω).map (StageSystem.PairCategory.mkHom N hA hB f))
      (sectionsClass D l hl Ω A B N hA hB f) ∧
    HEq ((commonPullback D l hl g Ω ⋙ pointQbarFibre D l hl Ω).map
      (StageSystem.PairCategory.mkHom N hA hB f))
      (compositeClass D l hl g Ω A B N hA hB f) ∧
    compositeArrow D l hl g Ω A B N hA hB f =
      sectionsArrow D l hl Ω (pullbackPair D l hl g Ω A) (pullbackPair D l hl g Ω B)
        N hA hB ((stageAlpha D l hl g Ω A N hA).hom ≫
          (pullback D l hl g (Coefficient.{u} l Ω N)).map f ≫
          (stageAlpha D l hl g Ω B N hB).inv)

/-- Identity and composition are preserved over the same common coefficient field.
Source: Weil II (1.1.3), DAG identity/composition clauses
(blueprint: lem-weil-point-composite-comparison-tower). -/
def IdentitiesAndComposition : Prop :=
  (∀ (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (hA : A.stage ≤ N),
    sectionsArrow D l hl Ω A A N hA hA (𝟙 _) = 𝟙 _ ∧
      compositeArrow D l hl g Ω A A N hA hA (𝟙 _) = 𝟙 _) ∧
  (∀ (A B C : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (hA : A.stage ≤ N) (hB : B.stage ≤ N) (hC : C.stage ≤ N)
    (f : A.toStage hA ⟶ B.toStage hB) (v : B.toStage hB ⟶ C.toStage hC),
    sectionsArrow D l hl Ω A C N hA hC (f ≫ v) =
      sectionsArrow D l hl Ω A B N hA hB f ≫ sectionsArrow D l hl Ω B C N hB hC v ∧
    compositeArrow D l hl g Ω A C N hA hC (f ≫ v) =
      compositeArrow D l hl g Ω A B N hA hB f ≫
        compositeArrow D l hl g Ω B C N hB hC v)

/-- Both formulas commute with extension of representatives by the specified associators.
No injectivity hypothesis is imposed on transition maps.
Source: Weil II (1.1.3), DAG further-extension clauses
(blueprint: lem-weil-point-composite-comparison-tower). -/
def Extension : Prop :=
  ∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N M : Index l Ω) (hA : A.stage ≤ N) (hB : B.stage ≤ N) (h : N ≤ M)
    (f : A.toStage hA ⟶ B.toStage hB),
    HEq (targetTransport l Ω (pointQbarFibreObj D l hl Ω A)
      (pointQbarFibreObj D l hl Ω B) N M hA hB h
      (sectionsArrow D l hl Ω A B N hA hB f))
      (sectionsArrow D l hl Ω A B M (hA.trans h) (hB.trans h)
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).tr h f)) ∧
    HEq (targetTransport l Ω
      (pointQbarFibreObj D l hl Ω (pullbackPair D l hl g Ω A))
      (pointQbarFibreObj D l hl Ω (pullbackPair D l hl g Ω B)) N M hA hB h
      (compositeArrow D l hl g Ω A B N hA hB f))
      (compositeArrow D l hl g Ω A B M (hA.trans h) (hB.trans h)
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).tr h f))

/-- Every equivalent representative gives the same two target classes.
Source: Weil II (1.1.3), DAG eventual-equality clause
(blueprint: lem-weil-point-composite-comparison-tower). -/
def Independent : Prop :=
  ∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N M : Index l Ω) (hA : A.stage ≤ N) (hB : B.stage ≤ N)
    (hA' : A.stage ≤ M) (hB' : B.stage ≤ M)
    (f : A.toStage hA ⟶ B.toStage hB) (f' : A.toStage hA' ⟶ B.toStage hB'),
    StageSystem.PairCategory.mkHom N hA hB f =
      StageSystem.PairCategory.mkHom M hA' hB' f' →
    sectionsClass D l hl Ω A B N hA hB f = sectionsClass D l hl Ω A B M hA' hB' f' ∧
      compositeClass D l hl g Ω A B N hA hB f =
        compositeClass D l hl g Ω A B M hA' hB' f'

/-- The composite point-section comparison and both prescribed common-stage actions.

Source: Deligne, Weil II (1.1.3), p. 150; (1.1.7) gives point-transport context only.
The normalized completed comparison calculation is the agent-written DAG proof
(blueprint: lem-weil-point-composite-comparison-tower).

Proof:
1. Rationalize the normalized integral comparisons of
lem-pur-integral-operations-scalar-extension and lem-weil-point-sections-scalar-extension.
Their inverse, unit and tower equations survive tensoring. Every rational arrow is a
finite sum of pure tensors (def-weil-rationalization-karoubi); linearity of the recorded
pullback and sections actions proves naturality for each summand and then for the sum.
2. Put d = alpha inverse and phi = the sections comparison. Naturality of d, followed
by naturality of phi at P(v), gives naturality of b = F(d) followed by phi at P(K).
The normalized identity comparisons give the unit equation.
3. Invert the pullback tower equation and retain its scalar associator from
lem-weil-scalar-extension-composition. Retain the point-complex associator in the
sections tower equation of lem-weil-point-sections-scalar-extension.
4. Expand the composite of the two b components. Naturality of phi at d interchanges
T(F(d)) with phi. Its tower equation combines the two phi factors. The inverted
pullback tower combines the remaining d factors and the source associator. This is
exactly Tower, including both associators in the displayed directions.
5. def-weil-finite-coefficient-point sends [N,f] to the class of phi inverse, F(f), phi.
def-weil-derived-pullback-tensor-hom sends it to the class of alpha, P(f), alpha inverse.
Apply the former to this very representative. Expanding F of its composite gives
b inverse, H(f), b, so ActualActions computes the specified composite functor.
6. For either formula, identity follows by inverse cancellation. In a composition the
middle comparison and its inverse cancel, and functoriality gives the displayed map.
7. Apply further scalar extension. Substitute the source and target associators,
the sections tower equation and the b tower equation. Naturality at the arbitrary
rational arrow f cancels the middle comparisons, giving exactly Extension.
8. Equal source classes become equal at some common later field by
 def-weil-algebraically-closed-coefficients. Step 7 makes their two target transitions
equal there; the equality criterion of def-weil-point-fd-qlbar-category identifies
the target classes. This uses eventual equality only, with no injectivity assumption
and no supplied transformation components. -/
theorem tower_and_actions [IsIso g] :
    NaturalityAndUnit D l hl g Ω ∧ Tower D l hl g Ω ∧ ActualActions D l hl g Ω ∧
      IdentitiesAndComposition D l hl g Ω ∧ Extension D l hl g Ω ∧ Independent D l hl g Ω := by
  sorry

end WeilConjectures.PointCompositeComparison
