/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.PointFdQbarCategory
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.PointSectionsScalarExtension
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.PointFibreDerivedTensorBasic
public import Sheaf.Paper.SfScalarExtensionComposition

/-! # Same-stage naturality of a rational point family

Source: Deligne, Weil II, (1.1.3), p. 150 and (1.1.7), pp. 150--151,
for coefficient-limit and point-transport context; the conjugation and descent
argument is the agent-written DAG proof
(blueprint: lem-weil-point-rational-family-common-stage-naturality).

The helper definitions below are the canonical composites of the recorded
pullback and point-section comparisons. They are owned by this item, so the
downstream coefficient-descent proof can import it without a module cycle.

## Main declarations

* `RationalFamily`, `RationalCompatible`: the supplied rational family and scalar equation.
* `rationalB`, `stageB`: the prescribed comparison composites.
* `componentAt`, `fibreArrow`, `pullbackArrow`: the finite-stage components and actions.
* `CommonNormalized`: the prescribed descended components.
* `rationalFamilyNaturalityLeft`, `rationalFamilyNaturalityRight`: the two composites.
* `rational_family_common_stage_naturality`: naturality, transport and descent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

namespace WeilConjectures.PointRationalFamily

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (g : Spec (.of D.k) ⟶ Spec (.of D.k))

/-- The same recorded pullback on raw rational Hom tensors.
Source: Weil II (1.1.3) and the normalized derived operations
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def rationalPullback (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  rationalDerivedPullback l E g

/-- The recorded pullback on the literal common-stage pair category.
Source: Weil II (1.1.3), (1.1.7)
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def commonPullback :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  commonStageDerivedPullback l Ω g

/-- Its literal object formula, used to specify representative endpoints.
Source: Weil II (1.1.3), (1.1.7)
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def pullbackObject (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  commonStagePullbackObject l Ω g A

variable (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)

/-- The rational comparison b = phi at P(K) after F(alpha inverse).
Source: normalized scalar comparison in the DAG, rational paragraph
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def rationalB (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  (pointRationalFibre D l hl L).mapIso
      ((rationalPullbackScalarComparison l E L ι g).app K).symm ≪≫
    (pointRationalFibreScalarIso D l hl E L ι).app
      ((rationalPullback D l hl g E).obj K)

/-- A rational family is natural for every arrow in the raw scalar localization.
Source: the rational-family hypothesis of the DAG
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def RationalFamily :=
  ∀ F : Index l Ω,
    pointRationalFibre D l hl (Coefficient.{u} l Ω F) ⟶
      rationalPullback D l hl g (Coefficient.{u} l Ω F) ⋙
        pointRationalFibre D l hl (Coefficient.{u} l Ω F)

/-- Rational scalar compatibility, using exactly the rationalizations of alpha and phi.
Source: the displayed rational scalar-compatibility equation of the DAG
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def RationalCompatible (t : RationalFamily D l hl Ω g) : Prop :=
  ∀ (F G : Index l Ω) (h : F ≤ G)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    (t G).app ((sfRationalScalarExtension l (Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω G)
        (coefficientInclusion l Ω F G h)).obj K) ≫
      (rationalB D l hl g _ _ (coefficientInclusion l Ω F G h) K).hom =
    (pointRationalFibreScalarIso D l hl _ _ (coefficientInclusion l Ω F G h)).hom.app K ≫
      (DerivedCategory.pointFdScalarExtension (coefficientInclusion l Ω F G h).toRingHom).map
        ((t F).app K)

/-- The normalized pullback comparison at an arbitrary common stage, including its
specified transition identifications. Source: the DAG common-stage action hypotheses
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def pullbackComparison
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (h : A.stage ≤ N) :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  commonStagePullbackComparison l Ω g A N h

/-- The comparison b on the actual coefficient-field stage models.
Source: the displayed b and common-stage action formulas in the DAG
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def stageB
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (h : A.stage ≤ N) :=
  (pointStageFibre D l hl Ω N).mapIso (pullbackComparison D l hl Ω g A N h).symm ≪≫
    (pointStageFibreScalarIso D l hl Ω A.stage N h).app
      (pullbackObject D l hl Ω g A).obj

/-- The component at the coefficient field of a literal pair, transported by the
recorded Shrink algebra equivalence. Source: the DAG finite-stage component prescription
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def stageComponent (t : RationalFamily D l hl Ω g)
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :=
  (DerivedCategory.pointFdScalarExtension
    (Shrink.algEquiv ℚ_[l] A.stage.val).toRingHom).map ((t A.stage).app A.obj)

/-- Extend that component to the very same field as a supplied representative.
Source: the DAG prescription of t^L at (E,K)
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def componentAt (t : RationalFamily D l hl Ω g)
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (N : Index l Ω) (h : A.stage ≤ N) :=
  (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion h).toRingHom).map
    (stageComponent D l hl Ω g t A)

variable
  (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
  (N : Index l Ω) (hA : A.stage ≤ N) (hB : B.stage ≤ N)
  (f : A.toStage hA ⟶ B.toStage hB)

/-- A_L(u) = phi_target F_L(u) phi_source inverse.
Source: the first common-stage action formula in the DAG
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def fibreArrow :=
  (pointStageFibreScalarIso D l hl Ω A.stage N hA).inv.app A.obj ≫
    (pointStageFibre D l hl Ω N).map f ≫
    (pointStageFibreScalarIso D l hl Ω B.stage N hB).hom.app B.obj

/-- B_L(u) = b_target H_L(u) b_source inverse.
Source: the second common-stage action formula in the DAG
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def pullbackArrow :=
  (stageB D l hl Ω g A N hA).inv ≫
    (pointStageFibre D l hl Ω N).map
      ((rationalPullback D l hl g (Coefficient.{u} l Ω N)).map f) ≫
    (stageB D l hl Ω g B N hB).hom

/-- The usual finite-stage class in the recorded point-category cocone.
Source: common-stage realization in the DAG and def-weil-point-fd-qlbar-category
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def pointClass (X Y : DerivedCategory.PointFdQbar l Ω)
    (M : Index l Ω) (hX : X.1 ≤ M) (hY : Y.1 ≤ M)
    (v : (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hX).toRingHom).obj X.2 ⟶
      (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hY).toRingHom).obj Y.2) : X ⟶ Y :=
  (DerivedCategory.pointFdQbarStageComp l Ω hX).inv.app X.2 ≫
    (DerivedCategory.pointFdQbarStage l Ω M).map v ≫
    (DerivedCategory.pointFdQbarStageComp l Ω hY).hom.app Y.2

/-- The finite-stage class of the prescribed first action formula.
Source: the DAG common-stage action hypotheses
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def fibreClass :=
  pointClass l Ω (pointQbarFibreObj D l hl Ω A) (pointQbarFibreObj D l hl Ω B)
    N hA hB (fibreArrow D l hl Ω A B N hA hB f)

/-- The finite-stage class of the prescribed composite action formula.
Source: the DAG common-stage action hypotheses
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def pullbackClass :=
  pointClass l Ω (pointQbarFibreObj D l hl Ω (pullbackObject D l hl Ω g A))
    (pointQbarFibreObj D l hl Ω (pullbackObject D l hl Ω g B))
    N hA hB (pullbackArrow D l hl Ω g A B N hA hB f)

/-- Extend a point-category representative using exactly its specified tensor towers.
Source: def-weil-point-fd-qlbar-category and the DAG scalar-transport paragraph
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def pointTransport (X Y : DerivedCategory.PointFdQbar l Ω)
    (N M : Index l Ω) (hX : X.1 ≤ N) (hY : Y.1 ≤ N) (h : N ≤ M)
    (v : (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hX).toRingHom).obj X.2 ⟶
      (DerivedCategory.pointFdScalarExtension
        (IntermediateField.inclusion hY).toRingHom).obj Y.2) :=
  (pointFibreFdTensorTower (IntermediateField.inclusion hX).toRingHom
      (IntermediateField.inclusion h).toRingHom).inv.app X.2 ≫
    (DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion h).toRingHom).map v ≫
    (pointFibreFdTensorTower (IntermediateField.inclusion hY).toRingHom
      (IntermediateField.inclusion h).toRingHom).hom.app Y.2

/-- The common-stage components are exactly the classes of the rational components.
HEq inserts only the object equalities in the defining specifications of the two
recorded functors. Source: the DAG final paragraph and proof step 4
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def CommonNormalized (t : RationalFamily D l hl Ω g)
    (τ : pointQbarFibre D l hl Ω ⟶ commonPullback D l hl Ω g ⋙ pointQbarFibre D l hl Ω) :
    Prop :=
  ∀ A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)),
    HEq (τ.app A)
      ((DerivedCategory.pointFdQbarStage l Ω A.stage).map (stageComponent D l hl Ω g t A))

/-- The left side A_L(u) followed by t at the target, with Lean's composition order.
Source: DAG displayed same-stage equation, Weil II (1.1.3) context
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def rationalFamilyNaturalityLeft (t : RationalFamily D l hl Ω g)
    (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (L : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : A.toStage hA ⟶ B.toStage hB) :=
  fibreArrow D l hl Ω A B L hA hB f ≫ componentAt D l hl Ω g t B L hB

/-- The right side t at the source followed by B_L(u), in Lean's composition order.
Source: DAG displayed same-stage equation, Weil II (1.1.3) context
(blueprint: lem-weil-point-rational-family-common-stage-naturality). -/
def rationalFamilyNaturalityRight (t : RationalFamily D l hl Ω g)
    (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (L : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    (f : A.toStage hA ⟶ B.toStage hB) :=
  componentAt D l hl Ω g t A L hA ≫ pullbackArrow D l hl Ω g A B L hA hB f

/-- Scalar-compatible rational point families are natural at the original common field,
remain so after scalar transport, and descend independently of representatives.

Source: Deligne, Weil II, (1.1.3), p. 150; (1.1.7), pp. 150--151 supplies only
point-transport context. The proof below is the agent-written normalized argument
(blueprint: lem-weil-point-rational-family-common-stage-naturality).

Proof:
1. Fix the actual representative f over L. RationalCompatible rewrites the extended
components as b t_L phi inverse. Naturality of the supplied natural transformation t_L
at f gives H_L(f) t_X = t_Y F_L(f). Substitute in the two conjugated action formulas;
cancel only the comparison isomorphisms. This gives the equality in D(L), without
inverting any component of t.
2. Apply the point scalar functor to this equality and conjugate with the prescribed
tensor associators. Naturality of the associators at t identifies the transported
components, and the assumed action transport identifies the other two factors.
Thus both transported sides are precisely the sides at N, also for N=L by the units.
Uses def-weil-point-fd-qlbar-category.
3. Equality of source classes gives a common finite N with equal source transports,
by def-weil-algebraically-closed-coefficients. At N the two left sides and the two
right sides are identical. Use only forward passage to target classes; injectivity
of coefficient transitions is unnecessary. Uses def-weil-point-fd-qlbar-category.
4. At (E,K) take the class of t_E,K, using the specified units. The tower and unit
identifications identify its representative at L with T_L/E(t_E,K). Composition is
computed at a common stage, so step 1 is exactly its naturality square. Step 3 makes
this independent of representatives, giving the required natural transformation.
Uses def-weil-point-fd-qlbar-category. No integral lift is used. -/
theorem rational_family_common_stage_naturality [IsIso g]
    (t : RationalFamily D l hl Ω g) (ht : RationalCompatible D l hl Ω g t)
    (hunit : ∀ (E : Index l Ω)
      (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) (Spec (.of D.k))),
      HEq
        ((rationalB D l hl g _ _ (AlgHom.id ℚ_[l] (Coefficient.{u} l Ω E)) K).hom.hom ≫
          (DerivedCategory.fieldScalarUnit (Coefficient.{u} l Ω E)).hom.app _)
        ((pointRationalFibre D l hl (Coefficient.{u} l Ω E)).map
          ((rationalPullback D l hl g (Coefficient.{u} l Ω E)).map
            ((sfRationalScalarUnit l (Coefficient.{u} l Ω E) (Spec (.of D.k)) 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app K))).hom)
    (htower : ∀ (E L N : Index l Ω) (h : E ≤ L) (k : L ≤ N)
      (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) (Spec (.of D.k))),
      HEq
        ((pointRationalFibre D l hl (Coefficient.{u} l Ω N)).map
          ((rationalPullback D l hl g (Coefficient.{u} l Ω N)).map
            ((sfRationalScalarComp l _ _ (coefficientInclusion l Ω E L h)
              (Spec (.of D.k)) 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
              _ (coefficientInclusion l Ω L N k)).hom.app K)) ≫
          (rationalB D l hl g _ _
            ((coefficientInclusion l Ω L N k).comp (coefficientInclusion l Ω E L h)) K).hom)
        ((rationalB D l hl g _ _ (coefficientInclusion l Ω L N k)
          ((sfRationalScalarExtension l _ (Spec (.of D.k)) 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) _
            (coefficientInclusion l Ω E L h)).obj K)).hom ≫
          (DerivedCategory.pointFdScalarExtension
            (coefficientInclusion l Ω L N k).toRingHom).map
              (rationalB D l hl g _ _ (coefficientInclusion l Ω E L h) K).hom ≫
          (pointFibreFdTensorTower (coefficientInclusion l Ω E L h).toRingHom
            (coefficientInclusion l Ω L N k).toRingHom).hom.app _))
    (hactions : ∀
      (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
      (L : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (f : A.toStage hA ⟶ B.toStage hB),
      HEq ((pointQbarFibre D l hl Ω).map (StageSystem.PairCategory.mkHom L hA hB f))
        (fibreClass D l hl Ω A B L hA hB f) ∧
      HEq ((commonPullback D l hl Ω g ⋙ pointQbarFibre D l hl Ω).map
        (StageSystem.PairCategory.mkHom L hA hB f))
        (pullbackClass D l hl Ω g A B L hA hB f) ∧
      ∀ (N : Index l Ω) (h : L ≤ N),
        HEq (pointTransport l Ω (pointQbarFibreObj D l hl Ω A)
          (pointQbarFibreObj D l hl Ω B) L N hA hB h
          (fibreArrow D l hl Ω A B L hA hB f))
          (fibreArrow D l hl Ω A B N (hA.trans h) (hB.trans h)
            ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
              (Spec (.of D.k))).tr h f)) ∧
        HEq (pointTransport l Ω
          (pointQbarFibreObj D l hl Ω (pullbackObject D l hl Ω g A))
          (pointQbarFibreObj D l hl Ω (pullbackObject D l hl Ω g B)) L N hA hB h
          (pullbackArrow D l hl Ω g A B L hA hB f))
          (pullbackArrow D l hl Ω g A B N (hA.trans h) (hB.trans h)
            ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
              (Spec (.of D.k))).tr h f))) :
    (∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
      (L : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (f : A.toStage hA ⟶ B.toStage hB),
      rationalFamilyNaturalityLeft D l hl Ω g t A B L hA hB f =
        rationalFamilyNaturalityRight D l hl Ω g t A B L hA hB f ∧
      ∀ (N : Index l Ω) (h : L ≤ N),
        pointTransport l Ω (pointQbarFibreObj D l hl Ω A)
          (pointQbarFibreObj D l hl Ω (pullbackObject D l hl Ω g B)) L N hA hB h
          (rationalFamilyNaturalityLeft D l hl Ω g t A B L hA hB f) =
        rationalFamilyNaturalityLeft D l hl Ω g t A B N (hA.trans h) (hB.trans h)
          ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).tr h f) ∧
        pointTransport l Ω (pointQbarFibreObj D l hl Ω A)
          (pointQbarFibreObj D l hl Ω (pullbackObject D l hl Ω g B)) L N hA hB h
          (rationalFamilyNaturalityRight D l hl Ω g t A B L hA hB f) =
        rationalFamilyNaturalityRight D l hl Ω g t A B N (hA.trans h) (hB.trans h)
          ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω (Spec (.of D.k))).tr h f)) ∧
    (∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
      (L M : Index l Ω) (hA : A.stage ≤ L) (hB : B.stage ≤ L)
      (hA' : A.stage ≤ M) (hB' : B.stage ≤ M)
      (f : A.toStage hA ⟶ B.toStage hB) (v : A.toStage hA' ⟶ B.toStage hB'),
      StageSystem.PairCategory.mkHom L hA hB f =
        StageSystem.PairCategory.mkHom M hA' hB' v →
      ∃ (N : Index l Ω) (hL : L ≤ N) (hM : M ≤ N),
        HEq ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
          (Spec (.of D.k))).tr hL f)
          ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
            (Spec (.of D.k))).tr hM v) ∧
        HEq
          (rationalFamilyNaturalityLeft D l hl Ω g t A B N (hA.trans hL) (hB.trans hL)
            ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
              (Spec (.of D.k))).tr hL f))
          (rationalFamilyNaturalityLeft D l hl Ω g t A B N (hA'.trans hM) (hB'.trans hM)
            ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
              (Spec (.of D.k))).tr hM v)) ∧
        HEq
          (rationalFamilyNaturalityRight D l hl Ω g t A B N (hA.trans hL) (hB.trans hL)
            ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
              (Spec (.of D.k))).tr hL f))
          (rationalFamilyNaturalityRight D l hl Ω g t A B N (hA'.trans hM) (hB'.trans hM)
            ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω
              (Spec (.of D.k))).tr hM v))) ∧
    ∃ τ : pointQbarFibre D l hl Ω ⟶ commonPullback D l hl Ω g ⋙ pointQbarFibre D l hl Ω,
      CommonNormalized D l hl Ω g t τ := by
  sorry

end WeilConjectures.PointRationalFamily
