/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.AlgebraicGeometry.SpCondensedIntegralAdjunction.IntegralAdjunctionBijectionStatement
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.AlgebraicGeometry.ReductionExceptionalStatement
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Strict coefficient-extension constructions independent of the geometric base

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-setup/sec-the-purity-statement/sk-thm-purity-transport/
sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.md and .proof.md (2).
(blueprint: det-sp-field-extension-towers).
These are the sequence-site presentations of the existing strict coefficient towers.
The old presentation required an algebraic closure of a finite geometric field;
no such assumption is used in these coefficient constructions. The coefficient
closure is kept fixed, and its finite subfields and their inclusions are literal.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u a b a' b' vA vB vA' vB'
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale.NativeFieldTower
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Finite fields in the fixed coefficient closure, with their actual inclusions.
Source: blueprint (2), E subset F (blueprint: det-sp-field-extension-towers). -/
abbrev Index := Padic.FiniteCoefficientFields l Ω

/-- Canonical quotient and whole-ring-system maps, fixed on every residue class.
Source: blueprint (2), coefficient square
(blueprint: det-sp-field-extension-towers). -/
structure Coefficients (E F : Index l Ω) (h : E ≤ F) where
  quotient : ∀ n : ℕ,
    SpTowerShriek.R l E.val n →+* SpTowerShriek.R l F.val n
  quotient_mk : ∀ (n : ℕ) (x : Padic.coefficientExtensionIntegers l E.val),
    quotient n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _
      (integralScalarIntegerInclusion l E.val F.val
        (IntermediateField.inclusion h) x)
  tower : ∀ T : Scheme.{u},
    spCoefficientCommRings l E.val T ⟶
      spCoefficientCommRings l F.val T
  tower_app : ∀ (T : Scheme.{u}) (n : ℕ), (tower T).app (op n) =
    (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom ((ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).symm.toRingHom.comp
        ((quotient n).comp (ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).toRingHom)))

/-- The actual coefficient morphism on the entire sequence site.
Source: blueprint (2), simultaneous models
(blueprint: det-sp-field-extension-towers). -/
def coefficientMap {E F : Index l Ω} {h : E ≤ F} (a : Coefficients l Ω E F h)
    (T : Scheme.{u}) :=
  SemilinearSections.systemMap (Scheme.ProEt.topology T)
    (SpTowerShriek.B l E.val T) (SpTowerShriek.tau l E.val T)
    (SpTowerShriek.B l F.val T) (SpTowerShriek.tau l F.val T)
    (fun n ↦ (a.tower T).app (op n))
    (fun n ↦ ((a.tower T).naturality (homOfLE (Nat.le_succ n)).op).symm)

/-- Scalar extension is the dependency's universal K-flat normalized scalar extension.
Source: blueprint (2), C_T (blueprint: det-sp-field-extension-towers). -/
abbrev Scalars {E F : Index l Ω} {h : E ≤ F} (a : Coefficients l Ω E F h) (T : Scheme.{u}) :=
  SemilinearSections.ScalarData (coefficientMap l Ω a T)

/-- Normalize the geometric/scalar pullback square before localization. The pushforward
restriction square is literally the identity on sections, and the pullback square is
its double adjunction mate. The derived square has its cochain normalization, so a
transformation invisible to evaluations cannot be added.
Source: blueprint (2), lambda_a on simultaneous models
(blueprint: det-sp-field-extension-towers). -/
structure PullComparison {E F : Index l Ω} {h : E ≤ F}
    (a : Coefficients l Ω E F h) (bE : SpTowerShriek.Base l E.val)
    (bF : SpTowerShriek.Base l F.val)
    (oE : SpTowerShriek.Operations l E.val bE)
    (oF : SpTowerShriek.Operations l F.val bF)
    (s : ∀ T : Scheme.{u}, Scalars l Ω a T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) where
  restrictionPush : SemilinearSections.res (coefficientMap l Ω a X) ⋙ (oE.geometry f).push ≅
    (oF.geometry f).push ⋙ SemilinearSections.res (coefficientMap l Ω a Y)
  sections : ∀ (M : SpTowerShriek.S l F.val X)
    (U : (ℕ × Y.ProEt)ᵒᵖ)
    (x : ((SemilinearSections.res (coefficientMap l Ω a X) ⋙
      (oE.geometry f).push).obj M).val.obj U),
    HEq (((restrictionPush.hom.app M).val.app U) x) x
  ordinary : (s Y).model.E ⋙ (oF.geometry f).pull ≅
    (oE.geometry f).pull ⋙ (s X).model.E
  ordinary_mate :
    (mateEquiv (s Y).ordinaryAdjunction (s X).ordinaryAdjunction ordinary.inv).natTrans =
      ((mateEquiv (oF.geometry f).ordinaryAdjunction
        (oE.geometry f).ordinaryAdjunction).symm restrictionPush.inv).natTrans
  derived : (s Y).T ⋙ SpTowerShriek.pull l F.val bF (oF.geometry f) ≅
    SpTowerShriek.pull l E.val bE (oE.geometry f) ⋙ (s X).T
  representative : ∀ (K : CochainComplex (SpTowerShriek.S l E.val Y) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients
      (R := SemilinearSections.systemRing (Scheme.ProEt.topology Y)
        (SpTowerShriek.B l E.val Y)
        (SpTowerShriek.tau l E.val Y)) K →
    derived.hom.app (DerivedCategory.Q.obj K) ≫
        (s X).T.map ((oE.geometry f).pull.mapDerivedCategoryFactors.hom.app K) ≫
        (s X).model.ε.app (((oE.geometry f).pull.mapHomologicalComplex (.up ℤ)).obj K) =
      (SpTowerShriek.pull l F.val bF (oF.geometry f)).map
          ((s Y).model.ε.app K) ≫
        (oF.geometry f).pull.mapDerivedCategoryFactors.hom.app
          (((s Y).model.E.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app K)

/-- All coefficient and operation presentations needed to construct b. Every datum is
normalized by the recorded universal constructions, not an arbitrary natural map.
Source: blueprint (2), proper/open construction
(blueprint: det-sp-field-extension-towers). -/
structure Models where
  base : ∀ E : Index l Ω, SpTowerShriek.Base l E.val
  operations : ∀ E : Index l Ω, SpTowerShriek.Operations l E.val (base E)
  coordinates : ∀ E : Index l Ω, SpTowerCalculus.Coordinates l E.val (base E)
  coefficients : ∀ (E F : Index l Ω) (h : E ≤ F), Coefficients l Ω E F h
  scalars : ∀ (E F : Index l Ω) (h : E ≤ F) (T : Scheme.{u}),
    Scalars l Ω (coefficients E F h) T
  pull : ∀ (E F : Index l Ω) (h : E ≤ F) {X Y : Scheme.{u}} (f : X ⟶ Y),
    PullComparison l Ω (coefficients E F h) (base E) (base F)
      (operations E) (operations F) (scalars E F h) f
  openIso : ∀ (E F : Index l Ω) (h : E ≤ F) {X Z : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j],
    SpTowerShriek.openD l E.val (base E) ((operations E).openOp j) ⋙
        (scalars E F h Z).T ≅
      (scalars E F h X).T ⋙
        SpTowerShriek.openD l F.val (base F) ((operations F).openOp j)
  open_unit : ∀ (E F : Index l Ω) (h : E ≤ F) {X Z : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j],
    (openIso E F h j).inv =
      ((mateEquiv ((operations E).openOp j).derivedAdjunction
        ((operations F).openOp j).derivedAdjunction).symm (pull E F h j).derived.inv).natTrans

/-- The proper coefficient comparison is the actual geometric counit mate.
Source: blueprint (2), a_h (blueprint: det-sp-field-extension-towers). -/
def proper (D : Models l Ω) {E F : Index l Ω} (h : E ≤ F)
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) :=
  (mateEquiv
    (SpTowerShriek.adjunction l E.val (D.base E) ((D.operations E).geometry g))
    (SpTowerShriek.adjunction l F.val (D.base F) ((D.operations F).geometry g))
    (D.pull E F h g).derived.hom).natTrans

/-- The specified whole-system b: proper counit mate, followed by proper image of
open tensor identification. The same compactification occurs on both sides.
Source: blueprint (2), b_a = Q_B(e_a) a_h J_A
(blueprint: det-sp-field-extension-towers). -/
def comparison (D : Models l Ω) {E F : Index l Ω} (h : E ≤ F)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    SpTowerShriek.F l E.val (D.base E) (D.operations E) c ⋙
        (D.scalars E F h Y).T ⟶
      (D.scalars E F h X).T ⋙
        SpTowerShriek.F l F.val (D.base F) (D.operations F) c :=
  Functor.whiskerLeft
      (SpTowerShriek.openD l E.val (D.base E) ((D.operations E).openOp c.i))
      (proper l Ω D h c.g) ≫
    Functor.whiskerRight (D.openIso E F h c.i).hom
      (SpTowerShriek.push l F.val (D.base F) ((D.operations F).geometry c.g))

/-- The recorded normalized constructible predicate, in the section-preserving
sequence-site coordinates. Uniform cohomological and Tor bounds are retained.
Source: blueprint (2), N_A (blueprint: det-sp-field-extension-towers). -/
def normalized (D : Models l Ω) (E : Index l Ω) (T : Scheme.{u}) :
    ObjectProperty (SpTowerShriek.D l E.val T) :=
  fun K ↦ spNormalizedConstructibleTorTowers l E.val T
    ((D.coordinates E).abelian T)
    ((SpTowerCalculus.realization l E.val (D.base E) T
      ((D.coordinates E).abelian T)).inverse.obj K)


/-- Exact evaluation of coefficient restriction, fixed on all section carriers.
Source: blueprint (2), evaluation of simultaneous scalar models
(blueprint: det-sp-field-extension-towers). -/
structure RestrictionEvaluation (D : Models l Ω) {E F : Index l Ω} (h : E ≤ F)
    (T : Scheme.{u}) (n : ℕ) where
  ordinary : SemilinearSections.res (coefficientMap l Ω (D.coefficients E F h) T) ⋙
      SpTowerShriek.ev l E.val T n ≅
    SpTowerShriek.ev l F.val T n ⋙
      proEtaleRingRestrictScalars
        (proEtaleConstantRingMap (T := T) ((D.coefficients E F h).quotient n))
  sections : ∀ (M : SpTowerShriek.S l F.val T) (U : T.ProEtᵒᵖ)
    (x : ((SemilinearSections.res (coefficientMap l Ω (D.coefficients E F h) T) ⋙
      SpTowerShriek.ev l E.val T n).obj M).val.obj U),
    HEq (((ordinary.hom.app M).val.app U) x) x

/-- Exact localization of the uniquely section-normalized restriction comparison.
Source: blueprint (2), simultaneous evaluation
(blueprint: det-sp-field-extension-towers). -/
def restrictionEvaluation (D : Models l Ω) {E F : Index l Ω} (h : E ≤ F)
    (T : Scheme.{u}) (n : ℕ) (r : RestrictionEvaluation l Ω D h T n) :
    SemilinearSections.resD (coefficientMap l Ω (D.coefficients E F h) T) ⋙
        SpTowerShriek.Ev l E.val T n ≅
      SpTowerShriek.Ev l F.val T n ⋙
        scalarRestriction ((D.coefficients E F h).quotient n) T :=
  Functor.mapDerivedCategorySquareIso r.ordinary

attribute [local irreducible] restrictionEvaluation

/-- Evaluation compatibility of two actual adjunctions is equality of the right mate
with the given restriction square. This is the adjunction-transpose equation, before
any claim of conservativity. Source: blueprint (2), scalar evaluation normalization
(blueprint: det-sp-field-extension-towers). -/
@[irreducible] def AdjunctionEvaluationNormalized
    {A : Type a} {B : Type b} {A' : Type a'} {B' : Type b'}
    [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
    {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
    {U : A ⥤ A'} {V : B ⥤ B'} (adj : L ⊣ R) (adj' : L' ⊣ R')
    (left : L ⋙ V ≅ U ⋙ L') (right : R ⋙ U ≅ V ⋙ R') : Prop :=
  (mateEquiv adj adj' left.inv).natTrans = right.hom

/-- The specified finite scalar adjunction with its functors made explicit.
Source: blueprint (2), finite scalar normalization
(blueprint: det-sp-field-extension-towers). -/
@[irreducible] def finiteScalarAdjunction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    scalarExtensionFunctor φ T ⊣ scalarRestriction φ T :=
  proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := T) φ)

/-- Derived scalar evaluation, normalized by the actual two scalar adjunctions.
The transpose equation fixes the comparison on all derived morphisms.
Source: blueprint (2), evaluation of C_T
(blueprint: det-sp-field-extension-towers). -/
structure ScalarEvaluation (D : Models l Ω) {E F : Index l Ω} (h : E ≤ F)
    (T : Scheme.{u}) (n : ℕ) where
  restriction : RestrictionEvaluation l Ω D h T n
  iso : (D.scalars E F h T).T ⋙ SpTowerShriek.Ev l F.val T n ≅
    SpTowerShriek.Ev l E.val T n ⋙
      scalarExtensionFunctor ((D.coefficients E F h).quotient n) T
  transpose : AdjunctionEvaluationNormalized (D.scalars E F h T).adjunction
    (finiteScalarAdjunction ((D.coefficients E F h).quotient n) T) iso
    (restrictionEvaluation l Ω D h T n restriction)


/-- Finite compact-support evaluation in the recorded direct-image coordinates.
The ordinary pushforward change is the identity on sections.
Source: blueprint (2), finite b (blueprint: det-sp-field-extension-towers). -/
structure FiniteCoordinates (E : Index l Ω)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) where
  push : proEtaleConstantRingPushforward (SpTowerShriek.R l E.val n) c.g ≅
    proEtaleRingModuleDirectImage c.g
      (proEtaleConstantRing Y (SpTowerShriek.R l E.val n))
      (proEtaleConstantRing c.Z (SpTowerShriek.R l E.val n))
      (proEtaleConstantRingComparison c.g (SpTowerShriek.R l E.val n))
  sections : ∀ (M : proEtaleRingModules c.Z
      (proEtaleConstantRing c.Z (SpTowerShriek.R l E.val n)))
    (U : Y.ProEtᵒᵖ)
    (x : ((proEtaleConstantRingPushforward
      (SpTowerShriek.R l E.val n) c.g).obj M).val.obj U),
    HEq (((push.hom.app M).val.app U) x) x

/-- Finite support comparison, using the specified termwise open comparison and
right-derived section-identity proper comparison.
Source: blueprint (2), finite support evaluation
(blueprint: det-sp-field-extension-towers). -/
def supportEvaluation (D : Models l Ω) (E : Index l Ω)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ)
    (z : FiniteCoordinates l Ω E c n) :
    SpTowerShriek.F l E.val (D.base E) (D.operations E) c ⋙
        SpTowerShriek.Ev l E.val Y n ≅
      SpTowerShriek.Ev l E.val X n ⋙
        reductionCompactSupport (SpTowerShriek.R l E.val n) c.i c.g :=
  SpTowerShriek.Fcomparison l E.val (D.base E) (D.operations E) c n ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorNatIso z.push))


/-- Finite evaluation with its actual scalar and support coordinates.
Source: blueprint (2), specified finite b
(blueprint: det-sp-field-extension-towers). -/
structure EvaluationLaw (D : Models l Ω) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) where
  scalarEvaluation : ∀ (E F : Index l Ω) (h : E ≤ F) (T : Scheme.{u}) (n : ℕ),
    ScalarEvaluation l Ω D h T n
  supportCoordinates : ∀ (E : Index l Ω) (n : ℕ), FiniteCoordinates l Ω E c n
  evaluation : ∀ (E F : Index l Ω) (h : E ≤ F) (n : ℕ)
    (M : SpTowerShriek.D l E.val X),
    (SpTowerShriek.Ev l F.val Y n).map ((comparison l Ω D h c).app M) ≫
        (supportEvaluation l Ω D F c n (supportCoordinates F n)).hom.app
          ((D.scalars E F h X).T.obj M) ≫
        (reductionCompactSupport (SpTowerShriek.R l F.val n) c.i c.g).map
          ((scalarEvaluation E F h X n).iso.hom.app M) =
      (scalarEvaluation E F h Y n).iso.hom.app
          ((SpTowerShriek.F l E.val (D.base E) (D.operations E) c).obj M) ≫
        (scalarExtensionFunctor ((D.coefficients E F h).quotient n) Y).map
          ((supportEvaluation l Ω D E c n (supportCoordinates E n)).hom.app M) ≫
        (reductionDirectImageComparison ((D.coefficients E F h).quotient n) c.i c.g).app
          ((SpTowerShriek.Ev l E.val X n).obj M)



/-- Associativity of scalar extension on the sequence site, fixed by restriction
composition and the normalized adjunctions, hence by balanced tensor multiplication.
Source: blueprint (2), alpha_T (blueprint: det-sp-field-extension-towers). -/
def scalarAssoc (D : Models l Ω) {E F L : Index l Ω} (h : E ≤ F) (k : F ≤ L)
    (T : Scheme.{u})
    (hc : coefficientMap l Ω (D.coefficients E L (h.trans k)) T =
      coefficientMap l Ω (D.coefficients E F h) T ≫ coefficientMap l Ω (D.coefficients F L k) T) :
    (D.scalars E F h T).T ⋙ (D.scalars F L k T).T ≅ (D.scalars E L (h.trans k) T).T :=
  Adjunction.leftAdjointUniq
    (((D.scalars E F h T).adjunction.comp (D.scalars F L k T).adjunction).ofNatIsoRight
      (Functor.exactDerivedRestrictionComposition _ _ _
        (SheafOfModules.systemScalarRestrictionComposition.{u + 1, u, u + 1}
          (coefficientMap l Ω (D.coefficients E F h) T)
          (coefficientMap l Ω (D.coefficients F L k) T)
          (coefficientMap l Ω (D.coefficients E L (h.trans k)) T) hc)))
    (D.scalars E L (h.trans k) T).adjunction

/-- Identity scalar extension with its tensor unitor normalization.
Source: blueprint (2), identity coefficients
(blueprint: det-sp-field-extension-towers). -/
def scalarUnit (D : Models l Ω) (E : Index l Ω) (T : Scheme.{u})
    (hc : coefficientMap l Ω (D.coefficients E E le_rfl) T = 𝟙 _) :
    (D.scalars E E le_rfl T).T ≅ 𝟭 _ :=
  Adjunction.leftAdjointUniq
    ((D.scalars E E le_rfl T).adjunction.ofNatIsoRight
      (Functor.exactDerivedRestrictionUnit _
        (SheafOfModules.systemScalarRestrictionUnit.{u + 1, u, u + 1}
          (coefficientMap l Ω (D.coefficients E E le_rfl) T) hc))) Adjunction.id

attribute [local irreducible] scalarAssoc scalarUnit

/-- Composition and identity in the ordinary derived category of whole systems.
Source: blueprint (2), balanced coefficient cocycle
(blueprint: det-sp-field-extension-towers). -/
structure CoherenceLaw (D : Models l Ω) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) where
  coefficientComposition : ∀ (E F L : Index l Ω) (h : E ≤ F) (k : F ≤ L) (T : Scheme.{u}),
    coefficientMap l Ω (D.coefficients E L (h.trans k)) T =
      coefficientMap l Ω (D.coefficients E F h) T ≫ coefficientMap l Ω (D.coefficients F L k) T
  composition : ∀ (E F L : Index l Ω) (h : E ≤ F) (k : F ≤ L)
    (M : SpTowerShriek.D l E.val X), normalized l Ω D E X M →
    (D.scalars F L k Y).T.map ((comparison l Ω D h c).app M) ≫
        (comparison l Ω D k c).app ((D.scalars E F h X).T.obj M) ≫
        (SpTowerShriek.F l L.val (D.base L) (D.operations L) c).map
          ((scalarAssoc l Ω D h k X (coefficientComposition E F L h k X)).hom.app M) =
      (scalarAssoc l Ω D h k Y (coefficientComposition E F L h k Y)).hom.app
          ((SpTowerShriek.F l E.val (D.base E) (D.operations E) c).obj M) ≫
        (comparison l Ω D (h.trans k) c).app M
  coefficientIdentity : ∀ (E : Index l Ω) (T : Scheme.{u}),
    coefficientMap l Ω (D.coefficients E E le_rfl) T = 𝟙 _
  identity : ∀ (E : Index l Ω) (M : SpTowerShriek.D l E.val X),
    normalized l Ω D E X M →
    (comparison l Ω D (E := E) (F := E) le_rfl c).app M ≫
        (SpTowerShriek.F l E.val (D.base E) (D.operations E) c).map
          ((scalarUnit l Ω D E X (coefficientIdentity E X)).hom.app M) =
      (scalarUnit l Ω D E Y (coefficientIdentity E Y)).hom.app
        ((SpTowerShriek.F l E.val (D.base E) (D.operations E) c).obj M)



/-- The same total derived reduction/limit presentation as the integral adjunction.
Source: clause (2) (blueprint: det-sp-field-extension-towers). -/
abbrev IntegralModel.presentation (D : Models l Ω) (E : Index l Ω)
    {X Z Y : Scheme.{u}} {j : X ⟶ Z} [IsOpenImmersion j]
    {p : Z ⟶ Y} [IsProper p] [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    {d : ℕ} (m : IntegralModel l Ω D E j p d) :=
  SpCondensedIntegralAdjunction.presentation l E.val (D.base E) (D.operations E)
    (D.coordinates E) m.exchange m.laws

/-- The smooth right adjoint is precisely Rlim G red, with the recorded total limit.
Source: clause (2) (blueprint: det-sp-field-extension-towers). -/
abbrev integralExceptional (D : Models l Ω) (E : Index l Ω)
    {X Z Y : Scheme.{u}} {j : X ⟶ Z} [IsOpenImmersion j]
    {p : Z ⟶ Y} [IsProper p] [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    {d : ℕ} (m : IntegralModel l Ω D E j p d) :=
  SpCondensedIntegralAdjunction.right l E.val (IntegralModel.presentation l Ω D E m)
    m.realization.limitX m.realization.reductionY m.exceptional m.realization.closed

/-- The actual whole reduction functor on constructible inputs.
Source: clauses (1)--(2) (blueprint: det-sp-field-extension-towers). -/
abbrev integralReductionX (D : Models l Ω) (E : Index l Ω)
    {X Z Y : Scheme.{u}} {j : X ⟶ Z} [IsOpenImmersion j]
    {p : Z ⟶ Y} [IsProper p] [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    {d : ℕ} (m : IntegralModel l Ω D E j p d) :=
  SpCondensedIntegralAdjunction.reduce l E.val (IntegralModel.presentation l Ω D E m)
    X m.realization.reductionX

/-- The same actual whole reduction functor at Y.
Source: clauses (1)--(2) (blueprint: det-sp-field-extension-towers). -/
abbrev integralReductionY (D : Models l Ω) (E : Index l Ω)
    {X Z Y : Scheme.{u}} {j : X ⟶ Z} [IsOpenImmersion j]
    {p : Z ⟶ Y} [IsProper p] [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    {d : ℕ} (m : IntegralModel l Ω D E j p d) :=
  SpCondensedIntegralAdjunction.reduce l E.val (IntegralModel.presentation l Ω D E m)
    Y m.realization.reductionY


end AlgebraicGeometry.ProEtale.NativeFieldTower
