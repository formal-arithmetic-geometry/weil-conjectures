/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint
public import Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars
public import Sheaf.CategoryTheory.DerivedCoefficientSequenceRealization
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.Paper.ClosedSupportedScalarComparison
import Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus
import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Yoneda

/-! # Counit-normalized exceptional reduction and quotient transitions

Source: main-20261015, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-localization-all-stages.proof.md, Integral stage, returned step 7
(blueprint: lem-sf-exceptional-reduction-transition-comparison).

Natural numbers index exponents n+1. Adjunction presentations below specify the
ordinary completed and finite kernel right adjoints by their closed direct images.

## Main declarations

- `alphaOf`: the natural counit transpose of integral reduction.
- `t`: the canonical finite exceptional quotient transition.
- `exceptionalReductionTransitionComparison`: invertibility, characterization,
  open-unit normalization, and all transition, cocycle and identity equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.SfExceptionalReduction
open CategoryTheory.DerivedCoefficientSequence CategoryTheory.Pretriangulated

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual quotient A_m → A_n, sheafified on the original small site.
Source: Integral stage, quotient transitions
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def quotient (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    integralCoefficientCommRingSheaf l E T m ⟶ integralCoefficientCommRingSheaf l E T n :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (Ideal.Quotient.factor
      (S := Padic.coefficientExtensionIdeal l E (m + 1))
      (T := Padic.coefficientExtensionIdeal l E (n + 1))
      (Ideal.pow_le_pow_right (Nat.succ_le_succ h))).ulift)

/-- The limit projection and quotient identities, including equal indices.
Source: Integral stage, steps 1 and 7
(blueprint: lem-sf-exceptional-reduction-transition-comparison).
Proof: each quotient is induced by the identity on the valuation ring. Surjectivity
of the quotient map proves composition and identity by evaluation on lifts. The
inverse-limit cone condition then gives the projection equation for any two levels. -/
theorem quotient_laws (T : Scheme.{u}) :
    (∀ (m n : ℕ) (h : n ≤ m),
      completedIntegralCommRingProjectionUnrestricted l E T m ≫ quotient l E T h =
        completedIntegralCommRingProjectionUnrestricted l E T n) ∧
    (∀ (r m n : ℕ) (h : m ≤ r) (g : n ≤ m),
      quotient l E T h ≫ quotient l E T g = quotient l E T (g.trans h)) ∧
    (∀ n : ℕ, quotient l E T (le_refl n) = 𝟙 _) := by
  have hcomp (r m n : ℕ) (h : m ≤ r) (g : n ≤ m) :
      quotient l E T h ≫ quotient l E T g = quotient l E T (g.trans h) := by
    unfold quotient
    rw [← Functor.map_comp]
    congr 1
    ext x
    change Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ g))
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ h)) x.down) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ (g.trans h))) x.down
    exact Ideal.Quotient.factor_comp_apply _ _ x.down
  have hself (n : ℕ) : quotient l E T (le_refl n) = 𝟙 _ := by
    unfold quotient
    rw [Ideal.Quotient.factor_eq]
    exact (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_id _
  refine ⟨?_, hcomp, hself⟩
  intro m n h
  induction m, h using Nat.le_induction with
  | base => rw [hself, Category.comp_id]
  | succ m h ih =>
    rw [← hcomp (m + 1) m n (Nat.le_succ m) h, ← Category.assoc]
    have hs : completedIntegralCommRingProjectionUnrestricted l E T (m + 1) ≫
        quotient l E T (Nat.le_succ m) =
          completedIntegralCommRingProjectionUnrestricted l E T m := by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      apply (forget₂ CommRingCat RingCat).map_injective
      ext x
      have hw := congrArg (fun v ↦ (v.hom.app V).hom x)
        (limit.w (integralCoefficientSheafSystem l E T)
          (homOfLE (Nat.le_succ m)).op)
      simp only [integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ] at hw
      convert hw using 1 <;> rfl
    rw [hs]
    exact ih

/-- Finite scalar restriction retains the smaller coefficient action.
Source: Integral stage, steps 4--7
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
abbrev restrict (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    DerivedCategory (scalarReductionTarget.{u, u} l E T n) ⥤
      DerivedCategory (scalarReductionTarget.{u, u} l E T m) :=
  derivedRestriction.{u + 1, u, u + 1, u + 2} (quotient l E T h)

/-- Reduction is the already recorded universal derived scalar extension.
Source: Integral stage, K_n
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
abbrev reduce (T : Scheme.{u}) (n : ℕ) :=
  scalarReductionDerivedExtension.{u, u} l E T n

/-- The normalized restriction compositor induced by the identity on module sections.
Source: Integral stage, scalar restriction
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def projectionComparison (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :=
  comparison (completedIntegralCommRingProjectionUnrestricted l E T m)
    (quotient l E T h) (completedIntegralCommRingProjectionUnrestricted l E T n)
    ((quotient_laws l E T).1 m n h)

/-- The canonical quotient morphism is the scalar-adjunction transpose of the smaller
reduction unit. Thus it is not chosen from the Hom set without normalization.
Source: Integral stage, q_mn (blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def transition (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    reduce l E T m ⟶ reduce l E T n ⋙ restrict l E T h :=
  (((derivedScalarExtensionRestrictionAdjunction.{u, u} l E T m).choose.whiskerRight
      (DerivedCategory (scalarReductionSource.{u, u} l E T))).homEquiv
        (𝟭 _) (reduce l E T n ⋙ restrict l E T h)).symm
    ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E T n).choose.unit ≫
      Functor.whiskerLeft (reduce l E T n) (projectionComparison l E T h).inv ≫
      (Functor.associator _ _ _).inv)

/-- Direct-image reduction as the transpose of the reduction unit followed by the
recorded ordinary/completed restriction comparison. This fixes the canonical map.
Source: Integral stage, step 1
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def directReduction {V W : Scheme.{u}} (f : V ⟶ W) (n : ℕ) :
    sfCompletedDerivedDirectImage l E f ⋙ reduce l E W n ⟶
      reduce l E V n ⋙ proEtaleConstantDerivedDirectImage f
        (Padic.coefficientExtensionRing l E (n + 1)) :=
  (((derivedScalarExtensionRestrictionAdjunction.{u, u} l E W n).choose.whiskerRight
      (DerivedCategory (scalarReductionSource.{u, u} l E V))).homEquiv _ _).symm
    ((Functor.leftUnitor _).inv ≫
      Functor.whiskerRight
        (derivedScalarExtensionRestrictionAdjunction.{u, u} l E V n).choose.unit
        (sfCompletedDerivedDirectImage l E f) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (reduce l E V n) (sfDerivedRestrictionComparison l E f n).hom ≫
      (Functor.associator _ _ _).inv)

/-- Closed direct image at a positive finite level, on the ambient derived categories.
Source: Integral stage, I_n (blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
abbrev finiteImage {V W : Scheme.{u}} (f : V ⟶ W) (n : ℕ) :=
  proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1))

/-- The normalized finite closed scalar square, with the A_m-action retained.
Source: Integral stage, step 4
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def finiteImageRestriction {V W : Scheme.{u}} (f : V ⟶ W) {m n : ℕ} (h : n ≤ m) :
    restrict l E V h ⋙ finiteImage l E f m ≅
      finiteImage l E f n ⋙ restrict l E W h :=
  letI : Finite (Padic.coefficientExtensionRing l E (m + 1)) :=
    Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_pos m)
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  (proEtaleDerivedDirectImage_restrictScalars f
    (Ideal.Quotient.factor (S := Padic.coefficientExtensionIdeal l E (m + 1))
      (T := Padic.coefficientExtensionIdeal l E (n + 1))
      (Ideal.pow_le_pow_right (Nat.succ_le_succ h)))).choose

/-- The scalar-restriction right-adjoint mate, fixed by the actual closed counits.
Source: Integral stage, step 4, equation (**)
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def restrictionMate {X Z : Scheme.{u}} (i : Z ⟶ X)
    (J : ∀ n : ℕ, DerivedCategory (scalarReductionTarget.{u, u} l E X n) ⥤
      DerivedCategory (scalarReductionTarget.{u, u} l E Z n))
    (a : ∀ n : ℕ, finiteImage l E i n ⊣ J n)
    {m n : ℕ} (h : n ≤ m) :
    J n ⋙ restrict l E Z h ⟶ restrict l E X h ⋙ J m :=
  (mateEquiv (a n) (a m)
    (TwoSquare.mk _ _ _ _ (finiteImageRestriction l E i h).hom)).natTrans

/-- The exceptional quotient transition is J_m(q_mn) followed by its counit-normalized
restriction mate. Source: Integral stage, step 5
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def exceptionalTransition {X Z : Scheme.{u}} (i : Z ⟶ X)
    (J : ∀ n : ℕ, DerivedCategory (scalarReductionTarget.{u, u} l E X n) ⥤
      DerivedCategory (scalarReductionTarget.{u, u} l E Z n))
    (a : ∀ n : ℕ, finiteImage l E i n ⊣ J n)
    (hiso : ∀ (m n : ℕ) (h : n ≤ m), IsIso (restrictionMate l E i J a h))
    {m n : ℕ} (h : n ≤ m) :
    reduce l E X m ⋙ J m ⟶ (reduce l E X n ⋙ J n) ⋙ restrict l E Z h :=
  Functor.whiskerRight (transition l E X h) (J m) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (reduce l E X n)
      (@inv _ _ _ _ (restrictionMate l E i J a h) (hiso m n h)) ≫
    (Functor.associator _ _ _).inv


/-- The finite open pullback, in the canonical constant-coefficient presentation.
Source: Integral stage, step 1
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
abbrev finitePull {V W : Scheme.{u}} (f : V ⟶ W) (n : ℕ) :=
  finiteDerivedPullback l E n f

/-- The inverse pullback-reduction comparison, obtained from the actual direct-image
comparison by the inverse mates correspondence. Source: Integral stage, step 1
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def pullMate {X U : Scheme.{u}} (j : U ⟶ X)
    (P : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (scalarReductionSource.{u, u} l E U))
    (a : P ⊣ sfCompletedDerivedDirectImage l E j) (n : ℕ)
    (b : finitePull l E j n ⊣ finiteImage l E j n) :
    reduce l E X n ⋙ finitePull l E j n ⟶ P ⋙ reduce l E U n :=
  ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ (directReduction l E j n))).natTrans

/-- The integral constructible inclusion uses the recorded full subcategory.
Source: Integral stage, K in D^b_c(X,R)
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
abbrev inclusion (X : Scheme.{u}) := (sfIntegralConstructible l E X).ι

/-- The exceptional reduction arrow is the natural adjunction transpose of the
reduced integral counit. The inverse closed comparison is taken only on JR(K).
Source: Integral stage, step 2, equation (*)
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def alpha {X Z : Scheme.{u}} (i : Z ⟶ X)
    (JR : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (scalarReductionSource.{u, u} l E Z))
    (aR : sfCompletedDerivedDirectImage l E i ⊣ JR) (n : ℕ)
    (Jn : DerivedCategory (scalarReductionTarget.{u, u} l E X n) ⥤
      DerivedCategory (scalarReductionTarget.{u, u} l E Z n))
    (an : finiteImage l E i n ⊣ Jn)
    (hc : IsIso (Functor.whiskerLeft (inclusion l E X ⋙ JR) (directReduction l E i n))) :
    (inclusion l E X ⋙ JR) ⋙ reduce l E Z n ⟶ (inclusion l E X ⋙ reduce l E X n) ⋙ Jn :=
  ((an.whiskerRight (sfIntegralConstructibleCategory l E X)).homEquiv _ _)
    ((Functor.associator _ _ _).hom ≫
      @inv _ _ _ _ (Functor.whiskerLeft (inclusion l E X ⋙ JR)
        (directReduction l E i n)) hc ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        ((Functor.associator (inclusion l E X) JR (sfCompletedDerivedDirectImage l E i)).hom ≫
          Functor.whiskerLeft (inclusion l E X) aR.counit ≫
            (Functor.rightUnitor (inclusion l E X)).hom) (reduce l E X n))


/-- The restriction compositor through a third quotient level is the recorded
identity-on-sections compositor. Source: Integral stage, step 7
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def restrictComp (T : Scheme.{u}) {r m n : ℕ} (h : m ≤ r) (g : n ≤ m) :
    restrict l E T g ⋙ restrict l E T h ≅ restrict l E T (g.trans h) :=
  comparison (quotient l E T h) (quotient l E T g) (quotient l E T (g.trans h))
    ((quotient_laws l E T).2.1 r m n h g)

/-- Equal-index restriction is identified with the identity by its actual coefficient
map and termwise localization. Source: Integral stage, t_nn
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def restrictId (T : Scheme.{u}) (n : ℕ) : restrict l E T (le_refl n) ≅ 𝟭 _ :=
  eqToIso (congrArg (fun f ↦ derivedRestriction.{u + 1, u, u + 1, u + 2} f)
    ((quotient_laws l E T).2.2 n)) ≪≫ derivedIdentity.{u + 1, u, u + 1, u + 2} _

/-- A presentation of exactly the supported-triangle and operation-comparison hypotheses.
The ambient categories, reductions and direct images are the recorded constructions.
The two exceptional functors are specified as right adjoints of those actual images;
this determines them uniquely with their counits, including the kernel right adjoint.
Source: Integral stage, assumed constructible restrictions and ordinary comparisons
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
structure Presentation {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) where
  JR : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
    DerivedCategory (scalarReductionSource.{u, u} l E Z)
  Jn (n : ℕ) : DerivedCategory (scalarReductionTarget.{u, u} l E X n) ⥤
    DerivedCategory (scalarReductionTarget.{u, u} l E Z n)
  aR : sfCompletedDerivedDirectImage l E i ⊣ JR
  an (n : ℕ) : finiteImage l E i n ⊣ Jn n
  P : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
    DerivedCategory (scalarReductionSource.{u, u} l E U)
  aOpen : P ⊣ sfCompletedDerivedDirectImage l E j
  aFiniteOpen (n : ℕ) : finitePull l E j n ⊣ finiteImage l E j n
  preservesJR (K : sfIntegralConstructibleCategory l E X) : sfIntegralConstructible l E Z
    (JR.obj K.obj)
  preservesP (K : sfIntegralConstructibleCategory l E X) : sfIntegralConstructible l E U
    (P.obj K.obj)
  closedComparison (n : ℕ) :
    IsIso (Functor.whiskerLeft (inclusion l E X ⋙ JR) (directReduction l E i n))
  openComparison (n : ℕ) (K : sfIntegralConstructibleCategory l E U) :
    IsIso ((directReduction l E j n).app K.obj)
  pullComparison (n : ℕ) (K : sfIntegralConstructibleCategory l E X) :
    IsIso ((pullMate l E j P aOpen n (aFiniteOpen n)).app K.obj)
  preservesIntegralClosed (K : sfIntegralConstructibleCategory l E Z) :
    sfIntegralConstructible l E X ((sfCompletedDerivedDirectImage l E i).obj K.obj)
  preservesIntegralOpen (K : sfIntegralConstructibleCategory l E U) :
    sfIntegralConstructible l E X ((sfCompletedDerivedDirectImage l E j).obj K.obj)
  preservesFiniteClosed (n : ℕ)
      (K : DerivedCategory (scalarReductionTarget.{u, u} l E Z n))
      (hK : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z K) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X
      ((finiteImage l E i n).obj K)
  preservesFiniteOpen (n : ℕ)
      (K : DerivedCategory (scalarReductionTarget.{u, u} l E U n))
      (hK : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) U K) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X
      ((finiteImage l E j n).obj K)
  preservesFiniteExceptional (n : ℕ)
      (K : DerivedCategory (scalarReductionTarget.{u, u} l E X n))
      (hK : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X K) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z ((Jn n).obj K)
  preservesFinitePull (n : ℕ)
      (K : DerivedCategory (scalarReductionTarget.{u, u} l E X n))
      (hK : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X K) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) U
      ((finitePull l E j n).obj K)
  boundaryR (K : sfIntegralConstructibleCategory l E X) :
    (sfCompletedDerivedDirectImage l E j).obj (P.obj K.obj) ⟶
      ((sfCompletedDerivedDirectImage l E i).obj (JR.obj K.obj))⟦(1 : ℤ)⟧
  triangleR (K : sfIntegralConstructibleCategory l E X) :
    Triangle.mk (aR.counit.app K.obj) (aOpen.unit.app K.obj) (boundaryR K) ∈
      distTriang _
  boundaryN (n : ℕ) (K : DerivedCategory (scalarReductionTarget.{u, u} l E X n)) :
    (finiteImage l E j n).obj ((finitePull l E j n).obj K) ⟶
      ((finiteImage l E i n).obj ((Jn n).obj K))⟦(1 : ℤ)⟧
  triangleN (n : ℕ) (K : DerivedCategory (scalarReductionTarget.{u, u} l E X n))
      (hK : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X K) :
    Triangle.mk ((an n).counit.app K) ((aFiniteOpen n).unit.app K) (boundaryN n K) ∈
      distTriang _

variable {l E} {X Z U : Scheme.{u}} {i : Z ⟶ X} {j : U ⟶ X}
  (S : Presentation l E i j)

/-- The natural exceptional reduction fixed by the two actual counits.
Source: Integral stage, equation (*)
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def alphaOf (n : ℕ) :=
  alpha l E i S.JR S.aR n (S.Jn n) (S.an n) (S.closedComparison n)

/-- The open component formed from the canonical direct and inverse-image comparisons.
Source: Integral stage, open-unit normalization
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def openComponent (n : ℕ) (K : sfIntegralConstructibleCategory l E X) :=
  (directReduction l E j n).app (S.P.obj K.obj) ≫
    (finiteImage l E j n).map
      (@inv _ _ _ _ ((pullMate l E j S.P S.aOpen n (S.aFiniteOpen n)).app K.obj)
        (S.pullComparison n K))

/-- The closed component of the map of supported triangles, for any candidate arrow.
Source: Integral stage, step 3
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def closedComponent (n : ℕ) (K : sfIntegralConstructibleCategory l E X)
    (b : (reduce l E Z n).obj (S.JR.obj K.obj) ⟶
      (S.Jn n).obj ((reduce l E X n).obj K.obj)) :=
  (directReduction l E i n).app (S.JR.obj K.obj) ≫ (finiteImage l E i n).map b

/-- Exceptional right adjoints commute with finite scalar restriction; the displayed
mate is the inverse of d_mn, so d_mn carries precisely the counit normalization (**).
Source: Integral stage, step 4
(blueprint: lem-sf-exceptional-reduction-transition-comparison).
Proof: scalar extension is left adjoint to restriction. Compose its Hom bijections
with the two closed adjunctions and the normalized closed scalar comparison. Yoneda
identifies the right adjoints, giving this mate and its inverse. Evaluating the Hom
bijection on identity gives equation (**), so the isomorphism is counit-normalized. -/
theorem restrictionMate_isIso [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : IsCompl (Set.range i) (Set.range j)) (m n : ℕ) (h : n ≤ m) :
    IsIso (restrictionMate l E i S.Jn S.an h) := by
  sorry

/-- The transition in the finite exceptional tower, retaining the A_m action.
Source: Integral stage, t_mn
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def t [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : IsCompl (Set.range i) (Set.range j)) {m n : ℕ} (h : n ≤ m) :=
  exceptionalTransition l E i S.Jn S.an
    (fun a b g ↦ restrictionMate_isIso S hij a b g) h


/-- The canonical shift structure supplied with the universal derived reduction.
Source: scalar-extension exactness, Integral stage
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
@[instance_reducible]
def reductionShift (T : Scheme.{u}) (n : ℕ) : (reduce l E T n).CommShift ℤ :=
  (scalarReductionDerivedExistence.{u, u} l E T n).choose_spec.choose_spec.2.1.choose

/-- The actual integral supported triangle, before reduction.
Source: Integral stage, supported triangle
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def integralTriangle (K : sfIntegralConstructibleCategory l E X) :=
  Triangle.mk (S.aR.counit.app K.obj) (S.aOpen.unit.app K.obj) (S.boundaryR K)

/-- The actual finite supported triangle of the reduction of K.
Source: Integral stage, supported triangle
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def finiteTriangle (n : ℕ) (K : sfIntegralConstructibleCategory l E X) :=
  Triangle.mk ((S.an n).counit.app ((reduce l E X n).obj K.obj))
    ((S.aFiniteOpen n).unit.app ((reduce l E X n).obj K.obj))
    (S.boundaryN n ((reduce l E X n).obj K.obj))

/-- Reduction of all three arrows, including the canonical shift comparison.
Source: Integral stage, map of supported triangles
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def reducedTriangle (n : ℕ) (K : sfIntegralConstructibleCategory l E X) :=
  letI := reductionShift (l := l) (E := E) X n
  (reduce l E X n).mapTriangle.obj (integralTriangle S K)

/-- The exceptional counit equation for a candidate reduction arrow.
Source: Integral stage, equation (*)
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def PreservesCounit (n : ℕ) (K : sfIntegralConstructibleCategory l E X)
    (b : (reduce l E Z n).obj (S.JR.obj K.obj) ⟶
      (S.Jn n).obj ((reduce l E X n).obj K.obj)) : Prop :=
  closedComponent S n K b ≫ (S.an n).counit.app ((reduce l E X n).obj K.obj) =
    (reduce l E X n).map (S.aR.counit.app K.obj)

/-- The specified three components extend to a morphism of the actual triangles.
After the canonical comparisons the middle and open components are identities.
Source: Integral stage, equivalent triangle characterization
(blueprint: lem-sf-exceptional-reduction-transition-comparison). -/
def ExtendsTriangles (n : ℕ) (K : sfIntegralConstructibleCategory l E X)
    (b : (reduce l E Z n).obj (S.JR.obj K.obj) ⟶
      (S.Jn n).obj ((reduce l E X n).obj K.obj)) : Prop :=
  ∃ f : reducedTriangle S n K ⟶ finiteTriangle S n K,
    f.hom₁ = closedComponent S n K b ∧ f.hom₂ = 𝟙 _ ∧
      f.hom₃ = openComponent S n K

/-- Counit-normalized exceptional reduction, with quotient-linear tower coherence.
Source: main-20261015, prop-sf-localization-all-stages.proof.md, Integral stage,
returned step 7 (blueprint: lem-sf-exceptional-reduction-transition-comparison).

Proof: (1) The canonical direct-image and inverse-image scalar mates carry the
integral open unit to the finite unit, by their ordinary normalization and the
K-flat computation (lem-sfb-kflat-scalar-comparison-normalization).
(2) Transpose the reduced integral closed counit through the closed comparison;
this is alphaOf, and the adjunction bijection gives its counit equation and
uniqueness. (3) Apply TR3 to the supported triangles. The middle and open maps
are isomorphisms, so the closed map is one by lem-sf-triangle-morphism-iso.
Closed direct image is fully faithful, hence alpha is invertible. The same
adjunction injectivity gives the equivalent triangle characterization.
(4) Compose the scalar-extension/restriction and closed adjunction Hom bijections
with the closed scalar comparison (lem-sfb-closed-supported-scalar-comparison).
Yoneda gives the inverse of restrictionMate; evaluation on identity proves its
counit normalization. (5) Transposing the quotient composed with the finite
counit gives J_m(q); following by the inverse restriction mate gives t.
(6) Apply the injective closed adjunction Hom map to the two proposed composites.
Counit naturality and the two mate normalizations reduce both to reduction of
the same integral counit followed by the quotient. Thus the transition equality
holds as a natural transformation. (7) Apply the same injective Hom map at r
to the composite and direct transitions: both become q_rn times the counit,
since q_mn q_rm = q_rn. For equal indices the quotient is identity. The quotient
laws hold on K-flat complexes and descend with their coefficient actions by
lem-pur-derived-change-of-rings and lem-weil-integral-reduction-tower-well-defined;
the restriction compositors are those of lem-sf-derived-coefficient-sequence-realization.
No faithfulness of forgetting finite coefficients or boundedness after arbitrary
finite derived scalar extension is used. -/
theorem exceptionalReductionTransitionComparison
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : IsCompl (Set.range i) (Set.range j)) :
    (∀ n : ℕ, IsIso (alphaOf S n)) ∧
    (∀ (n : ℕ) (K : sfIntegralConstructibleCategory l E X),
      (reduce l E X n).map (S.aOpen.unit.app K.obj) ≫ openComponent S n K =
        (S.aFiniteOpen n).unit.app ((reduce l E X n).obj K.obj)) ∧
    (∀ (n : ℕ) (K : sfIntegralConstructibleCategory l E X),
      PreservesCounit S n K ((alphaOf S n).app K) ∧
      ∀ b : (reduce l E Z n).obj (S.JR.obj K.obj) ⟶
          (S.Jn n).obj ((reduce l E X n).obj K.obj),
        (PreservesCounit S n K b ↔ b = (alphaOf S n).app K) ∧
        (PreservesCounit S n K b ↔ ExtendsTriangles S n K b)) ∧
    (∀ (m n : ℕ) (h : n ≤ m) (K : sfIntegralConstructibleCategory l E X),
      (alphaOf S m).app K ≫ (t S hij h).app K.obj =
        (transition l E Z h).app (S.JR.obj K.obj) ≫
          (restrict l E Z h).map ((alphaOf S n).app K)) ∧
    (∀ (r m n : ℕ) (h : m ≤ r) (g : n ≤ m)
        (K : sfIntegralConstructibleCategory l E X),
      (t S hij h).app K.obj ≫ (restrict l E Z h).map ((t S hij g).app K.obj) ≫
        (restrictComp l E Z h g).hom.app
          ((S.Jn n).obj ((reduce l E X n).obj K.obj)) =
        (t S hij (g.trans h)).app K.obj) ∧
    (∀ (n : ℕ) (K : sfIntegralConstructibleCategory l E X),
      (t S hij (le_refl n)).app K.obj ≫ (restrictId l E Z n).hom.app
        ((S.Jn n).obj ((reduce l E X n).obj K.obj)) = 𝟙 _) := by
  sorry

end WeilConjectures.SfExceptionalReduction
