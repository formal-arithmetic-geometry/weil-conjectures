module

public import Sheaf.Paper.ProperSectionsSemilinearGerms
public import Sheaf.Paper.FrobeniusGeometricExchange
public import Sheaf.SixFunctors.FrobeniusPointTransportNatural
public import Sheaf.Paper.SfDerivedDirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
import Sheaf.Paper.BasicOperationsCoefficientReduction

/-! # Positive iteration and coefficient descent of the semilinear germ square

Source: Deligne, Weil II (1.1.3), (1.1.7), (1.1.10)--(1.1.14), pp. 150--153;
Stacks Project, Tag 0D6D, lemma-derived-pullback-composition
(blueprint: lem-a1-semilinear-germ-iteration-descent).

Positive exponents are indexed by n, meaning r = n + 1. The ordinary counit germ
and moving point are reused from their definition node. All comparisons below are
composites of the recorded pullback compositors, before coefficient descent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
namespace SemilinearGermIteration
open ProperSemilinearGerms FrobeniusExchange

variable (D : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of D.k₀))) [IsProper Y₀.hom]
  (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The elementary power and moving-point identities used to type the recurrences.
Source: Deligne (1.1.7), (1.1.10)
(blueprint: lem-a1-semilinear-germ-iteration-descent).
Proof: powers of one arrow commute. Iterate the second projection equation
of galoisMap_projections, also for inverse powers. Cancellation of h with its
inverse gives the square and the moving-point shift. Compose the projection
identity with h^(-r) x and use x a = id to obtain the k-point assertion. -/
theorem geometry
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ) :
    movingPoint D Y₀ x n ≫ (D.geometricFiber Y₀).hom = 𝟙 _ ∧
    localPositivePower (frobeniusPointIso D).hom n ≫ movingPoint D Y₀ x n =
      x ≫ localPositivePower (D.geometricFrobenius Y₀).hom n ∧
    movingPoint D Y₀ (movingPoint D Y₀ x 0) n = movingPoint D Y₀ x (n + 1) := by
  sorry

/-- Powers of one arrow may be multiplied on the left in the positive-power convention.
Source: Stacks 0D6D, compositor iteration
(blueprint: lem-a1-semilinear-germ-iteration-descent).
Proof: induction on n, using associativity in the successor step. -/
theorem positivePower_step {X : Scheme.{u}} (g : X ⟶ X) (n : ℕ) :
    g ≫ localPositivePower g n = localPositivePower g (n + 1) := by
  sorry

/-- S_r or J_r, with S_(r+1) = P S_r on objects and on arrows.
Source: the positive-iteration recurrence, Deligne (1.1.14)
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def pullbackPower {C : Type v} [Category.{w} C] (P : C ⥤ C) : ℕ → C ⥤ C
  | 0 => P
  | n + 1 => pullbackPower P n ⋙ P

/-- The specified d_r or f_r, formed recursively from the actual compositors.
Source: Stacks 0D6D, lemma-derived-pullback-composition
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def contraction {X : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)] (g : X ⟶ X) :
    (n : ℕ) → (M : sfIntegralConstructibleCategory l E X) →
      (constructibleIntegralPullback l E (localPositivePower g n)).obj M ≅
        (pullbackPower (constructibleIntegralPullback l E g) n).obj M
  | 0, _M => Iso.refl _
  | n + 1, M =>
    eqToIso (congrArg (fun f ↦ (constructibleIntegralPullback l E f).obj M)
      (positivePower_step g n).symm) ≪≫
      (((integralPullbackComposition l E).choose g (localPositivePower g n)).app M) ≪≫
      (constructibleIntegralPullback l E g).mapIso (contraction g n M)

/-- The comparison b_(r,x) for the actual square g^r x = x_r h^r.
Source: Stacks 0D6D; Deligne (1.1.10)
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def square
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  (((integralPullbackComposition l E).choose
      (localPositivePower (frobeniusPointIso D).hom n) (movingPoint D Y₀ x n)).app M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (constructibleIntegralPullback l E f).obj M)
      (geometry D Y₀ x hx n).2.1) ≪≫
    ((integralPullbackComposition l E).choose x
      (localPositivePower (D.geometricFrobenius Y₀).hom n)).app M

/-- The uncontracted comparison b-hat, with the node's recurrence and moving points.
Source: Deligne (1.1.10)--(1.1.14); Stacks 0D6D
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def squareHat
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) :
    (n : ℕ) → (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) →
      (pullbackPower (constructibleIntegralPullback l E (frobeniusPointIso D).hom) n).obj
        ((constructibleIntegralPullback l E (movingPoint D Y₀ x n)).obj M) ≅
      (constructibleIntegralPullback l E x).obj
        ((pullbackPower (constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom) n).obj M)
  | 0, M => square D Y₀ l E x hx 0 M
  | n + 1, M =>
    (constructibleIntegralPullback l E (frobeniusPointIso D).hom).mapIso
      ((pullbackPower (constructibleIntegralPullback l E (frobeniusPointIso D).hom) n).mapIso
        (eqToIso (congrArg (fun z ↦ (constructibleIntegralPullback l E z).obj M)
          (geometry D Y₀ x hx n).2.2.symm))) ≪≫
    (constructibleIntegralPullback l E (frobeniusPointIso D).hom).mapIso
      (squareHat (movingPoint D Y₀ x 0) (geometry D Y₀ x hx 0).1 n M) ≪≫
    square D Y₀ l E x hx 0
      ((pullbackPower (constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom) n).obj M)

/-- The hypothesis of the conditional theorem, before applying the point fibre.
Source: Deligne (1.1.14), actual whole-system mate
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def OneStep : Prop :=
  ∀ (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left),
    (properFrobeniusIntegralExchange D Y₀ l E false).app M ≫
        integralGerm D Y₀ l E x hx
          ((constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom).obj M) =
      (constructibleIntegralPullback l E (frobeniusPointIso D).hom).map
        (integralGerm D Y₀ l E (movingPoint D Y₀ x 0) (geometry D Y₀ x hx 0).1 M) ≫
      (square D Y₀ l E x hx 0 M).hom

/-- The prescribed ordinary cohomology transport, without any Weil structure.
Source: Deligne (1.1.14), the ordinary transport composite
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def tau (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  frobeniusTransportIntegral D l Fact.out E Y₀ (frobeniusCohomologyDirectModel D Y₀) M

/-- Uncontracted positive ordinary transport: tau_(S_r M) after tau-hat_r.
Source: Deligne (1.1.14), the stated recurrence
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def tauHat (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :
    (n : ℕ) →
      (pointIntegralFibre D l Fact.out E).obj
        ((properFrobeniusIntegralFunctor D Y₀ l E false).obj M) ⟶
      (pointIntegralFibre D l Fact.out E).obj
        ((properFrobeniusIntegralFunctor D Y₀ l E false).obj
          ((pullbackPower
            (constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom) n).obj M))
  | 0 => tau D Y₀ l E M
  | n + 1 => tauHat M n ≫ tau D Y₀ l E
      ((pullbackPower (constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom) n).obj M)

/-- Uncontracted point transport, in exactly the order I-hat_(r+1)=iota_(J_r N) I-hat_r.
Source: Deligne (1.1.7), restriction--insertion--pullback transport
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def insertionHat (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (n : ℕ) → (pointIntegralFibre D l Fact.out E).obj N ⟶
      (pointIntegralFibre D l Fact.out E).obj
        ((pullbackPower (constructibleIntegralPullback l E (frobeniusPointIso D).hom) n).obj N)
  | 0 => frobeniusPointTransportIntegralConstructible D l Fact.out E N
  | n + 1 => insertionHat N n ≫
      frobeniusPointTransportIntegralConstructible D l Fact.out E
        ((pullbackPower (constructibleIntegralPullback l E (frobeniusPointIso D).hom) n).obj N)

/-- The evaluated integral germ e_x = V(v_x).
Source: Deligne (1.1.10), counit germ
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def evaluation
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  (pointIntegralFibre D l Fact.out E).map (integralGerm D Y₀ l E x hx M)

/-- Contract tau-hat using V R(d_r inverse).
Source: Deligne (1.1.14), comparison contraction
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def transport (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left)
    (n : ℕ) :=
  tauHat D Y₀ l E M n ≫ (pointIntegralFibre D l Fact.out E).map
    ((properFrobeniusIntegralFunctor D Y₀ l E false).map
      (contraction l E (D.geometricFrobenius Y₀).hom n M).inv)

/-- Contract I-hat using V(f_r inverse).
Source: Deligne (1.1.7), comparison contraction
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def insertion (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) (n : ℕ) :=
  insertionHat D l E N n ≫ (pointIntegralFibre D l Fact.out E).map
    (contraction l E (frobeniusPointIso D).hom n N).inv

/-- The left uncontracted germ composite.
Source: Deligne (1.1.14), second displayed conclusion
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def leftHat
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  tauHat D Y₀ l E M n ≫ evaluation D Y₀ l E x hx
    ((pullbackPower (constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom) n).obj M)

/-- The right uncontracted germ composite, with all three specified factors.
Source: Deligne (1.1.10)--(1.1.14), second displayed conclusion
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def rightHat
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  evaluation D Y₀ l E (movingPoint D Y₀ x n) (geometry D Y₀ x hx n).1 M ≫
    insertionHat D l E ((constructibleIntegralPullback l E (movingPoint D Y₀ x n)).obj M) n ≫
    (pointIntegralFibre D l Fact.out E).map (squareHat D Y₀ l E x hx n M).hom

/-- The left contracted composite, with the actual inverse d_r.
Source: Deligne (1.1.14), fourth displayed conclusion
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def left
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  transport D Y₀ l E M n ≫ evaluation D Y₀ l E x hx
    ((constructibleIntegralPullback l E
      (localPositivePower (D.geometricFrobenius Y₀).hom n)).obj M)

/-- The right contracted composite, with the actual inverse f_r.
Source: Deligne (1.1.10)--(1.1.14), fourth displayed conclusion
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def right
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  evaluation D Y₀ l E (movingPoint D Y₀ x n) (geometry D Y₀ x hx n).1 M ≫
    insertion D l E ((constructibleIntegralPullback l E (movingPoint D Y₀ x n)).obj M) n ≫
    (pointIntegralFibre D l Fact.out E).map (square D Y₀ l E x hx n M).hom

/-- The four integral equalities, with naturality for every integral derived arrow.
The base n=0 is the first displayed equality; n+1 represents every positive r.
Source: Deligne (1.1.3), (1.1.7), (1.1.10)--(1.1.14); Stacks 0D6D
(blueprint: lem-a1-semilinear-germ-iteration-descent).
Proof:
1. Counit naturality and naturality of the identity/composition comparisons give
   Z_x(t) v_x = v_x R(t). The same holds after applying V. Geometric projection
   equations show all moving points remain k-points, without k-linearity of g.
2. Apply V to OneStep and precompose with iota. Naturality of the specified
   restriction--insertion--pullback point transport at v_(x_1) gives leftHat=rightHat
   at n=0, the first displayed conclusion.
3. Induct simultaneously at all x. Apply step 2 at S_r M and the induction
   hypothesis at x_1. Move b-hat_r through iota by its derived naturality and use
   the three defining recurrences. This proves the uncontracted equality.
4. Expand b_r as c_(h^r,x_r)^(-1) followed by c_(x,g^r). Use compositor associativity
   on (x,g,g^r), (h,x_1,g^r), (h,h^r,x_(r+1)); the middle inverse factors cancel.
   The equality-compatible whole-system normalization of the realization theorem
   identifies these comparisons before any finite quotient is evaluated.
5. Induct using d_(r+1)=P(d_r) C_r and f_(r+1)=Q(f_r) H_r. Naturality of b_1
   moves P(d_r) across it. The result is b-hat_r followed by Z_x(d_r inverse)
   equals f_r inverse followed by b_r, the third displayed conclusion.
6. Naturality of e_x at d_r inverse, step 3 and step 5 give left=right.
   Every factor is a functor image or natural comparison, so the same induction
   proves both displayed naturality clauses. No Weil structure or finite-Tor
   hypothesis is used. -/
theorem integral (h : OneStep D Y₀ l E)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) :
    (∀ M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left,
      leftHat D Y₀ l E x hx 0 M = rightHat D Y₀ l E x hx 0 M) ∧
    (∀ (n : ℕ) (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left),
      leftHat D Y₀ l E x hx n M = rightHat D Y₀ l E x hx n M) ∧
    (∀ (n : ℕ) (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left),
      (squareHat D Y₀ l E x hx n M).hom ≫
        (constructibleIntegralPullback l E x).map
          (contraction l E (D.geometricFrobenius Y₀).hom n M).inv =
      (contraction l E (frobeniusPointIso D).hom n
        ((constructibleIntegralPullback l E (movingPoint D Y₀ x n)).obj M)).inv ≫
        (square D Y₀ l E x hx n M).hom) ∧
    (∀ (n : ℕ) (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left),
      left D Y₀ l E x hx n M = right D Y₀ l E x hx n M) ∧
    (∀ (n : ℕ) (M N : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left)
      (t : M ⟶ N),
      (pointIntegralFibre D l Fact.out E).map
          ((properFrobeniusIntegralFunctor D Y₀ l E false).map t) ≫
        leftHat D Y₀ l E x hx n N =
      leftHat D Y₀ l E x hx n M ≫ (pointIntegralFibre D l Fact.out E).map
        ((constructibleIntegralPullback l E x).map
          ((pullbackPower
            (constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom) n).map t))) ∧
    (∀ (n : ℕ) (M N : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left)
      (t : M ⟶ N),
      (pointIntegralFibre D l Fact.out E).map
          ((properFrobeniusIntegralFunctor D Y₀ l E false).map t) ≫
        left D Y₀ l E x hx n N =
      left D Y₀ l E x hx n M ≫ (pointIntegralFibre D l Fact.out E).map
        ((constructibleIntegralPullback l E x).map
          ((constructibleIntegralPullback l E
            (localPositivePower (D.geometricFrobenius Y₀).hom n)).map t))) := by
  sorry

/-- The rational ordinary image has precisely the unchanged integral object.
Source: Deligne (1.1.3), raw-localization convention
(blueprint: lem-a1-semilinear-germ-iteration-descent).
Proof: unfold the direct SupportModel branch, localizedFunctor and its object map.
It is the integral direct image wrapped as a scalar-localization object. -/
theorem rationalImageObjectEq
    (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :
    (properFrobeniusRationalFunctor D Y₀ l E false).obj M =
      (sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj
        ((properFrobeniusIntegralFunctor D Y₀ l E false).obj M.obj) := by
  sorry

/-- The ordinary rational germ is the literal localization of the integral counit germ,
followed by the specified rational pullback object comparison and point fibre.
Source: Deligne (1.1.3), (1.1.10)
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def rationalEvaluation
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  (pointRationalFibre D l Fact.out E).map
    (eqToHom (rationalImageObjectEq D Y₀ l E M) ≫
      (sfRationalConstructibleLocalization l E (Spec (.of D.k))).map
        (integralGerm D Y₀ l E x hx M.obj) ≫ (localPullbackObjectIso l E x M).inv)

/-- The rational compositor contraction is obtained by the same specified iteration.
Every localPullbackComposition is the raw-localization image of the integral compositor.
Source: Deligne (1.1.3); Stacks 0D6D
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def rationalContraction {X : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)] (g : X ⟶ X) :
    (n : ℕ) → (M : sfRationalConstructibleCategory l E X) →
      (rationalDerivedPullback l E (localPositivePower g n)).obj M ≅
        (pullbackPower (rationalDerivedPullback l E g) n).obj M
  | 0, _M => Iso.refl _
  | n + 1, M =>
    eqToIso (congrArg (fun f ↦ (rationalDerivedPullback l E f).obj M)
      (positivePower_step g n).symm) ≪≫
      localPullbackComposition l E g (localPositivePower g n) M ≪≫
      (rationalDerivedPullback l E g).mapIso (rationalContraction g n M)

/-- Rational b-hat is formed by the specified recurrence, on the unchanged objects.
Source: Deligne (1.1.3), (1.1.10)--(1.1.14)
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def rationalSquareHat
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) :
    (n : ℕ) → (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) →
      (pullbackPower (rationalDerivedPullback l E (frobeniusPointIso D).hom) n).obj
        ((rationalDerivedPullback l E (movingPoint D Y₀ x n)).obj M) ≅
      (rationalDerivedPullback l E x).obj
        ((pullbackPower (rationalDerivedPullback l E (D.geometricFrobenius Y₀).hom) n).obj M)
  | 0, M => ProperSemilinearGerms.rationalSquare D Y₀ l E x hx 0 M
  | n + 1, M =>
    (rationalDerivedPullback l E (frobeniusPointIso D).hom).mapIso
      ((pullbackPower (rationalDerivedPullback l E (frobeniusPointIso D).hom) n).mapIso
        (eqToIso (congrArg (fun z ↦ (rationalDerivedPullback l E z).obj M)
          (geometry D Y₀ x hx n).2.2.symm))) ≪≫
    (rationalDerivedPullback l E (frobeniusPointIso D).hom).mapIso
      (rationalSquareHat (movingPoint D Y₀ x 0) (geometry D Y₀ x hx 0).1 n M) ≪≫
    ProperSemilinearGerms.rationalSquare D Y₀ l E x hx 0
      ((pullbackPower (rationalDerivedPullback l E (D.geometricFrobenius Y₀).hom) n).obj M)

/-- Ordinary rational tau is the specified point transport followed by the
specified raw-localization image of the actual integral exchange mate.
Source: Deligne (1.1.3), (1.1.14)
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def rationalTau (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  frobeniusTransportRational D l Fact.out E Y₀ (frobeniusCohomologyDirectModel D Y₀) M

/-- Rational tau-hat with the source's uncontracted recurrence.
Source: Deligne (1.1.3), (1.1.14)
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def rationalTauHat (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :
    (n : ℕ) →
      (pointRationalFibre D l Fact.out E).obj
        ((properFrobeniusRationalFunctor D Y₀ l E false).obj M) ⟶
      (pointRationalFibre D l Fact.out E).obj
        ((properFrobeniusRationalFunctor D Y₀ l E false).obj
          ((pullbackPower (rationalDerivedPullback l E
            (D.geometricFrobenius Y₀).hom) n).obj M))
  | 0 => rationalTau D Y₀ l E M
  | n + 1 => rationalTauHat M n ≫ rationalTau D Y₀ l E
      ((pullbackPower (rationalDerivedPullback l E (D.geometricFrobenius Y₀).hom) n).obj M)

/-- Rational I-hat uses the recorded rationalized point transport at every step.
The localPointTransport endpoint comparison is the one fixed by raw localization.
Source: Deligne (1.1.3), (1.1.7)
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def rationalInsertionHat (N : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (n : ℕ) → (pointRationalFibre D l Fact.out E).obj N ⟶
      (pointRationalFibre D l Fact.out E).obj
        ((pullbackPower (rationalDerivedPullback l E (frobeniusPointIso D).hom) n).obj N)
  | 0 => localPointTransport l E D Fact.out N
  | n + 1 => rationalInsertionHat N n ≫ localPointTransport l E D Fact.out
      ((pullbackPower (rationalDerivedPullback l E (frobeniusPointIso D).hom) n).obj N)

/-- Rational contracted tau, with the inverse specified comparison d_r.
Source: Deligne (1.1.3), (1.1.14)
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def rationalTransport (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left)
    (n : ℕ) :=
  rationalTauHat D Y₀ l E M n ≫ (pointRationalFibre D l Fact.out E).map
    ((properFrobeniusRationalFunctor D Y₀ l E false).map
      (rationalContraction l E (D.geometricFrobenius Y₀).hom n M).inv)

/-- Rational contracted I, with the inverse specified comparison f_r.
Source: Deligne (1.1.3), (1.1.7)
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def rationalInsertion (N : sfRationalConstructibleCategory l E (Spec (.of D.k))) (n : ℕ) :=
  rationalInsertionHat D l E N n ≫ (pointRationalFibre D l Fact.out E).map
    (rationalContraction l E (frobeniusPointIso D).hom n N).inv

/-- Rational uncontracted left composite with its actual localized factors.
Source: Deligne (1.1.3), (1.1.14)
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def rationalLeftHat
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  rationalTauHat D Y₀ l E M n ≫ rationalEvaluation D Y₀ l E x hx
    ((pullbackPower (rationalDerivedPullback l E (D.geometricFrobenius Y₀).hom) n).obj M)

/-- Rational uncontracted right composite with its actual localized factors.
Source: Deligne (1.1.3), (1.1.10)--(1.1.14)
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def rationalRightHat
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  rationalEvaluation D Y₀ l E (movingPoint D Y₀ x n) (geometry D Y₀ x hx n).1 M ≫
    rationalInsertionHat D l E ((rationalDerivedPullback l E
      (movingPoint D Y₀ x n)).obj M) n ≫
    (pointRationalFibre D l Fact.out E).map (rationalSquareHat D Y₀ l E x hx n M).hom

/-- Rational contracted left composite with its actual localized factors.
Source: Deligne (1.1.3), (1.1.14)
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def rationalLeft
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  rationalTransport D Y₀ l E M n ≫ rationalEvaluation D Y₀ l E x hx
    ((rationalDerivedPullback l E
      (localPositivePower (D.geometricFrobenius Y₀).hom n)).obj M)

/-- Rational contracted right composite with its actual localized factors.
Source: Deligne (1.1.3), (1.1.10)--(1.1.14)
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def rationalRight
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  rationalEvaluation D Y₀ l E (movingPoint D Y₀ x n) (geometry D Y₀ x hx n).1 M ≫
    rationalInsertion D l E ((rationalDerivedPullback l E (movingPoint D Y₀ x n)).obj M) n ≫
    (pointRationalFibre D l Fact.out E).map (ProperSemilinearGerms.rationalSquare D Y₀ l E x hx n
      M).hom

/-- All four rational identities with the specified localized factors, natural for
all rational morphisms, including arbitrary finite sums of scalar tensor arrows.
Source: Deligne (1.1.3), (1.1.7), (1.1.10)--(1.1.14)
(blueprint: lem-a1-semilinear-germ-iteration-descent).
Proof (step 7): apply raw scalar localization to the integral germ and comparison
identities, then apply the rational point fibre. Localization keeps every object
and preserves compositions and inverses. The operations and their ordinary
counit/exchange are the prescribed rationalizations by lem-fix-operation-reduction.
The point fibre sends t tensor a to a times V(t) tensor E; point transport is its
specified integral tensor image by def-weil-frobenius-point-transport. Thus every
factor is precisely the rational factor defined here. Naturality for each integral
tensor summand follows from integral naturality; multiply by the scalar and add to
obtain naturality for every localized arrow. No new lattice is selected. -/
theorem rational (h : OneStep D Y₀ l E)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) :
    (∀ M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left,
      rationalLeftHat D Y₀ l E x hx 0 M = rationalRightHat D Y₀ l E x hx 0 M) ∧
    (∀ (n : ℕ) (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left),
      rationalLeftHat D Y₀ l E x hx n M = rationalRightHat D Y₀ l E x hx n M) ∧
    (∀ (n : ℕ) (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left),
      (rationalSquareHat D Y₀ l E x hx n M).hom ≫
        (rationalDerivedPullback l E x).map
          (rationalContraction l E (D.geometricFrobenius Y₀).hom n M).inv =
      (rationalContraction l E (frobeniusPointIso D).hom n
        ((rationalDerivedPullback l E (movingPoint D Y₀ x n)).obj M)).inv ≫
        (ProperSemilinearGerms.rationalSquare D Y₀ l E x hx n M).hom) ∧
    (∀ (n : ℕ) (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left),
      rationalLeft D Y₀ l E x hx n M = rationalRight D Y₀ l E x hx n M) ∧
    (∀ (n : ℕ) (M N : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left)
      (t : M ⟶ N),
      (pointRationalFibre D l Fact.out E).map
          ((properFrobeniusRationalFunctor D Y₀ l E false).map t) ≫
        rationalLeftHat D Y₀ l E x hx n N =
      rationalLeftHat D Y₀ l E x hx n M ≫ (pointRationalFibre D l Fact.out E).map
        ((rationalDerivedPullback l E x).map
          ((pullbackPower
            (rationalDerivedPullback l E (D.geometricFrobenius Y₀).hom) n).map t))) ∧
    (∀ (n : ℕ) (M N : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left)
      (t : M ⟶ N),
      (pointRationalFibre D l Fact.out E).map
          ((properFrobeniusRationalFunctor D Y₀ l E false).map t) ≫
        rationalLeft D Y₀ l E x hx n N =
      rationalLeft D Y₀ l E x hx n M ≫ (pointRationalFibre D l Fact.out E).map
        ((rationalDerivedPullback l E x).map
          ((rationalDerivedPullback l E
            (localPositivePower (D.geometricFrobenius Y₀).hom n)).map t))) := by
  sorry

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The canonical scalar comparison for the uncontracted pullback power.
Source: Deligne (1.1.3); specified scalar pullback comparisons
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def powerScalar {X : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)] (g : X ⟶ X) :
    (n : ℕ) → (M : sfRationalConstructibleCategory l E X) →
      (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
        ((pullbackPower (rationalDerivedPullback l E g) n).obj M) ≅
      (pullbackPower (rationalDerivedPullback l L g) n).obj
        ((sfRationalScalarExtension l E X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)
  | 0, M => (rationalPullbackScalarComparison l E L ι g).app M
  | n + 1, M =>
    (rationalPullbackScalarComparison l E L ι g).app
      ((pullbackPower (rationalDerivedPullback l E g) n).obj M) ≪≫
    (rationalDerivedPullback l L g).mapIso (powerScalar g n M)

/-- The prescribed source scalar comparison, ordinary direct image then point fibre.
It includes the identity field extension, and uses no compact-support conversion.
Source: Deligne (1.1.3), (1.1.14), operation and point scalar comparisons
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def sourceScalar (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  (frobeniusCohomologyRationalScalar D l Fact.out E Y₀
    (Compactification.ofIsProper Y₀.hom) false L ι).app M

/-- The canonical target comparison for V Z_x S_r, built in the order V, Z_x, S_r.
Source: Deligne (1.1.3), (1.1.10), normalized scalar comparisons
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def hatTargetScalar
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  (pointRationalFibreScalarIso D l Fact.out E L ι).symm.app
      ((rationalDerivedPullback l E x).obj
        ((pullbackPower (rationalDerivedPullback l E (D.geometricFrobenius Y₀).hom) n).obj M)) ≪≫
    (pointRationalFibre D l Fact.out L).mapIso
      ((rationalPullbackScalarComparison l E L ι x).app
        ((pullbackPower (rationalDerivedPullback l E (D.geometricFrobenius Y₀).hom) n).obj M)) ≪≫
    (pointRationalFibre D l Fact.out L).mapIso
      ((rationalDerivedPullback l L x).mapIso
        (powerScalar l E L ι (D.geometricFrobenius Y₀).hom n M))

/-- The canonical target comparison for V Z_x P_r, using the actual g^r pullback.
Source: Deligne (1.1.3), (1.1.10), normalized scalar comparisons
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def targetScalar
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  (pointRationalFibreScalarIso D l Fact.out E L ι).symm.app
      ((rationalDerivedPullback l E x).obj
        ((rationalDerivedPullback l E
          (localPositivePower (D.geometricFrobenius Y₀).hom n)).obj M)) ≪≫
    (pointRationalFibre D l Fact.out L).mapIso
      ((rationalPullbackScalarComparison l E L ι x).app
        ((rationalDerivedPullback l E
          (localPositivePower (D.geometricFrobenius Y₀).hom n)).obj M)) ≪≫
    (pointRationalFibre D l Fact.out L).mapIso
      ((rationalDerivedPullback l L x).mapIso
        ((rationalPullbackScalarComparison l E L ι
          (localPositivePower (D.geometricFrobenius Y₀).hom n)).app M))

/-- Further finite coefficient extension preserves both sides of the uncontracted
and contracted germ identities, with the specified conjugating comparisons.
Source: Deligne (1.1.3), finite coefficient stages
(blueprint: lem-a1-semilinear-germ-iteration-descent).
Proof (step 8, finite extension): the coefficient mate and scalar pullback comparisons
of lem-fix-operation-reduction identify the counit, exchange and every compositor
under E to L. The point-sections scalar comparison identifies V, and
lem-weil-frobenius-point-transport-natural identifies iota under that same comparison.
Substitute these into the definitions of the germs and the three recurrences.
Induction shows that every factor at E transports to its named factor at L.
Their products give the four squares below. Identity and successive extensions
are included, using the ordinary tensor unit and tensor-tower comparisons. -/
theorem scalarCompatibility
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ)
    (M : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :
    ((DerivedCategory.pointFdScalarExtension ι.toRingHom).map
        (rationalLeftHat D Y₀ l E x hx n M) ≫
        (hatTargetScalar D Y₀ l E L ι x n M).hom =
      (sourceScalar D Y₀ l E L ι M).hom ≫
        rationalLeftHat D Y₀ l L x hx n
          ((sfRationalScalarExtension l E (D.geometricFiber Y₀).left 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)) ∧
    ((DerivedCategory.pointFdScalarExtension ι.toRingHom).map
        (rationalRightHat D Y₀ l E x hx n M) ≫
        (hatTargetScalar D Y₀ l E L ι x n M).hom =
      (sourceScalar D Y₀ l E L ι M).hom ≫
        rationalRightHat D Y₀ l L x hx n
          ((sfRationalScalarExtension l E (D.geometricFiber Y₀).left 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)) ∧
    ((DerivedCategory.pointFdScalarExtension ι.toRingHom).map
        (rationalLeft D Y₀ l E x hx n M) ≫
        (targetScalar D Y₀ l E L ι x n M).hom =
      (sourceScalar D Y₀ l E L ι M).hom ≫
        rationalLeft D Y₀ l L x hx n
          ((sfRationalScalarExtension l E (D.geometricFiber Y₀).left 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)) ∧
    ((DerivedCategory.pointFdScalarExtension ι.toRingHom).map
        (rationalRight D Y₀ l E x hx n M) ≫
        (targetScalar D Y₀ l E L ι x n M).hom =
      (sourceScalar D Y₀ l E L ι M).hom ≫
        rationalRight D Y₀ l L x hx n
          ((sfRationalScalarExtension l E (D.geometricFiber Y₀).left 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)) := by
  sorry

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The LeftHat composite as its finite-stage class in the faithful point realization.
Source: Deligne (1.1.3), (1.1.14), common finite stages
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def qbarLeftHat
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ)
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :=
  (stageRealization.{u, v} l Ω M.stage).map
    (rationalLeftHat D Y₀ l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M.stage)
      x hx n M.obj)

/-- The RightHat composite as its finite-stage class in the faithful point realization.
Source: Deligne (1.1.3), (1.1.14), common finite stages
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def qbarRightHat
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ)
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :=
  (stageRealization.{u, v} l Ω M.stage).map
    (rationalRightHat D Y₀ l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M.stage)
      x hx n M.obj)

/-- The Left composite as its finite-stage class in the faithful point realization.
Source: Deligne (1.1.3), (1.1.14), common finite stages
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def qbarLeft
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ)
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :=
  (stageRealization.{u, v} l Ω M.stage).map
    (rationalLeft D Y₀ l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M.stage)
      x hx n M.obj)

/-- The Right composite as its finite-stage class in the faithful point realization.
Source: Deligne (1.1.3), (1.1.14), common finite stages
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def qbarRight
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ)
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :=
  (stageRealization.{u, v} l Ω M.stage).map
    (rationalRight D Y₀ l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M.stage)
      x hx n M.obj)

/-- Ordinary-sections source comparison, retaining the ordinary branch false.
Source: Deligne (1.1.14), normalized common-stage coefficient comparisons
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
abbrev qbarSourceComparison
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : M.stage ≤ L) :=
  frobeniusCohomologyRealizedComparison D l Fact.out Y₀ Ω
    (Compactification.ofIsProper Y₀.hom) false M L h

/-- The uncontracted target comparison, conjugated by the specified contractions
from and to the actual pullback power. This fixes its normalization completely.
Source: Stacks 0D6D; Deligne (1.1.3), (1.1.14)
(blueprint: lem-a1-semilinear-germ-iteration-descent). -/
def qbarHatTargetComparison
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : M.stage ≤ L) :
    (stageRealization.{u, v} l Ω M.stage).obj
        ((pointRationalFibre D l Fact.out (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
          M.stage)).obj
          ((rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M.stage)
            x).obj
            ((pullbackPower (rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M.stage)
              (D.geometricFrobenius Y₀).hom) n).obj M.obj))) ≅
      (stageRealization.{u, v} l Ω L).obj
        ((pointRationalFibre D l Fact.out (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
          L)).obj
          ((rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) x).obj
            ((pullbackPower (rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
              (D.geometricFrobenius Y₀).hom) n).obj (M.toStage h)))) :=
  (stageRealization.{u, v} l Ω M.stage).mapIso
      ((pointRationalFibre D l Fact.out
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M.stage)).mapIso
        ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M.stage) x).mapIso
          (rationalContraction l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M.stage)
            (D.geometricFrobenius Y₀).hom n M.obj).symm)) ≪≫
    realizedTargetComparison.{u, v} D Y₀ l Ω x n M L h ≪≫
    (stageRealization.{u, v} l Ω L).mapIso
      ((pointRationalFibre D l Fact.out
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).mapIso
        ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) x).mapIso
          (rationalContraction l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
            (D.geometricFrobenius Y₀).hom n (M.toStage h))))

/-- All four identities over the algebraic closure, at literal finite stages.
Naturality is quantified over every representative at any common stage, and each
side is identified with its further-stage representative under canonical comparisons.
The third equality is in the common-stage sheaf category, before point realization.
Source: Deligne (1.1.3), (1.1.7), (1.1.10)--(1.1.14); Stacks 0D6D
(blueprint: lem-a1-semilinear-germ-iteration-descent).
Proof: step 7 gives rational and its naturality at each finite field F. Apply the
inclusion functor to the contraction equation and stageRealization to the other
three equations. These functors preserve products and equality. Every common-stage
object has exactly the indicated stage and underlying object. Every common-stage
morphism is represented by a rational arrow at some common field, so rational
naturality gives both displayed naturality equations there. For any further field
L use scalarCompatibility: the normalized whole-system operation mates identify
counit and exchange, and the point scalar comparison identifies insertion. Induction
identifies each recurrence and the contraction. The tensor-tower comparison then
gives precisely the four conjugation equations below. Their validity for every
L, including L equal to the source stage, identifies all representatives; the
tensor-tower coherence gives independence of successive enlargements. -/
theorem descent
    (h : ∀ F : AlgebraicallyClosedCoefficients.Index l Ω,
      OneStep D Y₀ l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F))
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) :
    (∀ M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left,
      qbarLeftHat D Y₀ l Ω x hx 0 M = qbarRightHat D Y₀ l Ω x hx 0 M) ∧
    (∀ (n : ℕ) (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left),
      qbarLeftHat D Y₀ l Ω x hx n M = qbarRightHat D Y₀ l Ω x hx n M) ∧
    (∀ (F : AlgebraicallyClosedCoefficients.Index l Ω) (n : ℕ)
      (M : sfRationalConstructibleCategory l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
        (D.geometricFiber Y₀).left),
      (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω)
          (Y := Spec (.of D.k)) F).map
        ((rationalSquareHat D Y₀ l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) x hx n
          M).hom ≫
          (rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) x).map
            (rationalContraction l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
              (D.geometricFrobenius Y₀).hom n M).inv) =
      (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω)
          (Y := Spec (.of D.k)) F).map
        ((rationalContraction l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
          (frobeniusPointIso D).hom n
          ((rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
            (movingPoint D Y₀ x n)).obj M)).inv ≫
          (ProperSemilinearGerms.rationalSquare D Y₀ l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) x hx n M).hom)) ∧
    (∀ (n : ℕ) (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left),
      qbarLeft D Y₀ l Ω x hx n M = qbarRight D Y₀ l Ω x hx n M) ∧
    (∀ (F : AlgebraicallyClosedCoefficients.Index l Ω) (n : ℕ)
      (M N : sfRationalConstructibleCategory l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        F) (D.geometricFiber Y₀).left) (t : M ⟶ N),
      (stageRealization.{u, v} l Ω F).map
          ((pointRationalFibre D l Fact.out (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
            F)).map
            ((properFrobeniusRationalFunctor D Y₀ l (AlgebraicallyClosedCoefficients.Coefficient.{u}
              l Ω F) false).map t)) ≫
        (stageRealization.{u, v} l Ω F).map (rationalLeftHat D Y₀ l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) x hx n N) =
      (stageRealization.{u, v} l Ω F).map (rationalLeftHat D Y₀ l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) x hx n M) ≫
        (stageRealization.{u, v} l Ω F).map
          ((pointRationalFibre D l Fact.out (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
            F)).map
            ((rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
              x).map ((pullbackPower (rationalDerivedPullback l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) (D.geometricFrobenius Y₀).hom)
              n).map t)))) ∧
    (∀ (F : AlgebraicallyClosedCoefficients.Index l Ω) (n : ℕ)
      (M N : sfRationalConstructibleCategory l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        F) (D.geometricFiber Y₀).left) (t : M ⟶ N),
      (stageRealization.{u, v} l Ω F).map
          ((pointRationalFibre D l Fact.out (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
            F)).map
            ((properFrobeniusRationalFunctor D Y₀ l (AlgebraicallyClosedCoefficients.Coefficient.{u}
              l Ω F) false).map t)) ≫
        (stageRealization.{u, v} l Ω F).map (rationalLeft D Y₀ l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) x hx n N) =
      (stageRealization.{u, v} l Ω F).map (rationalLeft D Y₀ l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) x hx n M) ≫
        (stageRealization.{u, v} l Ω F).map
          ((pointRationalFibre D l Fact.out (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
            F)).map
            ((rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
              x).map ((rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l
              Ω F) (localPositivePower (D.geometricFrobenius Y₀).hom n)).map t)))) ∧
    (∀ (n : ℕ) (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
      (L : AlgebraicallyClosedCoefficients.Index l Ω) (hL : M.stage ≤ L),
      (qbarSourceComparison D Y₀ l Ω M L hL).inv ≫ qbarLeftHat D Y₀ l Ω x hx n M ≫
          (qbarHatTargetComparison D Y₀ l Ω x n M L hL).hom =
        (stageRealization.{u, v} l Ω L).map
          (rationalLeftHat D Y₀ l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) x hx n (M.toStage hL))) ∧
    (∀ (n : ℕ) (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
      (L : AlgebraicallyClosedCoefficients.Index l Ω) (hL : M.stage ≤ L),
      (qbarSourceComparison D Y₀ l Ω M L hL).inv ≫ qbarRightHat D Y₀ l Ω x hx n M ≫
          (qbarHatTargetComparison D Y₀ l Ω x n M L hL).hom =
        (stageRealization.{u, v} l Ω L).map
          (rationalRightHat D Y₀ l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) x hx n (M.toStage hL))) ∧
    (∀ (n : ℕ) (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
      (L : AlgebraicallyClosedCoefficients.Index l Ω) (hL : M.stage ≤ L),
      (qbarSourceComparison D Y₀ l Ω M L hL).inv ≫ qbarLeft D Y₀ l Ω x hx n M ≫
          (realizedTargetComparison.{u, v} D Y₀ l Ω x n M L hL).hom =
        (stageRealization.{u, v} l Ω L).map
          (rationalLeft D Y₀ l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) x hx n (M.toStage hL))) ∧
    (∀ (n : ℕ) (M : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
      (L : AlgebraicallyClosedCoefficients.Index l Ω) (hL : M.stage ≤ L),
      (qbarSourceComparison D Y₀ l Ω M L hL).inv ≫ qbarRight D Y₀ l Ω x hx n M ≫
          (realizedTargetComparison.{u, v} D Y₀ l Ω x n M L hL).hom =
        (stageRealization.{u, v} l Ω L).map
          (rationalRight D Y₀ l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) x hx n (M.toStage hL))) := by
  sorry

end SemilinearGermIteration
end WeilConjectures
