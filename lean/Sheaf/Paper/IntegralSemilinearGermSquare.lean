module

public import Sheaf.Paper.ProperSectionsSemilinearGerms
public import Sheaf.Paper.FrobeniusGeometricExchange
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.CompletedRlimFunctor
public import Sheaf.Paper.SfDerivedDirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.BasicOperationsCoefficientReduction

/-! # Completed one-step semilinear counit germ square

Source: Deligne, Weil II (1.1.3), (1.1.7), (1.1.10)--(1.1.14), pp. 150--153;
Stacks Project, Tag 07A7, remark-base-change
(blueprint: lem-a1-integral-semilinear-germ-square).

All arrows use the published simultaneous coefficient systems. In particular,
the exchange is the realized system mate, rather than a map specified by reductions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open FrobeniusExchange ProperSemilinearGerms

variable (D : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of D.k₀))) [IsProper Y₀.hom]
  (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

namespace IntegralSemilinearGerms

/-- The integer-indexed moving point, including zero and negative exponents.
Source: Deligne (1.1.7), (1.1.10)
(blueprint: lem-a1-integral-semilinear-germ-square). -/
def point (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (j : ℤ) :=
  ((@id (Aut (Spec (.of D.k))) (frobeniusPointIso D)) ^ (-j)).hom ≫ x ≫
    ((D.geometricFrobenius Y₀) ^ j).hom

/-- Every moving point is over k and the next point gives the semilinear square.
Source: Deligne (1.1.7), (1.1.10)
(blueprint: lem-a1-integral-semilinear-germ-square).
Proof: iterate g a = a h in the automorphism groups, using inverses for negative
indices. Then h^(-j) x g^j a = h^(-j) x a h^j = id. Cancellation of h and its
inverse gives h x_(j+1) = x_j g. No assertion that g is a k-morphism is used. -/
theorem point_properties
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (j : ℤ) :
    point D Y₀ x j ≫ (D.geometricFiber Y₀).hom = 𝟙 _ ∧
      (frobeniusPointIso D).hom ≫ point D Y₀ x (j + 1) =
        point D Y₀ x j ≫ (D.geometricFrobenius Y₀).hom := by
  sorry

/-- The actual geometric Frobenius square for the structure morphism.
Source: Deligne (1.1.7); Stacks 07A7
(blueprint: lem-a1-integral-semilinear-germ-square).
Proof: the second projection of id times Spec(gamma) is the second projection
followed by Spec(gamma), by galoisMap_projections. -/
theorem structure_square :
    (D.geometricFrobenius Y₀).hom ≫ (D.geometricFiber Y₀).hom =
      (D.geometricFiber Y₀).hom ≫ (frobeniusPointIso D).hom := by
  sorry

/-- The recorded first moving point g x h^(-1) is the integer moving point at j = 1;
it is a k-point, and g x = x_1 h. This is the clause used for x_1 below.
Source: Deligne (1.1.7), (1.1.10)
(blueprint: lem-a1-integral-semilinear-germ-square).
Proof: the positive power with index 0 is the map itself, and inversion in the
automorphism group is Iso.symm, so point 1 = movingPoint 0 by unfolding.
The other two equalities are point_properties at j = 1 and at j = 0, after
cancelling the identity powers at j = 0. -/
theorem movingPoint_zero_properties
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) :
    point D Y₀ x 1 = movingPoint D Y₀ x 0 ∧
      movingPoint D Y₀ x 0 ≫ (D.geometricFiber Y₀).hom = 𝟙 _ ∧
      (frobeniusPointIso D).hom ≫ movingPoint D Y₀ x 0 =
        x ≫ (D.geometricFrobenius Y₀).hom := by
  sorry

/-- u_x inverse, from the identity comparison and the specified compositor.
Source: Stacks 0D6D, 0941
(blueprint: lem-a1-integral-semilinear-germ-square). -/
def unitInverse
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _)
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :=
  (integralComparisonUnit l E (comparisons l) (Spec (.of D.k)) N).symm ≪≫
    eqToIso (congrArg (fun f ↦ (integralDerivedPullback l E f).obj N.obj) hx.symm) ≪≫
    (sfIntegralConstructible l E (Spec (.of D.k))).ι.mapIso
      (((integralPullbackComposition l E).choose x (D.geometricFiber Y₀).hom).app N)

/-- Theta is c_(a,h) inverse followed by the equality ag=ha and c_(g,a).
Source: Stacks 07A7, 0D6D
(blueprint: lem-a1-integral-semilinear-germ-square). -/
def theta (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :=
  (((integralPullbackComposition l E).choose
      (D.geometricFiber Y₀).hom (frobeniusPointIso D).hom).app N).symm ≪≫
    eqToIso (congrArg (fun f ↦ (constructibleIntegralPullback l E f).obj N)
      (structure_square D Y₀).symm) ≪≫
    ((integralPullbackComposition l E).choose
      (D.geometricFrobenius Y₀).hom (D.geometricFiber Y₀).hom).app N

/-- b_(1,x,M), from the two compositors and the actual moving-point square.
Source: Stacks 0D6D; Deligne (1.1.10)
(blueprint: lem-a1-integral-semilinear-germ-square). -/
def square
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) :=
  (((integralPullbackComposition l E).choose
      (frobeniusPointIso D).hom (movingPoint D Y₀ x 0)).app M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (constructibleIntegralPullback l E f).obj M)
      (movingPoint_zero_properties D Y₀ x hx).2.2) ≪≫
    ((integralPullbackComposition l E).choose x (D.geometricFrobenius Y₀).hom).app M

end IntegralSemilinearGerms

/-- The one-step integral germ identities, for the specified whole-system maps.
The arrows are in the full completed integral constructible categories; the
comparison equation is written after their faithful inclusion in the ambient category.
The last conjunct is on the ordinary derived category of entire strict systems.
Source: Deligne, Weil II (1.1.3), (1.1.7), (1.1.10)--(1.1.14), pp. 150--153;
Stacks Project, Tag 07A7, remark-base-change
(blueprint: lem-a1-integral-semilinear-germ-square).
Proof:
1. The counit and the inverse identity/composition comparisons are natural.
Their two naturality equations give Z_x(f) v_x = v_x R(f).
2. On strict coefficient systems put T = theta_(R M) followed by P(epsilon_M).
The actual exchange is its adjunction transpose R(T) eta. Counit naturality and
the left triangle identity give A(exchange) epsilon_(P M) = T. This uses the
adjunction of lem-coef-semilinear-derived-sections and the mate formula of
def-weil-pbc-adjunction-mate, without detecting morphism equality by evaluation.
3. Apply exact scalar restriction and the total derived limit of
prop-weil-pbc-rlim-functoriality to this system equation. The definitions of
integralCounit and properFrobeniusIntegralExchange use these very system words.
The unit/counit operation comparisons of lem-fix-operation-reduction and the
realization comparison of lem-trf-integral-pullback-comparison-realization
identify its image with the first completed equation below.
4. Pullback associativity for (x,a,h), (h,x_1,a), and (x,g,a), with ax=ax_1=id,
identifies both sides of the comparison equation with c_(x,g) c_(gx,a).
These are the specified whole-system-normalized comparisons, by
lem-pod-integral-pullback-composition and
lem-trf-integral-pullback-comparison-realization.
5. Pull the first completed equation back by x, substitute the comparison
identity of step 4, and apply naturality of b_(1,x) to epsilon_M. Functoriality
then gives v_x^(P M) exchange_M = b_(1,x,M) Q(v_(x_1)^M).
The separate theorem IntegralSemilinearGerms.point_properties proves the
integer-indexed geometric clause. No Weil structure on M occurs. -/
theorem integralSemilinearGermSquare
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_ι : E →ₐ[ℚ_[l]] Ω)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hx : x ≫ (D.geometricFiber Y₀).hom = 𝟙 _) :
    (∀ (M M' : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left)
      (f : M ⟶ M'),
      integralGerm D Y₀ l E x hx M ≫ (constructibleIntegralPullback l E x).map f =
        (properFrobeniusIntegralFunctor D Y₀ l E false).map f ≫
          integralGerm D Y₀ l E x hx M') ∧
    (∀ M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left,
      (constructibleIntegralPullback l E (D.geometricFiber Y₀).hom).map
          ((properFrobeniusIntegralExchange D Y₀ l E false).app M) ≫
        integralCounit D Y₀ l E
          ((constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom).obj M) =
      (IntegralSemilinearGerms.theta D Y₀ l E
          ((properFrobeniusIntegralFunctor D Y₀ l E false).obj M)).hom ≫
        (constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom).map
          (integralCounit D Y₀ l E M)) ∧
    (∀ N : sfIntegralConstructibleCategory l E (Spec (.of D.k)),
      (IntegralSemilinearGerms.unitInverse D Y₀ l E x hx
          ((constructibleIntegralPullback l E (frobeniusPointIso D).hom).obj N)).hom ≫
        (integralDerivedPullback l E x).map
          (IntegralSemilinearGerms.theta D Y₀ l E N).hom.hom =
      (integralDerivedPullback l E (frobeniusPointIso D).hom).map
          (IntegralSemilinearGerms.unitInverse D Y₀ l E (movingPoint D Y₀ x 0)
            (IntegralSemilinearGerms.movingPoint_zero_properties D Y₀ x hx).2.1 N).hom ≫
        (IntegralSemilinearGerms.square D Y₀ l E x hx
          ((constructibleIntegralPullback l E (D.geometricFiber Y₀).hom).obj N)).hom.hom) ∧
    (∀ M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left,
      (properFrobeniusIntegralExchange D Y₀ l E false).app M ≫
          integralGerm D Y₀ l E x hx
            ((constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom).obj M) =
        (constructibleIntegralPullback l E (frobeniusPointIso D).hom).map
            (integralGerm D Y₀ l E (movingPoint D Y₀ x 0)
              (IntegralSemilinearGerms.movingPoint_zero_properties D Y₀ x hx).2.1 M) ≫
          (IntegralSemilinearGerms.square D Y₀ l E x hx M).hom) ∧
    (∀ C : coefficientSequenceDerived l E (D.geometricFiber Y₀).left,
      (integralComparisonDerivedSequencePullback l E (D.geometricFiber Y₀).hom).map
          ((systemExchange l E (D.geometricFiber Y₀).hom
            (D.geometricFrobenius Y₀).hom (frobeniusPointIso D).hom
            (IntegralSemilinearGerms.structure_square D Y₀)).app C) ≫
        (systemAdjunction l E (D.geometricFiber Y₀).hom).counit.app
          ((integralComparisonDerivedSequencePullback l E
            (D.geometricFrobenius Y₀).hom).obj C) =
      (systemSquare l E (D.geometricFiber Y₀).hom
          (D.geometricFrobenius Y₀).hom (frobeniusPointIso D).hom
          (IntegralSemilinearGerms.structure_square D Y₀)).hom.app
            ((systemDirect l E (D.geometricFiber Y₀).hom).obj C) ≫
        (integralComparisonDerivedSequencePullback l E
          (D.geometricFrobenius Y₀).hom).map
            ((systemAdjunction l E (D.geometricFiber Y₀).hom).counit.app C)) := by
  sorry

end WeilConjectures
