/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.LocalFrobeniusTransportNormalization
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.LocalFrobeniusTrace
import Sheaf.Paper.IteratedReturnTransportScalarCalculus

/-! # Block composition and powers of rational point returns

Source: blueprint latest, sec-deligne-laumon-a1/sk-p-dl-a1-some-weight,
lem-fd-realified-kernel-real.proof.md, Step 2; Deligne, Weil II (1.1.7)--(1.1.10)
(blueprint: lem-fd-rational-return-block-power).

Positive periods and block counts are indexed by successors. The transport is the
published normalized transport in the pullback-along-a-power presentation; the block
comparison explicitly supplies the composition identification suppressed in the paper.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- Predecessor of the positive block length (r+1)(d+1), with the first block literal.
Source: blueprint Step 2, blocks of length d
(blueprint: lem-fd-rational-return-block-power). -/
def fdRationalReturnIndex (d : ℕ) : ℕ → ℕ
  | 0 => d
  | r + 1 => fdRationalReturnIndex d r + d + 1

private theorem positivePower_add {X : Scheme.{u}} (f : X ⟶ X) (a b : ℕ) :
    localPositivePower f (a + b + 1) = localPositivePower f a ≫ localPositivePower f b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [localPositivePower, ← Nat.add_assoc, ih, localPositivePower, Category.assoc]

/-- The base return square also returns after any positive number of blocks.
Source: blueprint Step 2, repeated-return argument
(blueprint: lem-fd-rational-return-block-power).
Proof: the base equality is g_s^d z = z g_Y^d. Compose it r+1 times,
using associativity, to get g_s^((r+1)d) z = z g_Y^((r+1)d).
The published positivePower_eq identifies both power presentations. Induction in r
shows that fdRationalReturnIndex d r + 1 = (r+1)(d+1), so these are exactly
the positive multiples of the original period. -/
theorem fdRationalReturn_multiple (d r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (w : localPositivePower (frobeniusPointIso D).hom d ≫ z =
      z ≫ localPositivePower (D.geometricFrobenius Y₀).hom d) :
    localPositivePower (frobeniusPointIso D).hom (fdRationalReturnIndex d r) ≫ z =
      z ≫ localPositivePower (D.geometricFrobenius Y₀).hom (fdRationalReturnIndex d r) := by
  induction r with
  | zero => exact w
  | succ r ih =>
    simp only [fdRationalReturnIndex, positivePower_add]
    rw [Category.assoc, w, ← Category.assoc, ih, Category.assoc]

/-- The scheme-power equality underlying the specified block compositor.
Source: blueprint Step 2, a=d and b=rd
(blueprint: lem-fd-rational-return-block-power).
Proof: positivePower_eq identifies the three displayed positive powers with ordinary
endomorphism powers. Their exponents obey (r+2)(d+1)=(r+1)(d+1)+(d+1).
Apply pow_add, recalling that multiplication in End is reverse categorical composition. -/
theorem fdRationalReturn_blockPower (d r : ℕ) :
    localPositivePower (D.geometricFrobenius Y₀).hom (fdRationalReturnIndex d (r + 1)) =
      localPositivePower (D.geometricFrobenius Y₀).hom d ≫
        localPositivePower (D.geometricFrobenius Y₀).hom (fdRationalReturnIndex d r) := by
  simpa only [fdRationalReturnIndex, Nat.add_comm] using
    positivePower_add (D.geometricFrobenius Y₀).hom d (fdRationalReturnIndex d r)

/-- The existing J=Fib_s Lz*, with the canonical inherited prime-invertibility instances.
Source: blueprint Step 2, J=HP (blueprint: lem-fd-rational-return-block-power). -/
def fdRationalReturnFibre (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left ⥤
      (DerivedCategory.pointFiniteDimensional E).FullSubcategory :=
  @LocalFrobeniusTransport.rationalFibre D l _ hl E _ _ _ Y₀ _ _
    (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl Y₀) z

/-- Pullback along g_Y^(n+1), using the published rational pullback.
Source: blueprint Step 2, associative power identifications
(blueprint: lem-fd-rational-return-block-power). -/
def fdRationalReturnPullback (n : ℕ) :
    sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left ⥤
      sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left :=
  @rationalDerivedPullback l _ E _ _ _ _ _
    (localPositivePower (D.geometricFrobenius Y₀).hom n)
    (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)

variable (C : IntegralComparisonSystem.{u} l)

/-- The published normalized t_((r+1)(d+1)), using the deduced return equality.
This specializes the published LocalFrobeniusTransport.rationalTransport.
Source: blueprint Step 2, normalized successive point transports
(blueprint: lem-fd-rational-return-block-power). -/
def fdRationalReturnTransport (d r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (w : localPositivePower (frobeniusPointIso D).hom d ≫ z =
      z ≫ localPositivePower (D.geometricFrobenius Y₀).hom d)
    (N : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :
    (fdRationalReturnFibre D l hl E Y₀ z).obj N ⟶
      (fdRationalReturnFibre D l hl E Y₀ z).obj
        ((fdRationalReturnPullback D l hl E Y₀ (fdRationalReturnIndex d r)).obj N) :=
  @LocalFrobeniusTransport.rationalTransport D l _ hl E _ _ _ Y₀ _ _ C
    (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl Y₀)
    (fdRationalReturnIndex d r) z (fdRationalReturn_multiple D Y₀ d r z w) N

/-- The specified block-composition identification, with its actual scheme-power equality.
Source: blueprint Step 2, associative composition identifications
(blueprint: lem-fd-rational-return-block-power). -/
def fdRationalReturnBlockComparison (d r : ℕ)
    (N : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left) :
    (fdRationalReturnPullback D l hl E Y₀ (fdRationalReturnIndex d (r + 1))).obj N ≅
      (fdRationalReturnPullback D l hl E Y₀ d).obj
        ((fdRationalReturnPullback D l hl E Y₀ (fdRationalReturnIndex d r)).obj N) :=
  eqToIso (congrArg
      (fun f ↦ (@rationalDerivedPullback l _ E _ _ _ _ _ f
        (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).obj N)
      (fdRationalReturn_blockPower D Y₀ d r)) ≪≫
    @LocalFrobeniusTransport.rationalComposition l _ E _ _ _ C _ _ _
      (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)
      (sfWeilPrimeInvertible D l hl Y₀)
      (localPositivePower (D.geometricFrobenius Y₀).hom d)
      (localPositivePower (D.geometricFrobenius Y₀).hom (fdRationalReturnIndex d r)) N

/-- R_((r+1)(d+1))=J(theta^[((r+1)(d+1))]) t_((r+1)(d+1)).
The Weil iterate is the dependency's actual iterate, and t is the specified normalized map.
Source: blueprint Step 2, local rational return operator
(blueprint: lem-fd-rational-return-block-power). -/
def fdRationalReturnOperator (d r : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (w : localPositivePower (frobeniusPointIso D).hom d ≫ z =
      z ≫ localPositivePower (D.geometricFrobenius Y₀).hom d)
    (M : sfWeilComplex D l hl Y₀ E) :
    End ((fdRationalReturnFibre D l hl E Y₀ z).obj M.carrier) :=
  fdRationalReturnTransport D l hl E Y₀ C d r z w M.carrier ≫
    (fdRationalReturnFibre D l hl E Y₀ z).map
      (localWeilIterate l E D hl Y₀ M (fdRationalReturnIndex d r)).hom

/-- Block composition for every rational constructible object, recurrence and powers for
all rational Weil complexes, and the specified closed-point Frobenius in every degree.
No integral Weil-stable lattice or Tor-amplitude of reductions is assumed.
Source: blueprint latest, sec-deligne-laumon-a1/sk-p-dl-a1-some-weight,
lem-fd-realified-kernel-real.proof.md, Step 2; Deligne Weil II (1.1.7)--(1.1.10)
(blueprint: lem-fd-rational-return-block-power).
Proof:
1. Write P=Lz*, U=Lg_s*, H=Fib_s. The helper return equality gives every positive
multiple. lem-trf-iterated-return-transport-scalar-calculus identifies the normalized
transport with H(v_j) I^j and proves naturality for all rational morphisms.
2. lem-trf-integral-pullback-comparison-realization pastes the two return squares:
v_(a+b)=v_(a,G^b N) U^a(v_b), after the specified composition identifications.
The recursion for I gives I^(a+b)=I^a_(U^b N) I^b_N by reassociation.
3. Apply the rational naturality of I^a to v_b. Functoriality of H then gives
 t_(a+b)=t_(a,G^b N) t_b. The displayed block comparison records the endpoints.
4. The Weil recursion gives theta^[a+b]=theta^[a] G^a(theta^[b]). Naturality of t_a
for the rational morphism theta^[b] and the preceding block equation yield
R_(a+b)=R_a R_b for a=d and b=rd. Induct on the positive block count to get R_ed=R_d^e.
5. For the geometric lift of a closed point of degree d, def-weil-local-frobenius-trace
uses precisely I^d, the same normalized return comparison and J(theta^[d]). Thus R_d
induces its specified geometric Frobenius on H^j for every integer j. All steps are in
raw rationalized categories; no integral Weil structure or finite-reduction Tor bound
enters the calculation. -/
theorem fdRationalReturnBlockPower (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom] (C : IntegralComparisonSystem.{u} c.l)
    (_hC : IntegralComparisonRealizationCoherence c.l E.val E.val (AlgHom.id ℚ_[c.l] E.val) C)
    (d : ℕ) (z : Over.mk (𝟙 (Spec (.of D.k))) ⟶ D.geometricFiber Y₀)
    (w : localPositivePower (frobeniusPointIso D).hom d ≫ z.left =
      z.left ≫ localPositivePower (D.geometricFrobenius Y₀).hom d) :
    (∀ (N : sfRationalConstructibleCategory c.l E.val (D.geometricFiber Y₀).left) (r : ℕ),
      fdRationalReturnTransport D c.l c.different E.val Y₀ C d (r + 1) z.left w N =
        fdRationalReturnTransport D c.l c.different E.val Y₀ C d r z.left w N ≫
          fdRationalReturnTransport D c.l c.different E.val Y₀ C d 0 z.left w
            ((fdRationalReturnPullback D c.l c.different E.val Y₀
              (fdRationalReturnIndex d r)).obj N) ≫
          (fdRationalReturnFibre D c.l c.different E.val Y₀ z.left).map
            (fdRationalReturnBlockComparison D c.l c.different E.val Y₀ C d r N).inv) ∧
    (∀ (M : sfWeilComplex D c.l c.different Y₀ E.val) (r : ℕ),
      fdRationalReturnOperator D c.l c.different E.val Y₀ C d (r + 1) z.left w M =
        fdRationalReturnOperator D c.l c.different E.val Y₀ C d 0 z.left w M *
          fdRationalReturnOperator D c.l c.different E.val Y₀ C d r z.left w M) ∧
    (∀ (M : sfWeilComplex D c.l c.different Y₀ E.val) (e : ℕ),
      fdRationalReturnOperator D c.l c.different E.val Y₀ C d e z.left w M =
        fdRationalReturnOperator D c.l c.different E.val Y₀ C d 0 z.left w M ^ (e + 1)) ∧
    (∀ (M : sfWeilComplex D c.l c.different Y₀ E.val)
      (x : {x : Y₀.left // x ∈ closedPoints Y₀.left})
      (ι : Y₀.left.residueField x.val →+* D.k)
      (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k),
      localClosedPointDegree D Y₀ x = d + 1 → z.left = localClosedPoint D Y₀ x ι hι →
      ∀ j : ℤ, HEq
        ((DerivedCategory.coefficientFdCohomology E.val j).map
          (fdRationalReturnOperator D c.l c.different E.val Y₀ C d 0 z.left w M))
        (localClosedFrobeniusCohomology c.l E.val D c.different Y₀ M x ι hι j)) := by
  sorry

end WeilConjectures
