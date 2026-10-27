module

public import Sheaf.AlgebraicGeometry.OrdinaryMultiplePoint
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Inverse
import WeilConjectures.RingTheory.PowerSeriesNormalDomain

/-! # Coordinate axes and their normalization

Source: Stacks Project, Curves, equation multicross (Tag 0C1U), and the discussion
before lemma multicross-algebra (Tag 0C1V); Algebra, Tag 0BI0 for normality.
(blueprint: lem-trf-coordinate-axes-normalization).

The auxiliary maps construct the specific rings and maps of the statement. No
normalization, evaluation map, or scalar action is chosen from an existence proof.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace AlgebraicGeometry

/-- The coordinatewise constant-coefficient map rho.
Source: Stacks Project, Curves, Tag 0C1U.
(blueprint: lem-trf-coordinate-axes-normalization). -/
def coordinateAxesConstants (k : Type u) [Field k] (b : ℕ) :
    (Fin b → PowerSeries k) →ₐ[k] (Fin b → k) where
  toRingHom := RingHom.pi fun i ↦
    PowerSeries.constantCoeff.comp (Pi.evalRingHom (fun _ : Fin b ↦ PowerSeries k) i)
  commutes' c := by
    ext i
    exact PowerSeries.constantCoeff_C c

/-- The inverse image of the diagonal k under rho, with its inherited k-algebra.
The bottom k-subalgebra of k^b is precisely the image of the diagonal scalar map.
Source: Stacks Project, Curves, equation multicross, Tag 0C1U.
(blueprint: lem-trf-coordinate-axes-normalization). -/
def coordinateAxesSubalgebra (k : Type u) [Field k] (b : ℕ) :
    Subalgebra k (Fin b → PowerSeries k) :=
  (⊥ : Subalgebra k (Fin b → k)).comap (coordinateAxesConstants k b)

/-- Evaluation on each separate coordinate axis, using Mathlib's restriction to
an embedded set of variables, with all complementary variables killed.
Source: Stacks Project, Curves, Tag 0C1U, map following equation multicross.
(blueprint: lem-trf-coordinate-axes-normalization). -/
def coordinateAxesEvaluation (k : Type u) [Field k] (b : ℕ) :
    MvPowerSeries (Fin b) k →ₐ[k] (Fin b → PowerSeries k) :=
  AlgHom.pi fun i ↦ MvPowerSeries.killCompl
    (⟨fun _ : Unit ↦ i, fun _ _ _ ↦ Subsingleton.elim _ _⟩ : Unit ↪ Fin b)

/-- The mixed-monomial ideal with generators indexed by strictly increasing pairs.
The existing `ordinaryMultiplePointRing` uses the equivalent unequal-pair ideal.
Source: Stacks Project, Curves, Tag 0C1U.
(blueprint: lem-trf-coordinate-axes-normalization). -/
def coordinateAxesMixedIdeal (k : Type u) [Field k] (b : ℕ) :
    Ideal (MvPowerSeries (Fin b) k) :=
  Ideal.span {g | ∃ i j : Fin b, i < j ∧ g = MvPowerSeries.X i * MvPowerSeries.X j}

/-- The common constant coefficient on P, read in its first coordinate; positivity
is used only to name that coordinate. The theorem identifies its kernel as maximal.
Source: Stacks Project, Curves, Tag 0C1U.
(blueprint: lem-trf-coordinate-axes-normalization). -/
def coordinateAxesResidue (k : Type u) [Field k] (b : ℕ) (hb : 1 ≤ b) :
    coordinateAxesSubalgebra k b →ₐ[k] k :=
  (Pi.evalAlgHom k (fun _ : Fin b ↦ k) ⟨0, hb⟩).comp
    ((coordinateAxesConstants k b).comp (coordinateAxesSubalgebra k b).val)

/-- The tuple of formal parameters, an element of P because all constants are zero.
Source: Stacks Project, Curves, Tag 0C1U, total-fraction calculation.
(blueprint: lem-trf-coordinate-axes-normalization). -/
def coordinateAxesParameter (k : Type u) [Field k] (b : ℕ) :
    coordinateAxesSubalgebra k b :=
  ⟨fun _ ↦ PowerSeries.X, by
    change (fun _ : Fin b ↦ PowerSeries.constantCoeff (PowerSeries.X : PowerSeries k)) ∈
      (⊥ : Subalgebra k (Fin b → k))
    simpa only [PowerSeries.constantCoeff_X, Pi.zero_def] using
      (zero_mem (⊥ : Subalgebra k (Fin b → k)))⟩

/-- The canonical coordinatewise embedding of D into the product of fraction fields.
Source: Stacks Project, Curves, Tag 0C1U, integral closure in the total fraction ring.
(blueprint: lem-trf-coordinate-axes-normalization). -/
def coordinateAxesFractionMap (k : Type u) [Field k] (b : ℕ) :
    (Fin b → PowerSeries k) →ₐ[k] (Fin b → FractionRing (PowerSeries k)) :=
  AlgHom.pi fun i ↦ (IsScalarTower.toAlgHom k (PowerSeries k)
    (FractionRing (PowerSeries k))).comp
      (Pi.evalAlgHom k (fun _ : Fin b ↦ PowerSeries k) i)

/-- The canonical embedding of P into the same product of fraction fields.
Source: Stacks Project, Curves, Tag 0C1U.
(blueprint: lem-trf-coordinate-axes-normalization). -/
def coordinateAxesSubalgebraFractionMap (k : Type u) [Field k] (b : ℕ) :
    coordinateAxesSubalgebra k b →ₐ[k] (Fin b → FractionRing (PowerSeries k)) :=
  (coordinateAxesFractionMap k b).comp (coordinateAxesSubalgebra k b).val

/-- The axes presentation, finite normalization, total fractions, and residue quotient.
All localization structures refer to the displayed canonical embeddings into the same
product of fraction fields; this is the meaning of the equalities of fraction rings.
The residue isomorphism and the quotient-vector-space isomorphism are characterized
on representatives, so they are the maps induced by rho, with the stated P-action.

Source: Stacks Project, Curves, Tag 0C1U and discussion preceding Tag 0C1V;
Algebra, Tag 0BI0 for normality of power series over a Noetherian normal domain.
(blueprint: lem-trf-coordinate-axes-normalization).

Proof, following the ten steps of the node:
1. The coefficient at n on axis i is the coefficient at n times the i-th basis
   exponent. The product coefficient formula proves multiplicativity. Constants
   agree, and c plus the sum of the positive-degree one-axis series lifts any
   tuple with common constant c, giving image P.
2. The kernel consists of mixed monomials. Assign each mixed exponent to the first
   pair of positive coordinates, and divide that coefficient by the corresponding
   mixed monomial. There are finitely many pairs, so this expresses a genuine finite
   sum of multiples of the generators. The quotient map therefore induces the stated
   k-algebra isomorphism. Unequal and increasing pairs generate the same ideal.
3. Multivariate power series are Noetherian, as is their quotient. The product of
   the domain power-series factors is reduced, and so is its subring P.
4. The common-constant map onto k has kernel the tuples with zero constants. A tuple
   with nonzero common constant has coordinatewise inverse with common constant
   c inverse. Thus precisely the complement of the kernel consists of units; this
   proves locality, the maximal-ideal description and the residue isomorphism.
5. For each d and i use a tuple with i-th entry d_i and other entries the constant
   d_i(0). Multiplying these P-elements by the coordinate idempotents and summing
   gives d. The parameter tuple is regular coordinatewise, and sD has zero constants.
6. Every nonzero one-variable series is a power of the variable times a unit, by
   its first nonzero coefficient. Thus each fraction has a variable-power denominator.
   A common exponent for the finitely many coordinates proves D[1/s] is the product
   of the fraction fields.
7. Since sd belongs to P, d/s^n equals sd/s^(n+1), identifying the two localizations.
   A tuple in P is regular exactly when all coordinates are nonzero: a vanishing
   coordinate kills the corresponding nonzero parameter times idempotent. Hence
   every regular denominator is invertible in the product, proving the total-ring
   localization assertion as well.
8. For d, form for each i the P-tuple obtained by using the coefficients of d_i in
   every coordinate. The product of X minus these tuples is monic and vanishes at d.
   Thus every element of D is integral over P.
9. Power-series-normal-domain (Tag 0BI0), applied to k, makes each factor integrally
   closed. Projecting a monic equation for a fraction tuple to each coordinate
   therefore puts every coordinate in its power-series ring. This proves the converse
   and identifies the integral closure with the canonical image of D.
10. Constants induce D/P to k^b/diagonal k. Its kernel is zero by the definition of P,
    and constant tuples show surjectivity. The constant product formula identifies
    the P-action with multiplication by the residue. Taking differences from the
    first coordinate identifies the latter quotient with k^(b-1), including the
    zero space for b=1; thus its dimension is b-1 and the maximal ideal annihilates it.
-/
theorem coordinate_axes_normalization (k : Type u) [Field k] (b : ℕ) (hb : 1 ≤ b) :
    (coordinateAxesEvaluation k b).range = coordinateAxesSubalgebra k b ∧
    RingHom.ker (coordinateAxesEvaluation k b).toRingHom = coordinateAxesMixedIdeal k b ∧
    (∃ e : ordinaryMultiplePointRing k b ≃ₐ[k] coordinateAxesSubalgebra k b,
      ∀ f : MvPowerSeries (Fin b) k,
        (e (Ideal.Quotient.mk _ f)).val = coordinateAxesEvaluation k b f) ∧
    _root_.IsReduced (coordinateAxesSubalgebra k b) ∧
    IsNoetherianRing (coordinateAxesSubalgebra k b) ∧
    (∃ hlocal : IsLocalRing (coordinateAxesSubalgebra k b),
      @IsLocalRing.maximalIdeal (coordinateAxesSubalgebra k b) _ hlocal =
        RingHom.ker ((coordinateAxesConstants k b).comp
          (coordinateAxesSubalgebra k b).val).toRingHom ∧
      RingHom.ker (coordinateAxesResidue k b hb).toRingHom =
        RingHom.ker ((coordinateAxesConstants k b).comp
          (coordinateAxesSubalgebra k b).val).toRingHom ∧
      ∃ e : ((coordinateAxesSubalgebra k b) ⧸
          RingHom.ker (coordinateAxesResidue k b hb).toRingHom) ≃ₐ[k] k,
        ∀ p : coordinateAxesSubalgebra k b,
          e (Ideal.Quotient.mk _ p) = coordinateAxesResidue k b hb p) ∧
    (∀ d : Fin b → PowerSeries k,
      ∃ p : Fin b → coordinateAxesSubalgebra k b,
        d = ∑ i : Fin b, (p i).val * Pi.single i 1) ∧
    Module.Finite (coordinateAxesSubalgebra k b) (Fin b → PowerSeries k) ∧
    coordinateAxesParameter k b ∈ nonZeroDivisors (coordinateAxesSubalgebra k b) ∧
    (∀ d : Fin b → PowerSeries k,
      (coordinateAxesParameter k b).val * d ∈ coordinateAxesSubalgebra k b) ∧
    @IsFractionRing (coordinateAxesSubalgebra k b) _
      (Fin b → FractionRing (PowerSeries k)) _
      (coordinateAxesSubalgebraFractionMap k b).toRingHom.toAlgebra ∧
    @IsLocalization.Away (coordinateAxesSubalgebra k b) _ (coordinateAxesParameter k b)
      (Fin b → FractionRing (PowerSeries k)) _
      (coordinateAxesSubalgebraFractionMap k b).toRingHom.toAlgebra ∧
    @IsLocalization.Away (Fin b → PowerSeries k) _ (coordinateAxesParameter k b).val
      (Fin b → FractionRing (PowerSeries k)) _
      (coordinateAxesFractionMap k b).toRingHom.toAlgebra ∧
    (@integralClosure (coordinateAxesSubalgebra k b) (Fin b → FractionRing (PowerSeries k))
      _ _ (coordinateAxesSubalgebraFractionMap k b).toRingHom.toAlgebra).carrier =
        Set.range (coordinateAxesFractionMap k b) ∧
    (∃ e : ((Fin b → PowerSeries k) ⧸ (coordinateAxesSubalgebra k b).toSubmodule) ≃ₗ[k]
        ((Fin b → k) ⧸ (⊥ : Subalgebra k (Fin b → k)).toSubmodule),
      (∀ d : Fin b → PowerSeries k,
        e (Submodule.Quotient.mk d) =
          Submodule.Quotient.mk (coordinateAxesConstants k b d)) ∧
      ∀ (p : coordinateAxesSubalgebra k b) (d : Fin b → PowerSeries k),
        e (Submodule.Quotient.mk (p.val * d)) =
          coordinateAxesResidue k b hb p • e (Submodule.Quotient.mk d)) ∧
    Module.finrank k ((Fin b → PowerSeries k) ⧸
      (coordinateAxesSubalgebra k b).toSubmodule) = b - 1 ∧
    (∀ (p : coordinateAxesSubalgebra k b),
      p ∈ RingHom.ker (coordinateAxesResidue k b hb).toRingHom →
      ∀ d : Fin b → PowerSeries k,
        (Submodule.Quotient.mk (p.val * d) :
          (Fin b → PowerSeries k) ⧸ (coordinateAxesSubalgebra k b).toSubmodule) = 0) := by
  sorry

end AlgebraicGeometry
