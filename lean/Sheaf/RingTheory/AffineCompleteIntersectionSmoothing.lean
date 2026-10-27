/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.AlgebraicGeometry.GlobalCompleteIntersectionEquidimensional
import WeilConjectures.RingTheory.GlobalCompleteIntersectionLocalRegularSequence
import WeilConjectures.RingTheory.RegularSequenceFlatClosedFiber
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Equiv
import WeilConjectures.RingTheory.StandardSmoothDimensionAtPoints
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Polynomial smoothings of affine complete intersections

Source: Stacks Project, examples-defos.tex, Tag 0E7V, lemma-smoothing-affine-lci,
and the fibre-dimension assertion in Tag 0E7X, lemma-smoothing-at-lci-point
(blueprint: lem-sfb-affine-global-ci-smoothing).

The auxiliary constructions spell out the displayed polynomials and their quotients.
The generic-fibre map is the localization of the structure map, and the special-fibre
isomorphism is required to fix the polynomial coordinates.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MvPolynomial.AffineCISmoothing

variable {k : Type u} [Field k] {N c : ℕ}

/-- The equation `f_j + a_{0j} + ∑ a_{ij} x_i`, with row zero the constant term
and row `i.succ` the coefficient of variable `i`.
Source: Stacks Project, Tag 0E7V, displayed polynomial construction
(blueprint: lem-sfb-affine-global-ci-smoothing). -/
def equation (f : Fin c → MvPolynomial (Fin N) k)
    (a : Fin (N + 1) → Fin c → PowerSeries k) (j : Fin c) :
    MvPolynomial (Fin N) (PowerSeries k) :=
  MvPolynomial.map (PowerSeries.C (R := k)) (f j) + MvPolynomial.C (a 0 j) +
    ∑ i : Fin N, MvPolynomial.C (a i.succ j) * MvPolynomial.X i

/-- The specified quotient `Q = k[[t]][x₁,…,x_N]/(g₁,…,g_c)`.
Source: Stacks Project, Tag 0E7V, displayed polynomial construction
(blueprint: lem-sfb-affine-global-ci-smoothing). -/
abbrev Quotient (f : Fin c → MvPolynomial (Fin N) k)
    (a : Fin (N + 1) → Fin c → PowerSeries k) :=
  MvPolynomial (Fin N) (PowerSeries k) ⧸ Ideal.span (Set.range (equation f a))

/-- The special fibre `Q/tQ`, with its induced `k`-algebra structure.
Source: Stacks Project, Tag 0E7V, the reduction modulo `t`
(blueprint: lem-sfb-affine-global-ci-smoothing). -/
abbrev ClosedFiber (f : Fin c → MvPolynomial (Fin N) k)
    (a : Fin (N + 1) → Fin c → PowerSeries k) :=
  Quotient f a ⧸ Ideal.span
    ({algebraMap (PowerSeries k) (Quotient f a) PowerSeries.X} : Set (Quotient f a))

/-- The class of `x_i` in `Q/tQ`, using the two specified quotient maps.
Source: Stacks Project, Tag 0E7V, the coordinate identification of the closed fibre
(blueprint: lem-sfb-affine-global-ci-smoothing). -/
def closedCoordinate (f : Fin c → MvPolynomial (Fin N) k)
    (a : Fin (N + 1) → Fin c → PowerSeries k) (i : Fin N) : ClosedFiber f a :=
  Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (MvPolynomial.X i))

/-- The canonical map `K = k[[t]][1/t] → Q[1/t]`, obtained by localizing `k[[t]] → Q`.
Source: Stacks Project, Tag 0E7V, generic-fibre paragraph
(blueprint: lem-sfb-affine-global-ci-smoothing). -/
def genericMap (f : Fin c → MvPolynomial (Fin N) k)
    (a : Fin (N + 1) → Fin c → PowerSeries k) :
    Localization.Away (PowerSeries.X : PowerSeries k) →+*
      Localization.Away (algebraMap (PowerSeries k) (Quotient f a) PowerSeries.X) :=
  IsLocalization.Away.map _ _ (algebraMap (PowerSeries k) (Quotient f a)) PowerSeries.X

/-- The affine morphism `Spec Q → Spec k[[t]]` of the specified deformation.
Source: Stacks Project, Tag 0E7V, polynomial smoothing construction
(blueprint: lem-sfb-affine-global-ci-smoothing). -/
def structureMap (f : Fin c → MvPolynomial (Fin N) k)
    (a : Fin (N + 1) → Fin c → PowerSeries k) :
    Spec (.of (Quotient f a)) ⟶ Spec (.of (PowerSeries k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (Quotient f a)))

/-- A nonzero complete intersection in the specified `N` variables and `c` equations
admits the displayed linear perturbation over `k[[t]]`: it is flat, has the specified
coordinate-preserving special fibre, has smooth generic fibre, and has pure geometric
fibre dimension `N-c`.
Source: Stacks Project, examples-defos.tex, Tag 0E7V, lemma-smoothing-affine-lci;
Tag 0E7X, lemma-smoothing-at-lci-point, expected fibre dimension
(blueprint: lem-sfb-affine-global-ci-smoothing).

Proof plan, following the node's ten steps:
1. The power-series and finite-type Noetherian theorems make `R = k[[t]]` and
   `R[x₁,…,x_N]` Noetherian. Power-series domain and local-ring results, together
   with lowest-coefficient factorization, give precisely the primes `(0)` and `(t)`
   of `R`; inverting `t` gives the field `K`.
2. Apply `lem-sfb-generic-linear-perturbation-jacobian` to obtain a nonzero polynomial
   `H` in the `c(N+1)` coefficient variables. For `c=0`, use `H=1`.
3. Choose `D≥2` larger than every monomial exponent of `H`. Substitute successive
   powers `t^(D^l)` for its coefficient variables. Distinct monomials give distinct
   powers of `t` by base-`D` expansion, so `H(a)≠0`, over finite fields as well.
4. Reduce the displayed equations modulo `t` to identify `Q/tQ` with the original
   quotient, fixing scalars and all coordinates. Localizing gives the displayed
   `K`-presentation. The perturbation lemma gives smoothness and full-rank minors.
5. Polynomial projection is flat (`lem-nagata-polynomial-projection-flat` and
   `lem-weil-pbc-flat-ring-map-iff-flat-affine`). Localizing at a prime over `(t)`
   gives a flat local map of Noetherian local rings by
   `lem-weil-pbc-flat-local-ring-maps`; its closed fibre is the corresponding
   localization of `k[x₁,…,x_N]`.
6. Use `lem-weil-pbc-global-complete-intersection-local-regular-sequence` and
   `lem-weil-pbc-grothendieck-regular-sequence-flat` to obtain flatness of the
   localized quotient at each prime over `(t)`. Quotienting commutes with
   localization: the mutually inverse fraction maps send `u/v` to its class.
7. At primes over `(0)`, flatness is `lem-weil-pbc-module-over-field-flat` over `K`.
   Apply `lem-weil-pbc-flat-map-local-criterion` to conclude `R → Q` is flat.
8. On each nonvanishing Jacobian minor `δ`, adjoin `y` with `yδ=1`. The new
   Jacobian determinant is `δ²` up to sign. The standard-smooth dimension theorem
   (`lem-weil-pbc-standard-smooth-over-field-dimension-at-points`) gives dimension
   `(N+1)-(c+1)=N-c` at every point. Neighbourhoods in these open charts compute
   the same local dimension as in the whole generic fibre. For `c=0`, use `δ=1`.
9. The special fibre has constant local dimension `N-c` by
   `lem-weil-pbc-global-complete-intersection-equidimensional`. Apply
   `lem-weil-pbc-dimension-at-point-field-extension` to it and the generic fibre
   to obtain this local dimension on every geometric fibre.
10. Finite-type Noetherianity makes the geometric fibres locally Noetherian.
    Apply `lem-sbc-constant-local-dimension-components` to conclude pure dimension.
    Empty fibres satisfy this vacuously. The coefficient family and equation
    sequence can both be empty; no hypothesis on perfection or characteristic is used.
-/
theorem exists_smoothing (k : Type u) [Field k] (N c : ℕ) (hc : c ≤ N)
    (f : Fin c → MvPolynomial (Fin N) k)
    [Nontrivial (MvPolynomial (Fin N) k ⧸ Ideal.span (Set.range f))]
    (hdim : topologicalKrullDim
      (PrimeSpectrum (MvPolynomial (Fin N) k ⧸ Ideal.span (Set.range f))) =
        ((N - c : ℕ) : WithBot ℕ∞)) :
    ∃ a : Fin (N + 1) → Fin c → PowerSeries k,
      (∀ (i : Fin (N + 1)) (j : Fin c),
        a i j ∈ Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) ∧
      (algebraMap (PowerSeries k) (Quotient f a)).Flat ∧
      (∃ e : ClosedFiber f a ≃ₐ[k]
          (MvPolynomial (Fin N) k ⧸ Ideal.span (Set.range f)),
        ∀ i : Fin N, e (closedCoordinate f a i) = Ideal.Quotient.mk _ (MvPolynomial.X i)) ∧
      Smooth (Spec.map (CommRingCat.ofHom (genericMap f a))) ∧
      ∀ y : Spec (.of (PowerSeries k)),
        Scheme.IsPureDimension
          (pullback (structureMap f a)
            (Spec.map (CommRingCat.ofHom
              (algebraMap ((Spec (.of (PowerSeries k))).residueField y)
                (AlgebraicClosure ((Spec (.of (PowerSeries k))).residueField y)))) ≫
              (Spec (.of (PowerSeries k))).fromSpecResidueField y)) (N - c) := by
  sorry

end MvPolynomial.AffineCISmoothing
