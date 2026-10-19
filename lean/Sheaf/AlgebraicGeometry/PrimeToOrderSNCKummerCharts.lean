/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

import Sheaf.AlgebraicGeometry.RegularBoundaryDivisorialChart
import Sheaf.AlgebraicGeometry.InvertibleKummerChartLogRegular
import Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks
import Sheaf.TraceFormula.LogRegularDivisorialStructure
import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.DiagonalRootInvariantMonoidAlgebra
import Sheaf.DeligneLaumon.SncParameterRootQuotient

/-!
# Kummer charts on finite normalizations of invertible-order torsors

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose IX Proposition 2.1(iii)
and its proof, printed pp. 133--134; VI 2.1--2.2, pp. 71--72
(blueprint: lem-per-prime-to-order-snc-kummer-charts).

The integral structure and the canonical finite function-field extension of the connected
cover are unpacked existentially. Finiteness of its normalization is an assumption in the
ensuing implication. The base log structure is specified by an isomorphism with the actual
divisorial presheaf compatible with its structural inclusion. Charts and their canonical
scheme comparison use the published `FSLogChart` interface. Multiplicative notation uses
`1` for zero and powers for positive integer multiples.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Invertible-order torsors over a strict-normal-crossings complement have sharp Kummer
charts on their finite normalization. Source: ILO IX 2.1(iii), pp. 133--134, and VI 2.1--2.2,
pp. 71--72 (blueprint: lem-per-prime-to-order-snc-kummer-charts).

The generic-morphism equation fixes the function-field algebra induced by the cover.
The finite-normalization hypothesis is retained as the premise `_hb`. No excellence or
log-regularity conclusion is asserted. Pointed lifts commute with the chart morphism,
and the two specified maps to geometric characteristic monoids are bijective.

Proof plan:
1. Apply `lem-per-regular-boundary-divisorial-chart` at the chosen geometric base point.
   Obtain the parameter chart P = N^r, sharp at that point, allowing r = 0. The regular
   base is normal; the connected finite etale cover is integral, and its generic fibre
   gives the displayed canonical finite function-field extension.
2. `lem-per-snc-parameter-root-quotient`, with n = |G|, gives pointed etale refinements
   with the same parameters and coordinate ring C = B^H, where
   B = A[x_1,...,x_r]/(x_i^n-t_i). Finiteness of the normalization is exactly `_hb`.
3. `lem-per-diagonal-root-invariant-monoid-algebra` identifies C with
   A tensor_{Z[P]} Z[Q], where Q is the invariant exponent lattice intersected with
   (1/n)N^r. The monoids are fs sharp, P injects into Q, nQ lies in P, and the group
   cokernel is finite killed by the invertible n.
4. `lem-trf-associated-log-universal-stalks` supplies the associated log structure of
   Q and its compatible morphism to the base. The affine-spectrum fibre-product
   identification `lem-weil-pbc-fibre-product-affine-spectra` makes the canonical chart
   comparison an isomorphism, hence etale.
5. `lem-per-invertible-kummer-chart-log-regular` makes these local log schemes log
   regular. Their triviality locus is precisely the inverse image of the complement:
   c_q^n is a product of the parameters. `lem-trf-log-regular-divisorial-structure`
   identifies each local log structure with the same divisorial subsheaf.
6. Globally take O_Z intersect j_*O_{b^{-1}V}^units. The local identifications agree
   through their structural inclusions, so this is one fs log structure N. Pullback
   of functions gives its log morphism over the canonical normalization map.
7. At the selected points all parameters are in the maximal ideal. Every nonidentity
   element of Q has a nonunit structural image, since its n-th power is a nonconstant
   parameter monomial. The associated-log stalk pushout therefore identifies Q with
   the characteristic monoid; P has the analogous property from step 1. This proves
   all chart clauses. For the empty boundary r = 0 and both sharp monoids are trivial.
-/
theorem primeToOrder_snc_kummerCharts
    (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    (_hY : IsRegularScheme Y) (T : Y.IdealSheafData)
    (_hT : IsStrictNormalCrossingsBoundary T)
    (M : EtaleLogStructure Y)
    (eM : M.monoidSheaf.obj ≅ divisorialLogPresheaf (Scheme.Opens.ι T.support.compl))
    (_heM : eM.hom ≫ divisorialStructuralMap (Scheme.Opens.ι T.support.compl) = M.alpha)
    (hM : M.IsFineSaturated)
    (G : Type v) [Group G] [Finite G]
    (_hG : IsUnit (Nat.card G : Γ(Y, ⊤)))
    (C : Scheme.GaloisCoverAction G (Scheme.Opens.toScheme T.support.compl))
    [ConnectedSpace C.Z] :
    ∃ (_ : IsIntegral C.Z) (_ : Algebra Y.functionField C.Z.functionField),
      FiniteDimensional Y.functionField C.Z.functionField ∧
      Y.fromSpecOfAlgebraFunctionField C.Z.functionField =
        C.Z.fromSpecFunctionField ≫ C.π ≫ (Scheme.Opens.ι T.support.compl) ∧
      ∀ (_hb : IsFinite (Y.fromNormalizationIn C.Z.functionField)),
        ∃ (hZ : IsLocallyNoetherian (Y.normalizationIn C.Z.functionField))
          (N : EtaleLogStructure (Y.normalizationIn C.Z.functionField))
          (hN : N.IsFineSaturated)
          (f : EtaleLogHom
            ⟨Y.normalizationIn C.Z.functionField, hZ, N, hN⟩
            ⟨Y, inferInstance, M, hM⟩),
          f.base = Y.fromNormalizationIn C.Z.functionField ∧
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (z : Spec (.of Ω) ⟶ Y.normalizationIn C.Z.functionField),
            ∃ (c : FSLogChart f)
              (w : (Scheme.pointSmallEtale z).fiber.obj c.V)
              (y : (Scheme.pointSmallEtale
                (z ≫ Y.fromNormalizationIn C.Z.functionField)).fiber.obj c.W),
              w.left ≫ c.map = y.left ∧
              (∀ p : c.P, IsUnit p → p = 1) ∧
              (∀ q : c.Q, IsUnit q → q = 1) ∧
              Function.Bijective (fun p : c.P ↦ Associates.mk
                (M.toEtalePrelogStructure.germ
                  (z ≫ Y.fromNormalizationIn C.Z.functionField) c.W y (c.chartY p))) ∧
              Function.Bijective (fun q : c.Q ↦ Associates.mk
                (N.toEtalePrelogStructure.germ z c.V w (c.chartX q))) ∧
              Function.Injective c.g ∧
              (∀ q : c.Q, ∃ n : ℕ, 0 < n ∧ ∃ p : c.P, c.g p = q ^ n) ∧
              Function.Injective c.groupMap ∧ Finite c.cokernel ∧
              (∃ n : ℕ, 0 < n ∧ (∀ a : c.cokernel, a ^ n = 1) ∧
                ∀ t : c.W.left, IsUnit (n : c.W.left.presheaf.stalk t)) ∧
              Etale c.comparison := by
  sorry

end AlgebraicGeometry.Scheme
