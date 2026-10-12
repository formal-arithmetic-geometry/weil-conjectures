/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Smooth.Basic
import Sheaf.AlgebraicGeometry.UnramifiedAlgebraOverFieldProduct
import Sheaf.RingTheory.ClosedPointDimensionLocalRing
import Sheaf.RingTheory.FlatOfFlatClosedFiber
import Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension
import Sheaf.RingTheory.MiracleFlatness
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.RingTheory.SmoothAtPrimeDifferentialsDimension
import Sheaf.RingTheory.SmoothFibreRegularLocal

/-! # Fibrewise flatness of an unramified smooth chart

Source: Stacks Project, proof of Lemma 07CH.
(blueprint: lem-weil-pbc-unramified-smooth-conormal-chart-flat).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Algebra

/-- Unramified maps from an n-variable polynomial ring into the localized polynomial
extension of a smooth quotient with conormal rank c are flat.

Source: Stacks Project, proof of Lemma 07CH, fibrewise flatness paragraph, using
Tags 00R4, 00T6, and 00R7, https://stacks.math.columbia.edu/tag/07CH.
(blueprint: lem-weil-pbc-unramified-smooth-conormal-chart-flat).

Proof. The split conormal sequence for C = R[x]/(f) identifies Omega(C/R) plus C^c
with C^n; only the existence of the displayed conormal basis is needed here, not its
values on the equations. Polynomial extension by c variables and localization show
that B = C[y]_g is smooth over R and its differential module has rank n at every prime.
For each residue field k of R, both k[z] and T = B tensor_R k are smooth k-algebras
of relative dimension n. Formal unramifiedness survives this base change. At a maximal
ideal m of T, its contraction p in k[z] is maximal by Zariski's lemma. The local rings
T_m and k[z]_p are regular of dimension n: smoothness gives regularity and the rank of
differentials gives the dimension at closed points. The unramified fibre is a finite
product of finite separable fields, so its localization at m has dimension zero.
Miracle flatness, applied to these regular local rings, makes T_m flat over k[z]_p.
Localization and the local criterion for flatness give flatness of T over k[z].
Finally apply the fibrewise flatness criterion to R_p -> R[z]_q -> B_Q at every prime
Q of B. Both algebras are locally of finite presentation over R; B_Q is finite over
itself and flat over R_p by smoothness. Its closed fibre is flat by the preceding
argument. Thus B_Q is flat over R[z]_q, and the local criterion gives the asserted
flatness. Empty fibres and the zero ring contribute no primes and cause no exception. -/
theorem flat_of_unramified_smooth_conormal_chart
    (R : Type u) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    [Smooth R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))]
    (b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent)
    (g : MvPolynomial (Fin c) (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))
    (θ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g) :
    letI := θ.toRingHom.toAlgebra
    letI : Module (MvPolynomial (Fin n) R) (Localization.Away g) :=
      θ.toRingHom.toAlgebra.toModule
    FormallyUnramified (MvPolynomial (Fin n) R) (Localization.Away g) →
      Module.Flat (MvPolynomial (Fin n) R) (Localization.Away g) := by
  sorry

end Algebra
