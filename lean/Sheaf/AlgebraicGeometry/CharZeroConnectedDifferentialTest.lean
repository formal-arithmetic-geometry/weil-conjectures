/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import Sheaf.AlgebraicGeometry.LinearGroupSchemes
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.EtaleComponents
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.GroupSchemeIdentityDualUnramified
import Mathlib.RingTheory.Etale.Field

/-! # Connectedness detected by representations with zero differential

Source: Milne, Algebraic Groups (2017), Note 9.50, pp.184-185, Proposition 10.31,
p.196, Cartier's theorem 3.23, p.71, and Proposition 10.15, pp.190-191.
(blueprint: lem-sfb-charzero-connected-differential-test)

The representation is written on `k^m` using the existing `RationalHom` interface.
Every finite-dimensional vector space has this form after choosing a basis; an empty
index type includes the zero vector space. The differential is the existing tangent
map in matrix coordinates, and triviality is tested on every algebra, not only fields.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.GeneralLinearGroup

/-- An affine group scheme of finite type over a characteristic-zero field is geometrically
connected if and only if each finite-dimensional rational representation whose differential
vanishes is trivial on points over every commutative algebra. No algebraic closedness of the
base field or nonzero dimension of the representation is assumed.

Source: Milne, Algebraic Groups (2017), Note 9.50, pp.184-185, Proposition 10.31,
p.196, Cartier 3.23, p.71, and Proposition 10.15, pp.190-191.
(blueprint: lem-sfb-charzero-connected-differential-test)

Proof:
1. If H is geometrically connected, it is connected by
   lem-weil-geometrically-connected-algebraic-closure and smooth by
   lem-sfb-cartier-characteristic-zero-smooth. For a nonzero representation choose a basis.
   The identity subgroup of GL is closed, cut out by x_ij - delta_ij, by
   def-sc-general-linear-group and lem-weil-pbc-closed-immersion-affine-cover-criterion.
   Its tangent space is zero. The zero differential therefore factors uniquely through
   the identity subgroup by lem-sfb-charzero-lie-detects-factorization. This gives the
   identity on all algebra points. In dimension zero the automorphism group is a singleton.
2. For the converse use lem-sfb-algebraic-scheme-etale-components to form q : H -> P.
   Affineness implies separatedness by lem-weil-pbc-affine-source-morphism-separated.
   Functoriality and the product and unit comparisons give P its group structure and
   make q a homomorphism. Its nonempty fibres make q surjective. P is finite etale;
   by def-weil-finite-integral-morphism its coordinate algebra B is finite-dimensional,
   hence also finitely generated as an algebra.
3. By def-weil-etale-morphism and lem-sfb-group-scheme-identity-dual-unramified,
   Lie(P) is zero. The faithful regular representation rho of P on B from
   lem-sfb-finite-group-faithful-regular-matrices has surjective coordinate map.
   B is nonzero because P has an identity section. By the composition formula in
   lem-sfb-affine-group-lie-tangent-calculus, r = rho composed with q has zero differential.
4. The assumed test makes r trivial over every algebra. Faithfulness of rho on all
   algebra points forces q to take every point to the identity. Evaluating on the
   universal point with algebra k[H] proves that q is the constant identity morphism.
5. Surjectivity makes P have only its identity point. By
   lem-weil-pbc-etale-algebra-over-field-product, B is a finite product of separable
   fields. Exactly one factor is possible; its identity section to k forces that
   factor to be k itself. Thus P is Spec k, and the nonempty geometrically connected
   fibre assertion of lem-sfb-algebraic-scheme-etale-components applies to all of H. -/
theorem geometricallyConnected_iff_zero_differential_representations_trivial
    {k : Type u} [Field k] [CharZero k] (H : Over (Spec (.of k))) [GrpObj H]
    [IsAffine H.left] [LocallyOfFiniteType H.hom] [QuasiCompact H.hom] :
    GeometricallyConnected H.hom ↔
      ∀ (m : Type u) [Fintype m] [DecidableEq m] (r : RationalHom H m) [IsMonHom r],
        r.differential = 0 →
          ∀ (A : Type u) [CommRing A] [Algebra k A] (h : AlgebraicGeometry.points H A),
            r.points A h = 1 := by
  sorry

end AlgebraicGeometry.GeneralLinearGroup
