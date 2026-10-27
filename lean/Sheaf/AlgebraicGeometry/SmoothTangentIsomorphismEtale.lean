/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality
import Sheaf.AlgebraicGeometry.EtaleAtPointFromDifferentials

/-!
# Rational tangent isomorphisms detect etaleness between smooth schemes

Source: Stacks Project, morphisms.tex, Tags 02GU, 02J4 and 01TB; Milne,
Algebraic Groups, printed p.267, before Lemma 13.35
(blueprint: lem-sfb-smooth-tangent-isomorphism-etale).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism of smooth finite-type schemes over an algebraically closed field is etale
if its differential is an isomorphism at every rational point. A point is rational exactly
when the structural residue-field map `pX.residueFieldMap x` is bijective, since the residue
field of `Spec k` is canonically `k`. Its image under a morphism over `k` is rational too.
The existential `he` supplies the residue-field identification required by the canonical
`schemeTangentMap`; it follows already from rationality. This map is residue-field linear,
and hence `k`-linear under the structural identifications. Its bijectivity says precisely
that it is a linear isomorphism. Empty and disconnected schemes and all characteristics
are included.

Source: Stacks Project, Tags 02GU (smooth tangent consequence), 02J4 and 01TB;
Milne, Algebraic Groups, printed p.267, before Lemma 13.35
(blueprint: lem-sfb-smooth-tangent-isomorphism-etale).

Proof for stage 3:
1. At a rational point z, put R = O_z, m = ker(R -> k) and E = Omega_z tensor_R k.
   The universal Kahler presentation (def-weil-pbc-kahler-differentials) and the affine
   description of def-sc-relative-differential-sheaf identify E with Omega_(R/k) tensor_R k.
   Localization sends d(a/s) to s^-1 da - a s^-2 ds and gives the inverse comparison.
   The map c : m/m^2 -> E sends [b] to db tensor 1; its inverse sends da tensor lambda
   to lambda [a - bar(a)]. The latter is well defined by the universal derivation property:
   ab - bar(a)bar(b) equals bar(a)(b-bar(b)) + bar(b)(a-bar(a)) modulo m^2.
   Both composites fix generators, and the formulas commute with the stalk map of f.
2. By lem-sc-rational-tangent-cotangent-duality the tangent map is the dual u* of the
   cotangent map u. Its injectivity makes u surjective by
   lem-sc-dual-map-injective-iff-surjective. If u(b)=0 with b nonzero, a functional nonzero
   on b exists by lem-weil-pbc-vector-space-dual-separates; surjectivity of u* writes it
   as psi composed with u, a contradiction. Thus u, and by step 1 the differential-fibre
   map E_y -> E_x, are isomorphisms.
3. Choose finite-type affine neighbourhoods V=Spec A of y and W=Spec B of x with f(W)
   contained in V (def-weil-finite-type-morphism). Shrink a source affine chart to a
   principal open inside the inverse image of V; adjoining the inverse of its defining
   function preserves finite generation. Both charts are smooth (def-sbc-smooth-morphisms).
   Differentials of finite algebra generators of A span E_y by polynomial differentiation
   and step 1. Select a basis subfamily h_1,...,h_d, allowing d=0. Their pullbacks give a
   basis of E_x. The resulting coordinate maps satisfy h_X = h_Y composed with f.
4. Apply lem-pur-etale-at-point-from-differentials to both coordinate maps to obtain
   etale neighbourhoods V' and W'. On U_x = W' intersect f^-1(V'), the source coordinate
   map remains etale by open-immersion permanence and composition. Cancellation against
   the etale target coordinate map makes U_x -> V' etale, then U_x -> Y etale after
   composing with the open immersion (lem-weil-pbc-etale-composition-cancellation).
5. The union O of these U_x contains all rational points. A finite-type point z has an
   affine neighbourhood where it is closed (lem-sfb-finite-type-field-point-characterization).
   That neighbourhood is locally of finite type over k, and
   lem-weil-pbc-closed-point-residue-field-base makes its residue field structurally k.
   Thus z is rational and lies in O. By lem-sfb-finite-type-points-detect-open, O=X.
   Apply lem-weil-pbc-etale-local-on-source to the covering by the U_x. The empty scheme
   uses the empty cover, and d may vary with the point on a disconnected scheme.
-/
theorem etale_of_bijective_rational_tangentMap
    (k : Type u) [Field k] [IsAlgClosed k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [Smooth pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [Smooth pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    (hdf : ∀ x : X, Function.Bijective (pX.residueFieldMap x).hom →
      ∃ he : Function.Bijective (f.residueFieldMap x).hom,
        Function.Bijective (schemeTangentMap k X Y pX pY f hf x he)) :
    Etale f := by
  sorry

end AlgebraicGeometry
