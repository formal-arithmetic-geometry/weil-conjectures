/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Sheaf.AlgebraicGeometry.EtaleAtlasPresentation
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.AlgebraicGeometry.FiniteFlatAffineRelationQuotient

/-! # Quasi-separated algebraic spaces with an étale field atlas

Source: Stacks Project, Properties of Spaces, Tag 03DZ (lemma-point-like-spaces),
including the displayed invariant subfield in its proof
(blueprint: lem-sfb-pointlike-quasiseparated-space-field).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- An absolutely quasi-separated algebraic space with a surjective étale field atlas
is the spectrum of a subfield, with the atlas induced by inclusion and finite separable
extension. The presheaf isomorphism is over `S`, since Yoneda is taken on `Over S`.
Source: Stacks Project, Properties of Spaces, Tag 03DZ (lemma-point-like-spaces).
(blueprint: lem-sfb-pointlike-quasiseparated-space-field).

Proof:
1. Put U = Spec L and R = U ×_Y U. By lem-a1-etale-atlas-presentation the representing
   scheme R has surjective étale projections s,t to U, defines an equivalence relation,
   and presents Y as the fppf sheaf quotient U/R, with its specified atlas map.
2. Apply def-sfb-space-absolute-quasi-separated to the two affine schemes U,U and their
   atlas maps. Their represented fibre product R is quasi-compact. This uses absolute
   quasi-separatedness and puts no separation or finite-type condition on S.
3. Apply lem-weil-pbc-etale-fibre-discrete-separable-points to s over the unique point
   of U. Thus R is the disjoint union of singleton opens Spec L_i, each finite separable
   over L via s. Quasi-compactness makes the index set finite. Apply the same lemma to t
   to obtain finite separability of the same residue fields via t. The diagonal section
   U → R makes this finite index set nonempty.
4. By lem-weil-pbc-finite-affine-coproduct-spectrum, R = Spec (∏ i, L_i). Coordinate
   bases make its algebra finite over L under both structure maps, so s,t are finite
   by def-weil-finite-integral-morphism. They are flat and locally of finite presentation
   by def-weil-etale-morphism, hence finite locally free by def-pc-finite-locally-free.
5. Apply lem-a1-finite-flat-affine-relation-quotient over S. It identifies U/R with the
   spectrum of C = {a ∈ L | s♯(a) = t♯(a)}, and the quotient map with the inclusion map.
   This subring is closed under inversion of nonzero elements, since ring homomorphisms
   preserve inverses of units. Thus C is a subfield k. The two quotient identifications
   give the isomorphism over S and the asserted compatibility with the original q.
6. Apply lem-weil-pbc-etale-fibre-discrete-separable-points to the resulting étale map
   Spec L → Spec k at the unique point of Spec k. Its unique residue field is L, so L/k
   is finite and every element satisfies a separable polynomial. Its minimal polynomial
   divides that polynomial and is separable, proving the final two clauses. -/
theorem pointlike_quasiseparated_space_field {S : Scheme.{u}} (Y : AlgebraicSpace S)
    (L : Type u) [Field L] (a : Spec (CommRingCat.of L) ⟶ S)
    (q : yoneda.obj (Over.mk a) ⟶ Y.obj.obj)
    (hq : IsEtale q) (hsur : IsSurjective q) (hY : IsAbsolutelyQuasiSeparated Y) :
    ∃ (k : Subfield L) (b : Spec (CommRingCat.of k) ⟶ S)
      (h : Spec.map (CommRingCat.ofHom k.subtype) ≫ b = a)
      (e : Y.obj.obj ≅ yoneda.obj (Over.mk b)),
      q ≫ e.hom = yoneda.map (Over.homMk (Spec.map (CommRingCat.ofHom k.subtype)) h) ∧
        FiniteDimensional k L ∧ Algebra.IsSeparable k L := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
