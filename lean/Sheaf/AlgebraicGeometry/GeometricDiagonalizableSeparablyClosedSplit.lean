/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AlgClosedGroupEmbeddingExistenceDescent
import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality

/-! # Geometrically diagonalizable groups over separably closed fields

Source: Conrad, Reductive group schemes, Appendix B.4, opening paragraph, printed p.297,
and Lemma B.1.5, printed pp.283--284
(blueprint: lem-sfb-geometric-diagonalizable-separably-closed-split).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite-type affine group over a separably closed field is split diagonalizable
if it becomes diagonalizable over an algebraically closed extension, including a
transcendental extension and character groups with torsion.
Source: Conrad, Reductive group schemes, Appendix B.4, printed p.297, and
Lemma B.1.5, printed pp.283--284
(blueprint: lem-sfb-geometric-diagonalizable-separably-closed-split).

Proof plan:
1. Let K be the relative algebraic closure of k in E. It is an algebraic closure
   by lem-weil-pbc-relative-algebraic-closure-algclosed. The coordinate Hopf algebra
   of H (lem-sfb-affine-group-coordinate-hopf), the affine tensor-product formula
   (lem-weil-pbc-fibre-product-affine-spectra), and finite-type base change
   (lem-sfb-finite-type-composition-base-change) identify (H_K)_E with H_E.
   The tensor reassociation a tensor (b tensor c) maps to ab tensor c and respects
   coproduct, counit and antipode.
2. Choose finitely many generators of N₀. The surjection Z^r to N₀ induces the
   surjective Hopf map E[Z^r] to E[N₀] on basis monomials. Its spectrum is a closed
   group embedding by lem-sfb-hopf-spectrum-functor and def-weil-closed-immersion.
   The torus clause of lem-sfb-diagonalizable-group-geometric-criteria identifies
   D_K(Z^r) with G_m^r. The canonical scalar-extension map identifies its extension
   to E with D_E(Z^r). Compose to embed (H_K)_E into this torus; r=0 is allowed.
3. By lem-sfb-algclosed-group-embedding-existence-descent, some closed embedding
   H_K into G_m^r exists over K. Thus H is of multiplicative type in the sense of
   lem-sfb-multiplicative-character-antiduality. No specified embedding is descended.
4. The finite separable splitting clause of lem-sfb-multiplicative-character-antiduality
   gives a finite separable extension L/k, a finitely generated abelian group N,
   and a group isomorphism H_L with D_L(N), with no smoothness assumption.
5. By lem-pc-sepclosed-finite-sep-trivial the map k to L is an isomorphism. Transport
   the splitting along its inverse, using the scalar maps a tensor c maps to ac
   and a e_m maps to a e_m. These respect all Hopf operations. Invert the resulting
   group isomorphism to obtain D_k(N) to H, also for the zero group and for mu_p. -/
theorem geometric_diagonalizable_separably_closed_split
    (k E : Type u) [Field k] [IsSepClosed k] [Field E] [Algebra k E] [IsAlgClosed E]
    (H : Grp (Over (Spec (.of k)))) [IsAffineHom H.X.hom]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    (N₀ : AddCommGrpCat.{u}) [AddGroup.FG N₀]
    (h : Nonempty
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k E)))).mapGrp.obj H ≅
        ringDiagonalizableGroup E N₀)) :
    ∃ N : AddCommGrpCat.{u}, AddGroup.FG N ∧ Nonempty (ringDiagonalizableGroup k N ≅ H) := by
  sorry

end AlgebraicGeometry
