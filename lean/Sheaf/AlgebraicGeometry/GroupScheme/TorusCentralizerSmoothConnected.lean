/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q142
-/
module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Basic
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.ConstantSourceClosedFactorizationLocus
import Sheaf.AlgebraicGeometry.TorusFixedSchemeSmooth
import Sheaf.AlgebraicGeometry.GroupScheme.TorusCommutingPointCommonBorel
import Sheaf.AlgebraicGeometry.TorusRegularSemisimpleElement
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-! # Smoothness and geometric connectedness of torus centralizers

Source: Milne, Algebraic Groups (2017), Proposition 1.92, printed pp.33--34,
Corollary 13.10, printed p.257, and Theorem 17.38, printed p.363
(blueprint: lem-sfb-torus-centralizer-smooth-connected).

The centralizer is characterized on every algebra, using the recorded condition
that tests commutation after every algebra extension. Geometric connectedness is
written as connectedness after the recorded algebraic-closure base change.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The centralizer of any torus in a smooth geometrically connected affine group
of finite type is represented by a smooth geometrically connected closed subgroup.
Source: Milne, Proposition 1.92, pp.33--34, Corollary 13.10, p.257,
and Theorem 17.38, p.363 (blueprint: lem-sfb-torus-centralizer-smooth-connected).

Proof:
1. Write G = Spec R and T = Spec D. By
   lem-weil-pbc-fibre-product-affine-spectra, their products are spectra of tensor
   products. Finite generators in the two factors show finite type, and the
   surjective multiplication map R tensor R to R makes the diagonal closed
   (def-weil-closed-immersion), hence G separated (def-weil-proper-morphism).
   The same calculation applies to T and G times G.
2. Apply lem-sfb-constant-source-closed-factorization-locus to the family
   (t,g) mapping to (t,gtg^-1), with target G times G and its closed diagonal.
   It gives a closed C in G. On Spec A the commuting tests are equivalent to
   diagonal factorization: test the universal T-point over A tensor D, and
   use def-weil-affine-spectrum to identify equality of the coordinate maps.
3. The identity, products and inverses satisfy these commuting tests on every
   algebra extension. Thus the represented subfunctor is a subgroup, giving
   IsClosedSubgroupScheme (def-sc-group-scheme-subgroup). Its coordinate algebra
   R/I is finitely generated, so C is affine of finite type
   (def-weil-finite-type-morphism).
4. Conjugation by T is a group-scheme action (def-sc-group-scheme). Its fixed
   subfunctor equals this centralizer on all algebras. Therefore
   lem-sfb-torus-fixed-scheme-smooth applied to G and C proves smoothness.
5. Extend to K = algebraic closure of k. Smoothness persists by
   lem-pc-proper-base-change, and G_K is connected by hypothesis. The universal
   property in def-pc-fibre-product identifies C_K with the centralizer of T_K:
   every algebra extension of a K-algebra inherits the compatible K-structure.
   Tensoring generators preserves affine finite type.
6. For each c in C_K(K), lem-sfb-torus-commuting-point-common-borel supplies a
   smooth connected solvable Borel B containing T_K and c. By
   lem-sfb-torus-regular-semisimple-element choose s in T_K(K) whose centralizer
   functor in B equals that of T_K, on every algebra. By
   lem-sfb-solvable-semisimple-centralizer-connected this centralizer D is
   connected. Its map to G_K factors through C_K by the same commuting tests,
   and its image contains the identity and c.
7. For any clopen decomposition of C_K put the identity in the first part.
   Each connected D from step 6 has image in that part, so the other part has
   no K-points (def-weil-connected-scheme). Closed points in that part are dense
   by lem-sc-lft-over-field-jacobson-space and are K-points by clause (1) of
   lem-wf-affine-nullstellensatz-vanishing. Thus the other part is empty.
   This proves connectedness of C_K, without assuming reductivity, maximality
   of T, or finiteness of the collection of Borels. -/
theorem exists_torus_centralizer_smooth_connected {k : Type u} [Field k]
    (G T : Grp (Over (Spec (.of k))))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [IsAffine T.X.left] [LocallyOfFiniteType T.X.hom] [QuasiCompact T.X.hom]
    [Smooth G.X.hom]
    [ConnectedSpace ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj G).X.left]
    (i : T ⟶ G) (hi : IsClosedSubgroupScheme i.hom.hom)
    (hT : MultiplicativeType.IsTorus T) :
    ∃ (C : Grp (Over (Spec (.of k)))) (j : C ⟶ G),
      IsClosedSubgroupScheme j.hom.hom ∧ IsAffine C.X.left ∧
      LocallyOfFiniteType C.X.hom ∧ QuasiCompact C.X.hom ∧ Smooth C.X.hom ∧
      ConnectedSpace ((MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj C).X.left ∧
      ∀ (A : Type u) [CommRing A] [Algebra k A],
        ReductiveTorusCentralizer.centralizerPoints i A =
          Set.range (fun c : StandardGroupSchemes.affine k A ⟶ C.X ↦ c ≫ j.hom.hom) := by
  sorry

end AlgebraicGeometry
