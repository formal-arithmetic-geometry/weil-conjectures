/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.Dimension
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.FiniteTypeFibreImageDimensionBounds

/-!
# Finite kernels and equal-dimensional abelian varieties

Source: Milne, Abelian Varieties, Chapter I, Proposition 7.1(c) implies (d), printed p.32;
Stacks Project, Morphisms, Tag 02KB, `lemma-finite-flat`
(blueprint: lem-sfb-finite-kernel-equal-dimension-isogeny).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A homomorphism of equal-dimensional abelian varieties over an algebraically closed field
with finite scheme-theoretic kernel is surjective and finite locally free.

Source: Milne, Abelian Varieties I, Proposition 7.1(c) implies (d), printed p.32, and
Stacks Project, Morphisms, Tag 02KB, `lemma-finite-flat`
(blueprint: lem-sfb-finite-kernel-equal-dimension-isogeny).

Proof:
1. Properness of A and separatedness of B give the closed scheme-theoretic image Z,
   proper over k, and a proper surjection A -> Z (pqf-lem-image-proper). The abelian-variety
   characterization makes B irreducible (lem-sc-abelian-variety-characterization).
2. Every scheme fibre has dimension at most zero by translation of the finite kernel
   (lem-sfb-finite-kernel-group-fibres). The fibres over Z agree with the corresponding
   fibres over B, since a closed immersion identifies their residue fields.
3. Use lem-pc-scheme-dimension-local-rings to pass to topological dimension and
   lem-kun-dimension-finite-type for finiteness. The fibre/image dimension bound
   (lem-zl-finite-type-fibre-image-dimension-bounds) gives dim A <= dim Z. If Z were a
   proper closed subset of B, appending B to a maximal chain in Z would give
   dim Z + 1 <= dim B, contradicting dim A = dim B. Hence f is surjective.
4. Surjectivity and the finite kernel make f an isogeny (def-sc-isogeny), so f is finite
   and flat by lem-sc-isogeny-degree.
5. B is locally Noetherian by lem-weil-pbc-finite-type-over-noetherian. Finiteness of f
   gives local finite type, hence local finite presentation by pqf-lem-lft-fp-locnoeth.
   Together with finite flatness this is def-pc-finite-locally-free. -/
theorem surjective_and_isFiniteLocallyFree_of_finite_ker_of_dim_eq
    {k : Type u} [Field k] [IsAlgClosed k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
    [IsAbelianVariety A] [IsAbelianVariety B]
    (f : A ⟶ B) [IsMonHom f]
    (hdim : A.left.dim = B.left.dim) [IsFinite (GrpObj.ker f).hom] :
    Surjective f.left ∧ f.left.IsFiniteLocallyFree := by
  sorry

end AlgebraicGeometry
