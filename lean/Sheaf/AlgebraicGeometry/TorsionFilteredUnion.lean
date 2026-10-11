/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf

/-!
# The filtered union of the torsion kernels of an étale sheaf

Source: blueprint `sec-curve-estimates/sk-prop-h2`, lemma-weil-pbc-torsion-filtered-union
(blueprint: lemma-weil-pbc-torsion-filtered-union).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A locally torsion abelian sheaf is the filtered colimit of its kernels of multiplication
by positive integers, ordered by divisibility. The conclusion `IsTorsionAbelianSheaf F`
is the existing definition of precisely this assertion: the transition maps are the kernel
inclusions and the canonical map `colimit.desc D c` to `F` is an isomorphism.

Source: blueprint `sec-curve-estimates/sk-prop-h2`, detailed proof of
lemma-weil-pbc-torsion-filtered-union (blueprint: lemma-weil-pbc-torsion-filtered-union).

Proof for stage 3:
1. By def-pur-abelian-sheaf-kernel, `F[n]` consists of sections killed by `n`.
If `n` divides `m`, a section killed by `n` is killed by `m`, yielding compatible kernel
inclusions. Positive integers ordered by divisibility form a nonempty filtered category:
`lcm(n,m)` is a common upper bound, and parallel arrows in a poset coincide. By
 def-weil-pbc-category-colimit and def-weil-pbc-etale-sheaves, the diagram has a colimit and
the kernel inclusions induce its canonical map to `F`.
2. Each kernel inclusion is monic. Exactness of filtered colimits in the Grothendieck
abelian category of étale abelian sheaves (lem-weil-pbc-abelian-etale-sheaves-grothendieck)
shows that the induced map to the colimit of the constant diagram on `F` is monic.
The index category is connected, so that constant diagram has colimit `F`; this identifies
the induced map with the canonical map of step 1.
3. For any section `s`, local torsion gives a covering on whose members the restrictions
of `s` are killed by positive integers `n`. Each such restriction lifts to `F[n]` and hence
to the colimit. Thus the canonical map is locally surjective, hence epic by
lem-weil-pbc-abelian-sheaf-epi-locally-surjective.
4. A morphism that is both monic and epic in an abelian category is an isomorphism. -/
theorem isTorsionAbelianSheaf_of_isTorsion {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) :
    IsTorsionAbelianSheaf F := by
  sorry

end AlgebraicGeometry.Scheme
