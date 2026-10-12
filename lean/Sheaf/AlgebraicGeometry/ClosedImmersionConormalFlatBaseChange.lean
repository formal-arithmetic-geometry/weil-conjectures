/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.ClosedImmersionConormalFunctorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Conormal sheaves under flat base change
Source: Stacks Project, Morphisms, Lemma 0473 (morphisms-lemma-conormal-functorial-flat),
case of closed immersions (blueprint: lem-weil-pbc-closed-immersion-conormal-flat-base-change).
-/

@[expose] public section

universe uc
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
/-- For a cartesian square of closed immersions, the canonical conormal map is an
 epimorphism; if the ambient morphism is flat, it is an isomorphism. The canonical map
 is the unique map supplied by `closedImmersion_conormal_functorial`.

Source: Stacks Project, Morphisms, Lemma 0473 (lemma-conormal-functorial-flat),
closed-immersion case; Schemes, Lemma 01JU (lemma-fibre-product-immersion), assertion (1)
(blueprint: lem-weil-pbc-closed-immersion-conormal-flat-base-change).
Proof, following the node's three steps:
1. Use lem-weil-pbc-closed-immersion-conormal-functorial to obtain the canonical map.
2. At each point of `Z`, choose compatible affine opens `U = Spec R` in `X` and
   `U' = Spec R'` in `X'`. By lem-weil-pbc-closed-immersion-affine-cover-criterion,
   the inverse image of `U'` is `Spec (R'/I')`. Restrict the cartesian square using
   lem-weil-pbc-open-preimage-fibre-product and lem-weil-pbc-cartesian-square-pasting.
   Then lem-weil-pbc-quotient-base-change-closed-immersion-ideal gives the inverse image
   of `U` as `Spec (R/I)` with `I = I'R`. By lem-weil-pbc-module-pullback-affine-sections
   and the affine characterization in the functoriality node, `c` is the canonical
   map from `(I'/I'^2) tensor R` to `I/I^2` on these charts.
3. By lem-weil-pbc-ideal-cotangent-flat-base-change-ring this map is surjective.
   If `g` is flat, lem-weil-pbc-flat-morphism-affine-criterion makes `R'` to `R` flat,
   and the same ring result gives bijectivity. The modules are quasi-coherent by
   lem-weil-pbc-module-pullback-quasi-coherent and the functoriality node. By
   lem-weil-pbc-quasi-coherent-module-cokernel-image the cokernel has zero sections
   on this affine cover, hence is zero, so `c` is an epimorphism. In the flat case,
   lem-weil-pbc-affine-tilde-gamma-adjunction makes the restrictions isomorphisms;
   lem-weil-pbc-sheaf-morphism-on-basis then makes `c` globally an isomorphism. -/
theorem closedImmersion_conormal_flat_base_change
    {X Z X' Z' : Scheme.{uc}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (g : X ⟶ X') (f : Z ⟶ Z') (h : i ≫ g = f ≫ i')
    (hc : IsLimit (PullbackCone.mk i f h))
    (c : (tensorPullback f).obj ((tensorPullback i').obj i'.ker.toModules) ⟶
      (tensorPullback i).obj i.ker.toModules)
    (hcanonical : c = Classical.choose ((Classical.choose_spec
      (closedImmersion_conormal_functorial i i' g f h).2).2))
    : Epi c ∧ (Flat g → IsIso c) := by
  sorry
end AlgebraicGeometry.Scheme.Modules
