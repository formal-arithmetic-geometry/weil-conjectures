module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.Topology.Connected.Basic
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes

import Sheaf.AlgebraicGeometry.SmoothPTorsionAdditiveEmbedding
import Sheaf.AlgebraicGeometry.AdditiveSubgroupPerfectDecomposition
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

/-! # Smooth connected commutative exponent-p groups over a perfect field are vector groups

Source: Milne, Algebraic Groups (2017), Proposition 14.54, printed p.297 (also
Proposition 14.49 and Corollary 14.53).
(blueprint: lem-sfb-perfect-exponent-p-vector-group)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonObj

namespace AlgebraicGeometry

/-- A smooth connected commutative affine group scheme of exponent `p` over a perfect
field of characteristic `p` is a finite additive power.

Source: Milne, Algebraic Groups (2017), Proposition 14.54, printed p.297.
(blueprint: lem-sfb-perfect-exponent-p-vector-group)

Proof:
1. Apply `smooth_p_torsion_additive_embedding` to obtain a closed embedding into a
   finite additive power.
2. Apply `additive_subgroup_perfect_decomposition` to decompose the subgroup into
   additive, infinitesimal, and finite étale factors.
3. Smoothness gives reducedness, which excludes every nontrivial infinitesimal
   `alpha` factor.
4. Connectedness and the identity section exclude every nontrivial finite étale
   factor; the remaining group is the additive power. Inverting the resulting
   group-scheme isomorphism gives the displayed orientation, including `d = 0`.
-/
theorem perfect_exponent_p_vector_group
    {k : Type u} [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    (hperfect : ∀ x : k, ∃ y : k, y ^ p = x)
    (G : Grp (Over (Spec (.of k)))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [Smooth G.X.hom]
    [ConnectedSpace G.X.left] [IsCommMonObj G.X]
    (hpG : 𝟙 G.X ^ p = 1) :
    ∃ d : ℕ, Nonempty ((∏ᶜ (fun _ : Fin d ↦
      Grp.mk (StandardGroupSchemes.additive k))) ≅ G) := by
  sorry

end AlgebraicGeometry
