module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes

/-! # Trivializing an invertible module upstairs over a finite morphism

Source: Stacks Project, Tag 0BUT, `divisors-lemma-finite-trivialize-invertible-upstairs`
in `literature/stacks-project/divisors.tex`.
(blueprint: lem-sfb-finite-trivialize-invertible-upstairs)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- An invertible module on the source of a finite morphism is trivial over the inverse image
of some open neighbourhood of any prescribed point of the target.

Source: Stacks Project, Tag 0BUT, `divisors-lemma-finite-trivialize-invertible-upstairs`.

Proof:
1. Choose an affine open neighbourhood U of z. Its inverse image X is affine because p is
   finite. The restricted morphism q : X → U is finite, and the restriction L of M is
   invertible by restriction of its local rank-one trivializations.
2. By `lem-weil-pbc-finite-closed-map-finite-fibres`, the fibre E over z is finite. Apply
   `lem-sfb-affine-invertible-finite-set-section` to X, L and E to find a global section s
   nonvanishing at every point of E. This includes E empty and nonclosed fibre points.
3. By `lem-weil-pbc-nonvanishing-section-trivializes`, the nonvanishing locus W of s is open,
   contains E, and carries the multiplication-by-s trivialization of L. Let C = X \ W.
4. A finite morphism is closed by `lem-weil-pbc-finite-closed-map-finite-fibres`. Thus
   V = U \ q(C) is open. Since E is contained in W, z is in V. Every point of q⁻¹(V) lies
   in W, since otherwise its image would belong to q(C).
5. Restrict the trivialization on W and its inverse to q⁻¹(V). Since U is open in the
   original target, V is an open neighbourhood there, and q⁻¹(V) is p⁻¹(V). This is the
   required isomorphism of modules on that open subscheme.

(blueprint: lem-sfb-finite-trivialize-invertible-upstairs) -/
theorem exists_trivialization_over_preimage_of_isFinite
    {Y Z : AlgebraicGeometry.Scheme.{u}} (p : Y ⟶ Z) [AlgebraicGeometry.IsFinite p]
    (M : Y.Modules) [M.IsInvertible] (z : Z) :
    ∃ V : Z.Opens, z ∈ V ∧
      Nonempty (M.restrict (p ⁻¹ᵁ V).ι ≅
        SheafOfModules.unit (p ⁻¹ᵁ V).toScheme.ringCatSheaf) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
