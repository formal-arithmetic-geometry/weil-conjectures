/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q142
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Topology.KrullDimension

/-!
# Surjective dimension-attaining neighbourhoods of a flat morphism

Source: Stacks Project, Morphisms, Tag 0AFE, `lemma-rel-dimension-dimension`,
first proof paragraph (blueprint: lem-per-flat-dimension-surjective-neighbourhoods).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Around each source point, a flat locally finite type map of locally Noetherian schemes
with constant local fibre dimension admits a surjective open restriction attaining both
local dimensions and preserving the original hypotheses.

Source: Stacks Project, Morphisms, Tag 0AFE, `lemma-rel-dimension-dimension`,
first proof paragraph (blueprint: lem-per-flat-dimension-surjective-neighbourhoods).

Proof:
1. By `def-kun-topological-dimension-at-point`, choose open neighbourhoods U₀ of x
   and V₀ of f(x) whose dimensions attain the respective minima. The neighbourhood
   families contain the whole spaces; the minima are attained even at infinity.
2. By `pqf-lem-lft-fp-locnoeth`, f is locally of finite presentation. Together with
   flatness, `lem-weil-pbc-flat-lfp-open` implies that f is an open map.
3. Set U = U₀ ∩ f⁻¹(V₀) and V = f(U). Both are open neighbourhoods, and V ⊆ V₀.
   The minimum property and `lem-weil-pbc-open-subspace-dimension-monotone` give
   dim_x X ≤ dim U ≤ dim U₀ = dim_x X and the analogous chain for V.
   Restrict f using the open subschemes of `def-weil-open-immersion`; its image is V,
   so the restriction is surjective.
4. The open-subscheme stalk maps agree with those of f, proving flatness by
   `def-weil-flat-morphism`. Every affine open of U or V is an affine open of X or Y
   with unchanged sections; `pqf-lem-affine-open-locnoeth` makes its ring Noetherian,
   giving local Noetherianity by `pqf-def-locnoeth`.
5. For affine opens A ⊆ U and B ⊆ V with h(A) ⊆ B, their rings and induced map are
   unchanged from X and Y. Apply both directions of `lem-weil-pbc-lft-affine-pairs`
   to deduce that the restriction is locally of finite type.
6. By the fibre homeomorphisms of `def-pc-scheme-fibre`, the restricted fibre is
   the open subspace U ∩ f⁻¹(b) of the original fibre. At each of its points,
   `lem-weil-pbc-dimension-at-point-open-subspace` preserves local dimension,
   so the given dimension d remains unchanged. For empty X there is no x to consider. -/
theorem exists_surjective_dimension_attaining_neighbourhoods_of_flat
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f] (d : ℕ)
    (hd : ∀ a : X, topologicalKrullDimAt (f.asFiber a) = (d : WithBot ℕ∞))
    (x : X) :
    ∃ (U : X.Opens) (V : Y.Opens), x ∈ U ∧ f x ∈ V ∧
      ∃ e : U ≤ f ⁻¹ᵁ V,
        f '' (U : Set X) = (V : Set Y) ∧
        topologicalKrullDim U.toScheme = topologicalKrullDimAt x ∧
        topologicalKrullDim V.toScheme = topologicalKrullDimAt (f x) ∧
        Surjective (f.resLE V U e) ∧ Flat (f.resLE V U e) ∧
        LocallyOfFiniteType (f.resLE V U e) ∧
        IsLocallyNoetherian U.toScheme ∧ IsLocallyNoetherian V.toScheme ∧
        ∀ a : U.toScheme,
          topologicalKrullDimAt ((f.resLE V U e).asFiber a) = (d : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
