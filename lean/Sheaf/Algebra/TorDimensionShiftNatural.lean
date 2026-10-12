/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.Algebra.Homology.FreeResolutionSesSplit

/-! # Dimension shifting for Tor

Source: literature/stacks-project/algebra.tex, Tags 00LY, 00LZ, 00M0, 00S2
(blueprint: lem-sc-p1-tor-dimension-shift-natural).
-/

@[expose] public section

universe u

namespace CategoryTheory

/-- Dimension shifting for Tor along a free presentation, natural in the second variable.
Source: literature/stacks-project/algebra.tex, Tags 00LY, 00LZ, 00M0, 00S2
(blueprint: lem-sc-p1-tor-dimension-shift-natural).

Step 1. Apply lem-weil-pbc-free-resolution-ses-split to `0 → K → K → 0 → 0`
to fix a free resolution `G` of `K = S.X₁`, independently of the second module `N`.
Step 2. Splice it to the given short exact sequence: put `P₀ = F = S.X₂`,
`Pₙ₊₁ = Gₙ`, with first differential `jη` and augmentation `p` to `M = S.X₃`.
All terms are free (def-weil-pbc-free-module). Exactness follows from
`image j = kernel p` and injectivity of `j` (def-weil-pbc-exact-sequence):
`image (jη) = kernel p` and `kernel (jη) = kernel η = image e₁`;
all higher degrees inherit exactness from `G`.
Step 3. Compute Tor using these resolutions (def-weil-pbc-tor-modules).
For `i ≥ 1`, the three terms around degree `i+1` of `P ⊗ N` are
`Gᵢ₊₁ ⊗ N → Gᵢ ⊗ N → Gᵢ₋₁ ⊗ N`, with the same differentials as in `G ⊗ N`.
The identity on `Gᵢ ⊗ N` induces the desired quotient-of-cycles isomorphism.
Compose with the canonical resolution identifications to obtain `θ N`.
Step 4. For a map `g : N → N'`, the maps `1 ⊗ g` at these three terms coincide
in both complexes. They preserve cycles and boundaries, so the quotient isomorphism
commutes with the induced homology maps. The canonical identifications are functorial
(def-weil-pbc-tor-modules), giving the displayed naturality equation.
-/
theorem tor_dimension_shift_natural
    {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    [Module.Free R S.X₂] (i : ℕ) (hi : 1 ≤ i) :
    ∃ θ : ∀ N : ModuleCat.{u} R,
      (((Tor' (ModuleCat.{u} R) (i + 1)).obj S.X₃).obj N) ≅
        (((Tor' (ModuleCat.{u} R) i).obj S.X₁).obj N),
      ∀ (N N' : ModuleCat.{u} R) (g : N ⟶ N'),
        ((Tor' (ModuleCat.{u} R) (i + 1)).obj S.X₃).map g ≫ (θ N').hom =
          (θ N).hom ≫ ((Tor' (ModuleCat.{u} R) i).obj S.X₁).map g := by
  sorry

end CategoryTheory
