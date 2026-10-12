/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
import Sheaf.Algebra.Homology.FreeResolutionSesSplit

/-!
# Low-degree Tor exact sequence in the first variable

Source: Stacks Project, Algebra, Tags 00M0 and 00M3; More on Algebra, proof of
Tag 0912 (blueprint: lem-weil-pbc-tor-long-exact-first-variable).
-/

@[expose] public section

universe u

open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

namespace CategoryTheory

/-- The low-degree Tor sequence for a short exact sequence in the first variable,
with an `R`-linear connecting map natural in the second variable.

Source: Stacks Project, Algebra, Tags 00M0 and 00M3; More on Algebra, proof of
Tag 0912. The direct proof below uses Algebra 065P and Homology 0111.
(blueprint: lem-weil-pbc-tor-long-exact-first-variable)

1. By `lem-weil-pbc-free-resolution-ses-split`, choose free resolutions `F`, `F'`,
   `F''` of `Q`, `Q'`, `Q''`, with augmentation-compatible lifts `α` of `u` and `β`
   of `v`. Choose degreewise splittings `π`, `s` with `βα = 0`, `πα = 1`, `βs = 1`,
   and `απ + sβ = 1`. Fix these choices independently of `N`.
2. Tensor the resolutions and their maps with `N`. The splitting identities persist,
   so the resulting complexes `C`, `C'`, `C''` form a degreewise short exact sequence.
   For every `g : N →ₗ[R] N'`, the chain maps `1 ⊗ g` commute with `α ⊗ 1`,
   `β ⊗ 1`, and the differentials, by the tensor product map composition identities.
3. By `def-weil-pbc-tor-modules`, identify Tor in degree one with the homology of
   these complexes. By `lem-weil-pbc-tor-map-via-resolution-lift`, the maps induced
   by `β ⊗ 1` and `1 ⊗ g` are respectively `Tor₁(v,N)` and `Tor₁(Q'',g)`.
   By `lem-weil-pbc-tensor-right-exact`, the augmentations induce isomorphisms
   `c_N : H₀(C) ≅ Q ⊗ N` and similarly for `C'`; these commute with `u ⊗ 1`
   and `1 ⊗ g` because the augmentations do.
4. Apply `lem-weil-pbc-snake-lemma-modules` to the diagram with top row
   `C₁ / im d₂ → C'₁ / im d'₂ → C''₁ / im d''₂ → 0` and bottom row
   `0 → C₀ → C'₀ → C''₀`. The bottom is exact by step 2. For top exactness,
   if `β y = d'' z''`, lift `z''` along the surjective `β₂` to `z'`; then
   `y - d' z'` lies in `ker β₁ = im α₁`. The top last map is surjective as `β₁`
   is. The vertical kernels and cokernels are `H₁` and `H₀`. The snake map
   `∂_N : H₁(C'') → H₀(C)` sends a cycle class `[z]` to `[w]`, where
   `β₁ y = z` and `α₀ w = d'₁ y`; its value is independent of the choices.
5. Compose the Tor-to-homology isomorphism, `∂_N`, and `c_N` to obtain `δ_N`.
   Transport snake exactness to exactness at `Tor₁(Q'',N)` and `Q ⊗ N` using
   step 3. Exactness at `Q' ⊗ N` and surjectivity of `v ⊗ 1` follow from
   `lem-weil-pbc-tensor-right-exact` applied to the original short exact sequence.
6. Given `g`, the images of the choices `y,w` under `1 ⊗ g` are admissible choices
   for the image of `z`, by step 2. The snake formula therefore gives
   `∂_{N'} H₁(1 ⊗ g) = H₀(1 ⊗ g) ∂_N`. Transport through the natural
   identifications of step 3 to obtain `(1 ⊗ g) δ_N = δ_{N'} Tor₁(Q'',g)`.
   The other squares commute by tensor bifunctoriality and, for the Tor map,
   `lem-weil-pbc-tor-map-via-resolution-lift` applied to `β ⊗ g`.
-/
theorem tor_long_exact_first_variable
    {R : Type u} [CommRing R]
    {Q Q' Q'' : Type u} [AddCommGroup Q] [AddCommGroup Q'] [AddCommGroup Q'']
    [Module R Q] [Module R Q'] [Module R Q'']
    (u : Q →ₗ[R] Q') (v : Q' →ₗ[R] Q'')
    (hu : Function.Injective u) (hv : Function.Surjective v)
    (hExact : Function.Exact u v) :
    ∃ δ : (∀ (N : Type u) [AddCommGroup N] [Module R N],
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R Q'')).obj
            (ModuleCat.of R N)) ⟶ ModuleCat.of R (Q ⊗[R] N)),
      (∀ (N : Type u) [AddCommGroup N] [Module R N],
        Function.Exact
          (((Tor' (ModuleCat R) 1).map (ModuleCat.ofHom v)).app
            (ModuleCat.of R N)).hom (δ N).hom ∧
        Function.Exact (δ N).hom (u.rTensor N) ∧
        Function.Exact (u.rTensor N) (v.rTensor N) ∧
        Function.Surjective (v.rTensor N)) ∧
      (∀ (N N' : Type u) [AddCommGroup N] [Module R N]
        [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N'),
        (MonoidalCategory.tensorHom (𝟙 (ModuleCat.of R Q))
          (ModuleCat.ofHom g)).hom.comp (δ N).hom =
          (δ N').hom.comp
            (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R Q'')).map
              (ModuleCat.ofHom g)).hom) := by sorry

end CategoryTheory
