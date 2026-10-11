/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Monoidal.Tor

/-!
# Symmetry of Tor for modules over a commutative ring

Source: Stacks Project, Algebra, Lemma Tag 00M3, including its functoriality paragraph
(blueprint: lem-weil-pbc-tor-symmetry).
-/

universe u

namespace CategoryTheory

/-- Tor computed by resolving its first argument is naturally symmetric in its two arguments.
The components of the natural isomorphism are isomorphisms of `R`-modules.

Source: Stacks Project, Algebra, Lemma Tag 00M3 (lemma-tor-left-right).
(blueprint: lem-weil-pbc-tor-symmetry)

Proof:
1. Choose projective resolutions `P` of `M` and `Q` of `N`
   (`def-weil-pbc-tor-modules`). Form the double complex with terms `Pᵢ ⊗ Qⱼ` and
   differentials `dP ⊗ 1` and `1 ⊗ dQ`; these commute by functoriality of tensor.
2. Projective modules are flat (`lem-weil-pbc-projective-module-flat`), so tensoring
   the augmented resolutions with each term preserves exactness
   (`lem-weil-pbc-flat-tensor-exact`). Rows and columns are exact in positive degrees.
3. Right exactness (`lem-weil-pbc-tensor-right-exact`) identifies the row cokernel complex
   with `M ⊗ Q` and the column cokernel complex with `P ⊗ N`, compatibly with their
   differentials (`def-weil-pbc-chain-complex-tensor-module`).
4. The natural comparison of the homology of these two cokernel complexes
   (`lem-weil-pbc-double-complex-cokernel-homology-iso`) yields
   `Hᵢ(P ⊗ N) ≅ Hᵢ(M ⊗ Q)` (`def-weil-pbc-module-chain-complex-homology`).
5. Tensor commutativity (`lem-weil-pbc-module-tensor-comm`) is compatible with the
   differential, giving `M ⊗ Q ≅ Q ⊗ M` and an isomorphism on homology.
6. Compose these isomorphisms with the canonical projective-resolution computations of
   Tor (`def-weil-pbc-tor-modules`); the result is `Torᵢ(M,N) ≅ Torᵢ(N,M)`.
7. Lift maps of both modules to maps `a` and `b` of their resolutions
   (`lem-weil-pbc-projective-resolution-lift`). Their tensor product is a map of double
   complexes, inducing `φ ⊗ b` and `a ⊗ ψ` on the two cokernel complexes. The comparison
   in step 4 and the swap in step 5 are natural. Tor maps are computed by these lifts
   (`lem-weil-pbc-tor-map-via-resolution-lift`), so the composite commutes with maps in
   both variables. Applying this to identity maps with different resolutions proves
   independence of choices, hence gives the natural isomorphism of bifunctors. -/
theorem nonempty_tor'_flip_iso (R : Type u) [CommRing R] (i : ℕ) :
    Nonempty (Tor' (ModuleCat.{u} R) i ≅ (Tor' (ModuleCat.{u} R) i).flip) := by
  sorry

end CategoryTheory
