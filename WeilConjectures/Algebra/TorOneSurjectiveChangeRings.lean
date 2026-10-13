/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Surjectivity of the change-of-rings map on first Tor

Source: Stacks Project, Algebra, Lemma Tag 00MN
(`literature/stacks-project/algebra.tex`, lemma-surjective-on-tor-one-trivial).
(blueprint: lem-weil-pbc-tor-one-surjective-change-rings)

The first homology of a tensor product of a free resolution is the Tor module
of `def-weil-pbc-tor-modules`, realized by Mathlib's `CategoryTheory.Tor'`.
Tensor associativity identifies `(A ⊗[R] F) ⊗[A] (A/J)` with
`F ⊗[R] (A/J)`, with symmetry exchanging the tensor factors. Thus the
homology map below is precisely the node's resolution-induced change-of-rings map.
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory

/-- The change-of-rings map on first Tor with coefficients in `A/IA` is surjective.

Source: Stacks Project, Algebra, Lemma Tag 00MN
(`literature/stacks-project/algebra.tex`, lines 23881--23919).
(blueprint: lem-weil-pbc-tor-one-surjective-change-rings)

Proof, following the five steps of the node:
1. Base change the free resolution `F` to `F' = A ⊗[R] F`. Its terms are free,
   and right exactness gives exactness of `F'₁ → F'₀ → A ⊗[R] M → 0`.
   Tensor cancellation and symmetry identify `F' ⊗[A] (A/J)` with
   `F ⊗[R] (A/J)`, naturally in each term and hence on first homology.
2. Construct a free resolution `G'` of `A ⊗[R] M` containing `F'`, unchanged
   in degrees zero and one. Inductively, in degree `k ≥ 2`, adjoin a free
   module `E_k` on the elements of the kernel of the previous differential;
   send its basis vectors to those elements. Set `G'_k = F'_k ⊕ E_k` and
   extend the differential by this map. Its image is exactly that kernel,
   its square is zero, and the inclusions `j : F' → G'` form a chain map.
3. After tensoring with `A/J`, the degree-one cycles of `F'` and `G'` agree.
   The boundaries for `F'` are contained in those for `G'`, so `H₁(j ⊗ 1)`
   is the surjective projection between their quotients of the same cycles.
4. Extend the given `φ` to a chain map `a : G' → G` lifting the identity.
   In degrees zero and one use `φ`. On each newly adjoined basis vector in
   degree `k`, exactness of `G` supplies a preimage of its image under
   `a_(k-1)`. This constructs `a` with `a ∘ j = φ` in all degrees.
5. Free modules are projective. Independence of projective resolutions
   identifies `H₁(a ⊗ 1)` with the identity on `Tor₁`, hence it is an
   isomorphism. Therefore `H₁(φ ⊗ 1) = H₁(a ⊗ 1) ∘ H₁(j ⊗ 1)` is
   surjective; Step 1 identifies it with the asserted change-of-rings map.
-/
theorem tor_one_change_of_rings_surjective
    (R A : Type u) [CommRing R] [CommRing A]
    (f : R →+* A) (I : Ideal R) (M : ModuleCat.{u} R)
    (F : ProjectiveResolution M)
    (hF : ∀ i : ℕ, Module.Free R (F.complex.X i))
    (G : ProjectiveResolution ((ModuleCat.extendScalars f).obj M))
    (hG : ∀ i : ℕ, Module.Free A (G.complex.X i))
    (φ : ((ModuleCat.extendScalars f).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj F.complex ⟶ G.complex)
    (hφ : φ.f 0 ≫ G.π.f 0 = (ModuleCat.extendScalars f).map (F.π.f 0)) :
    Function.Surjective
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A)
        (ComplexShape.down ℕ) 1).map
        ((((MonoidalCategory.tensoringRight (ModuleCat.{u} A)).obj
          (ModuleCat.of A (A ⧸ I.map f))).mapHomologicalComplex
            (ComplexShape.down ℕ)).map φ)) := by
  sorry

end CategoryTheory
