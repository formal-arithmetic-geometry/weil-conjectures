/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.LinearAlgebra.BilinearMap
import WeilConjectures.CategoryTheory.MittagLefflerLimitExact

/-!
# Hom exactness for sequential finite-free colimits

Source: Stacks Project, Algebra, Tag 059X (`lemma-countgen-projective`), the
finite-free Hom rows and functorial colimit identification, and Tag 0598
(`lemma-ML-exact-sequence`).
(blueprint: lem-trf-sequential-free-colimit-hom-exact)

## Main definitions

- `Module.sequentialHomSystem`: the inverse Hom system with precomposition transitions.

## Main statements

- `Module.sequential_free_colimit_hom_exact`: natural restriction isomorphisms and
  exactness of Hom when the inverse Hom system of the kernel is Mittag-Leffler.
-/

@[expose] public section

universe u v w w₁ w₂ w₃

open CategoryTheory CategoryTheory.Limits

namespace Module

/-- The inverse system of Hom modules with precomposition transitions.
Its `ModuleCat.sectionsSubmodule` is the module `L_N` of compatible families,
with componentwise operations. Compatibility with all composites is equivalent to
adjacent compatibility. The natural number `n` represents the positive index `n + 1`.

Source: Stacks Project, Algebra, Tag 059X (`lemma-countgen-projective`), final
functorial identification with the inverse limit.
(blueprint: lem-trf-sequential-free-colimit-hom-exact) -/
def sequentialHomSystem {R : Type u} [CommRing R] (F : ℕ ⥤ ModuleCat.{v} R)
    (N : Type w) [AddCommGroup N] [Module R N] : ℕᵒᵖ ⥤ ModuleCat.{max v w} R :=
  Functor.ofOpSequence (X := fun n : ℕ ↦ ModuleCat.of R (F.obj n →ₗ[R] N))
    (fun n : ℕ ↦ ModuleCat.ofHom
      (LinearMap.lcomp R N (F.map (homOfLE (Nat.le_succ n))).hom))

/-- Restriction from a sequential finite-free colimit gives natural linear isomorphisms
with compatible Hom families. Hom from the colimit preserves a short exact sequence
when the inverse Hom system of its kernel is Mittag-Leffler.

Source: Stacks Project, Algebra, Tag 059X (`lemma-countgen-projective`), final two
paragraphs, and Tag 0598 (`lemma-ML-exact-sequence`).
(blueprint: lem-trf-sequential-free-colimit-hom-exact)

The index `n : ℕ` denotes the positive index `n + 1`. The diagram `F` includes
all composites of the adjacent maps, and `c.pt` is the module P with coprojections
`c.ι.app n`. Finite freeness includes rank zero. The formula for rho specifies the
canonical restriction isomorphism, and the next formula is its naturality.

Proof:
1. Cocone compatibility makes restriction land in `ModuleCat.sectionsSubmodule`; addition
   and scalar multiplication are componentwise. Conversely adjacent compatibility
   implies compatibility with every composite, by induction. The colimit universal
   property (`def-weil-pbc-category-colimit`) supplies a unique extending linear map.
   Restriction is therefore a linear isomorphism.
2. Associativity of composition shows that postcomposition commutes with restriction,
   and that postcomposition preserves compatible families. This gives naturality.
3. At every stage Hom from a finite-free module preserves the given short exact
   sequence: injectivity is pointwise, kernel elements lift uniquely through a,
   and maps into N3 lift through b by choosing lifts of finitely many basis values.
   The empty basis handles rank zero.
4. Precomposition commutes with postcomposition, so these rows form a short exact
   sequence of inverse systems of abelian groups. Its kernel system is ML by
   `def-weil-pbc-mittag-leffler-system`. Apply part (3) of
   `lem-weil-pbc-mittag-leffler-limit-exact` to obtain short exactness on compatible
   families. Their coordinate maps are R-linear.
5. Naturality from step 2 transports injectivity, the equality of image and kernel,
   and surjectivity across the restriction isomorphisms, proving Hom exactness. -/
theorem sequential_free_colimit_hom_exact
    {R : Type u} [CommRing R] (F : ℕ ⥤ ModuleCat.{v} R)
    (hfree : ∀ n : ℕ, ∃ r : ℕ, Nonempty (F.obj n ≃ₗ[R] (Fin r → R)))
    (c : Cocone F) (hc : IsColimit c) :
    (∃ ρ : (N : ModuleCat.{w} R) →
        (c.pt →ₗ[R] N) ≃ₗ[R] ModuleCat.sectionsSubmodule (sequentialHomSystem F N),
      (∀ (N : ModuleCat.{w} R) (h : c.pt →ₗ[R] N) (n : ℕ),
        (ρ N h).val (Opposite.op n) = h.comp (c.ι.app n).hom) ∧
      (∀ (N N' : ModuleCat.{w} R) (a : N →ₗ[R] N') (h : c.pt →ₗ[R] N) (n : ℕ),
        (ρ N' (a.comp h)).val (Opposite.op n) = a.comp ((ρ N h).val (Opposite.op n)))) ∧
    (∀ (N₁ : ModuleCat.{w₁} R) (N₂ : ModuleCat.{w₂} R) (N₃ : ModuleCat.{w₃} R)
      (a : N₁ →ₗ[R] N₂) (b : N₂ →ₗ[R] N₃),
      Function.Injective a → Function.Exact a b → Function.Surjective b →
      (sequentialHomSystem F N₁ ⋙ forget (ModuleCat R)).IsMittagLeffler →
      Function.Injective (fun h : c.pt →ₗ[R] N₁ ↦ a.comp h) ∧
      Function.Exact (fun h : c.pt →ₗ[R] N₁ ↦ a.comp h)
        (fun h : c.pt →ₗ[R] N₂ ↦ b.comp h) ∧
      Function.Surjective (fun h : c.pt →ₗ[R] N₂ ↦ b.comp h)) := by
  sorry

end Module
