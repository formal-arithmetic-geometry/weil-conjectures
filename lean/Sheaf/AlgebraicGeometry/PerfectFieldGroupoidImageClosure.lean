/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.Perfect
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Reduced image closures of groupoids over perfect fields

Source: Stacks Project, More on Groupoid Schemes, Tag 04Q8
(blueprint: lem-sfb-perfect-field-groupoid-image-closure).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The reduced closed image of a morphism of absolute groupoid schemes on the spectrum
of a perfect field inherits all groupoid operations. Source: Stacks Project, Tag 04Q8
(blueprint: lem-sfb-perfect-field-groupoid-image-closure).

The kernel ideal specifies the reduced induced structure: on each affine open it is
exactly the ideal of functions vanishing at the points of the image closure. The map
on composable pairs is the canonical pullback map, with both projections equal to `j`.
There are no finiteness or separatedness assumptions, and the source and target maps
need not coincide. Taking `a` to be the identity gives the reduction of `R₂`: the
vanishing ideal of the whole space is its nilradical, and uniqueness of the reduced
closed structure identifies the resulting immersion with the canonical reduction.

Proof plan, following the node:
1. Apply `lem-weil-pbc-reduced-induced-closed-subscheme` to the closure of the image of
   `a`. This constructs the reduced closed immersion and gives its vanishing ideal,
   support and uniqueness. Restrict source and target by composition with `j`.
2. A closed immersion is a monomorphism (`def-weil-closed-immersion`): locally its ring
   map is a quotient, so two maps into its source with equal composites agree. Hence
   its map on points of every test scheme is injective.
3. The unit image lies in the closure since `e₁ ≫ a = e₂`. Inversion preserves the image
   and its closure since it is involutive and commutes with `a`. The unit source is a
   field spectrum, hence reduced. Factor the unit and the inverse through `j` by
   `lem-weil-pbc-reduced-source-factors-through-closed-subscheme`.
4. The composable-pair scheme of the reduced image is reduced. Cover it by products of
   affine opens (`lem-weil-pbc-open-fibre-product`). Their rings are tensor products
   (`lem-weil-pbc-fibre-product-affine-spectra`) of reduced algebras for the two possibly
   different field structures. Use `lem-weil-pbc-perfect-reduced-tensor`; reducedness
   is local on this cover.
5. By `lem-sfb-scheme-product-image-closure`, the closure of the image of the original
   composable pairs is the image of the new composable pairs in the ambient pullback.
   The inverse image of the image closure under ambient composition is closed and
   contains that dense image, by compatibility with `a`. Ambient composition on the
   reduced composable-pair scheme therefore factors through `j` by the reduced-source
   factorization lemma.
6. Compose each required groupoid identity with `j`, use the ambient groupoid laws,
   and cancel the monomorphism from step 2. The resulting operations are scheme
   morphisms, so the pointwise groupoids are natural in the test scheme.
7. For the identity morphism the image closure is the whole space, its vanishing ideal
   is the nilradical (`def-weil-pbc-scheme-reduction`), and uniqueness of the reduced
   closed immersion gives exactly the reduction case. None of these steps uses any
   finite-type, quasi-compactness or separatedness hypothesis. -/
theorem exists_reduced_image_groupoid_of_perfectField
    (k : Type u) [Field k] [PerfectField k] {R₁ R₂ : Scheme.{u}}
    (s₁ t₁ : R₁ ⟶ Spec (CommRingCat.of k))
    (e₁ : Spec (CommRingCat.of k) ⟶ R₁) (i₁ : R₁ ⟶ R₁)
    (c₁ : pullback s₁ t₁ ⟶ R₁) (h₁ : IsGroupoidScheme s₁ t₁ e₁ i₁ c₁)
    (s₂ t₂ : R₂ ⟶ Spec (CommRingCat.of k))
    (e₂ : Spec (CommRingCat.of k) ⟶ R₂) (i₂ : R₂ ⟶ R₂)
    (c₂ : pullback s₂ t₂ ⟶ R₂) (h₂ : IsGroupoidScheme s₂ t₂ e₂ i₂ c₂)
    (a : R₁ ⟶ R₂) (hs : a ≫ s₂ = s₁) (ht : a ≫ t₂ = t₁)
    (he : e₁ ≫ a = e₂) (hi : i₁ ≫ a = a ≫ i₂)
    (hc : c₁ ≫ a =
      pullback.map s₁ t₁ s₂ t₂ a a (𝟙 (Spec (CommRingCat.of k)))
        ((Category.comp_id s₁).trans hs.symm) ((Category.comp_id t₁).trans ht.symm) ≫ c₂) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ R₂),
      IsClosedImmersion j ∧ IsReduced Z ∧
      Set.range j = closure (Set.range a) ∧
      j.ker = Scheme.IdealSheafData.vanishingIdeal
        ⟨closure (Set.range a), isClosed_closure⟩ ∧
      ∃ (e : Spec (CommRingCat.of k) ⟶ Z) (i : Z ⟶ Z)
        (c : pullback (j ≫ s₂) (j ≫ t₂) ⟶ Z),
        IsGroupoidScheme (j ≫ s₂) (j ≫ t₂) e i c ∧
        e ≫ j = e₂ ∧ i ≫ j = j ≫ i₂ ∧
        c ≫ j = pullback.map (j ≫ s₂) (j ≫ t₂) s₂ t₂ j j
          (𝟙 (Spec (CommRingCat.of k)))
          (Category.comp_id (j ≫ s₂)) (Category.comp_id (j ≫ t₂)) ≫ c₂ := by
  sorry

end AlgebraicGeometry
