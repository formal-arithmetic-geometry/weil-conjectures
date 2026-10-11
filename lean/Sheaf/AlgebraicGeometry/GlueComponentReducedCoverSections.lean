/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Structure sections on a reduced scheme away from component intersections

Source: Stacks Project, Varieties Lemma 09NE, proof, first paragraph after setting T
(blueprint: lem-sc-glue-component-reduced-cover-sections).
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- Let `X` be a reduced scheme and `i a : Z a ⟶ X` finitely many closed immersions whose
images cover `X`. With `T` the union of the pairwise intersections `Z a ∩ Z b`, `a ≠ b`, the
sets `Z a \ T` are open in `X`, pairwise disjoint and cover `X \ T`, and for every open
`V ⊆ X \ T` the restriction maps `Γ(X, V) → Γ(Z a, (i a)⁻¹ V)` together give a bijection
onto the product over `a` (empty factors are the zero ring), so `X \ T` is the
scheme-theoretic union of the open subschemes `Z a \ T`.
Source: Stacks Project, Varieties Lemma 09NE, proof, first paragraph after setting T
(blueprint: lem-sc-glue-component-reduced-cover-sections).

Proof: `T` is a finite union of closed sets, hence closed, and `Z a \ T` is the complement
in `X \ T` of the finitely many closed sets `Z b`, `b ≠ a`, hence open; disjointness and
coverage are set-theoretic.  On `X \ T` each restricted closed immersion is a homeomorphism
onto the open `Z a \ T`; since `X` is reduced its defining ideal vanishes there (a section
vanishing on a closed subscheme with the same underlying open set is nilpotent locally, hence
zero), so it is an isomorphism of open subschemes.  The sheaf axiom for the disjoint open
cover of `V` by the `V ∩ Z a` then identifies `Γ(X, V)` with the product of the sections.
-/
theorem glue_component_reduced_cover_sections
    {X : Scheme.{u}} [IsReduced X] {ι : Type v} [Finite ι]
    (Z : ι → Scheme.{u}) (i : ∀ a : ι, Z a ⟶ X) [∀ a : ι, IsClosedImmersion (i a)]
    (hcover : (⋃ a : ι, Set.range (i a)) = Set.univ) :
    let T : Set X := ⋃ a : ι, ⋃ b : ι, ⋃ (_ : b ≠ a), Set.range (i a) ∩ Set.range (i b)
    IsClosed T ∧
      (∀ a : ι, IsOpen (Tᶜ ∩ Set.range (i a))) ∧
      Pairwise (fun a b : ι => Disjoint (Tᶜ ∩ Set.range (i a)) (Tᶜ ∩ Set.range (i b))) ∧
      (⋃ a : ι, Tᶜ ∩ Set.range (i a)) = Tᶜ ∧
      ∀ V : X.Opens, (V : Set X) ⊆ Tᶜ →
        Function.Bijective
          (fun s : Γ(X, V) => fun a : ι => ((i a).app V).hom s :
            Γ(X, V) → ∀ a : ι, Γ(Z a, (i a) ⁻¹ᵁ V)) := by
  sorry

end AlgebraicGeometry
