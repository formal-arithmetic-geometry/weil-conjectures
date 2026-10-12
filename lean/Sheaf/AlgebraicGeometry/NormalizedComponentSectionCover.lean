/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
import Sheaf.AlgebraicGeometry.GlueComponentReducedCoverSections

/-! # A normalized frame cover for prescribed component sections

Source: Stacks Project, Varieties Lemma 09NE (lemma-glue-invertible-sheaves).
(blueprint: lem-sc-normalized-component-section-cover) -/

@[expose] public section

universe u v
open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- Source: Stacks Project, Varieties Lemma 09NE, first three paragraphs of the direct
proof and final paragraph (normalizing the frames by the prescribed sections).

Proof: Let T be the finite union of pairwise intersections. The reduced-cover lemma
makes T closed and identifies the component opens off T scheme-theoretically, with a
product bijection on structure sections on every open disjoint from T. T is discrete:
a finite union of closed discrete subsets is discrete. Choose one open U_t for each
point t of T, meeting T only at t. Remove every component not containing t. On each
incident component s is nonzero in the residue-field fibre. A section of an invertible
module with nonzero fibre is a local free generator: choose a trivialization, whose
section coefficient has a germ outside the maximal ideal, and restrict to its basic
open. Shrink U_t simultaneously along these finitely many component neighborhoods.
For each incident component use the restricted s as frame m, and use f_t=1 on U_t.
For nonincident components the preimage is empty and its unique section is a frame.
Off T cover each component by its free-generator neighborhoods, regarded as opens of Y
by the reduced-cover lemma. Use that component's frames and the unique empty sections
on all other components. The structure-section bijection transfers the coefficient
of s in its frame to a function f on Y. Index the union of the point neighborhoods
and component neighborhoods by a type in universe max(u,v). Every distinct pair of
members overlaps outside T: point neighborhoods have distinct distinguished points,
and all other members avoid T. Thus for every open W contained in a distinct overlap,
the reduced-cover section bijection applies. This proves all the asserted clauses.
If T is empty take only component neighborhoods; if Y is empty take the empty cover.
No transition unit, cocycle, glued module, or global section is constructed here.
(blueprint: lem-sc-normalized-component-section-cover) -/
theorem exists_normalized_component_section_cover
    {Y : Scheme.{u}} [IsReduced Y] {ι : Type v} [Finite ι]
    (Z : ι → Scheme.{u}) (i : ∀ a : ι, Z a ⟶ Y) [∀ a : ι, IsClosedImmersion (i a)]
    (hcover : (⋃ a : ι, Set.range (i a)) = Set.univ)
    (hdiscrete : ∀ a b : ι, a ≠ b →
      DiscreteTopology ↥(Set.range (i a) ∩ Set.range (i b)))
    (M : ∀ a : ι, (Z a).Modules) [∀ a : ι, (M a).IsInvertible]
    (s : ∀ a : ι, Γ(M a, ⊤))
    (hs : ∀ a b : ι, a ≠ b → Set.range (i a) ∩ Set.range (i b) ⊆
      i a '' nonvanishingLocus (M a) (s a)) :
    ∃ (κ : Type (max u v)) (U : κ → Y.Opens) (f : ∀ b, Γ(Y, U b))
      (m : ∀ a b, Γ(M a, (i a) ⁻¹ᵁ U b)),
      (⨆ b, U b) = ⊤ ∧
      (∀ a b, IsFreeGenerator (m a b)) ∧
      (∀ a b, (M a).presheaf.map (homOfLE le_top).op (s a) =
        ((i a).app (U b)).hom (f b) • m a b) ∧
      ∀ b c, b ≠ c → ∀ (W : Y.Opens), W ≤ U b → W ≤ U c →
        Function.Bijective
          (fun r : Γ(Y, W) ↦ fun a ↦ ((i a).app W).hom r) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
