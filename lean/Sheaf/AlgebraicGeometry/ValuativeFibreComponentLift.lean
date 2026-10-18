/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Valuation.ValuationRing
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import WeilConjectures.Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Valuative base change lifting two fibre components

Source: Stacks Project, Tag 0GSH, Lemma `lemma-make-base-change`, all four clauses.
(blueprint: lem-trf-valuative-fibre-component-lift)

The reduced integral closures are represented by integral closed immersions with the
specified underlying images. Points of their fibres are kept as points of the actual
scheme-theoretic fibres, with `fiberι` giving their images in the ambient schemes.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

/-- A valuation-ring base change lifts a generic component point in each of the two fibres.

Source: Stacks Project, Tag 0GSH, all four clauses.
(blueprint: lem-trf-valuative-fibre-component-lift)

Here `i : Y ⟶ X` presents the reduced integral closure of `y`; `x` is a point of its
scheme-theoretic fibre, and its image in `X` is `i ((i ≫ f).fiberι s x)`. The point `z`
lies in the generic fibre of `Y ×_S Spec A`; its image under the canonical base-change
closed immersion is `y'`. By the canonical fibre base-change identification this is
exactly `Y_t ×_{Spec κ(t)} Spec κ(t')`. The integral closed immersion `i'` presents
the reduced closure of `y'`, and `x'` is the required point of its special fibre.

Proof:
1. The point `y` specializes to the image of `x`. Apply
   `lem-trf-valuation-ring-specialization-lift`, namely
   `Scheme.exists_valuationSubring_of_specializes` (Stacks 01J8), to obtain a valuation
   ring and `h : Spec A ⟶ X` realizing the specialization. Set `g = h ≫ f`.
2. The pullback universal property (`def-pc-base-change`, `def-pc-fibre-product`) gives
   a section of `X ×_S Spec A ⟶ Spec A`. Since `h` factors through the reduced closure
   `Y`, this section factors through `Y ×_S Spec A`.
3. Choose the generic point of a component of its generic fibre containing the section's
   generic point. Its image in `X` generalizes `y` within `Y_t`, hence equals `y`:
   `y` is the generic point of the irreducible fibre `Y_t`. This gives `z` and `y'`.
4. The section factors through the reduced closure `Y'` of `y'`. Choose the generic
   point `x'` of a component of its special fibre containing the section's closed point.
   Its image in `Y_s` generalizes `x`; maximality of the component of `x` and uniqueness
   of generic points imply equality. These are precisely the final image and component
   conditions (`def-pc-integral-scheme`, `def-pc-scheme-fibre`, `def-sc-generic-point`,
   `def-weil-irreducible-components`). -/
theorem exists_valuative_fibre_component_lift {X S Y : Scheme.{u}} (f : X ⟶ S)
    (y : X) (i : Y ⟶ X) [IsIntegral Y] [IsClosedImmersion i]
    (hY : Set.range i = closure ({y} : Set X)) (s : S) (x : (i ≫ f).fiber s)
    (C : Set ((i ≫ f).fiber s)) (hC : C ∈ irreducibleComponents ((i ≫ f).fiber s))
    (hx : IsGenericPoint x C) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (g : Spec (CommRingCat.of A) ⟶ S)
      (t' s' : Spec (CommRingCat.of A)),
      IsGenericPoint t' Set.univ ∧ IsClosed ({s'} : Set (Spec (CommRingCat.of A))) ∧
      g t' = f y ∧ g s' = s ∧
      ∃ (z : (pullback.snd (i ≫ f) g).fiber t')
        (D : Set ((pullback.snd (i ≫ f) g).fiber t')),
        D ∈ irreducibleComponents ((pullback.snd (i ≫ f) g).fiber t') ∧
        IsGenericPoint z D ∧
        ∃ y' : (pullback f g : Scheme.{u}),
          (pullback.snd f g) y' = t' ∧ (pullback.fst f g) y' = y ∧
          (pullback.map (i ≫ f) g f g i (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id g).trans (Category.id_comp g).symm))
            ((pullback.snd (i ≫ f) g).fiberι t' z) = y' ∧
          ∃ (Y' : Scheme.{u}) (_ : IsIntegral Y') (i' : Y' ⟶ pullback f g)
            (_ : IsClosedImmersion i'),
            Set.range i' = closure ({y'} : Set (pullback f g : Scheme.{u})) ∧
            ∃ (x' : (i' ≫ pullback.snd f g).fiber s')
              (E : Set ((i' ≫ pullback.snd f g).fiber s')),
              E ∈ irreducibleComponents ((i' ≫ pullback.snd f g).fiber s') ∧
              IsGenericPoint x' E ∧
              (pullback.fst f g) (i' ((i' ≫ pullback.snd f g).fiberι s' x')) =
                i ((i ≫ f).fiberι s x) := by
  sorry

end AlgebraicGeometry
