/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q49
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Restrict

import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Generic-fibre restriction on a reduced horizontal source

Source: Stacks Project, Tag 0AY8, proof of
`lemma-geometrically-connected-fibres-towards-normal`, reducedness and component dominance;
Tag 03GY, proof of `lemma-stein-universally-closed`, nilpotent-section argument
(blueprint: lem-trf-reduced-dominant-generic-restriction).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Restriction to the generic fibre detects sections on any quasi-compact open of a reduced
scheme whose component generic points all map to the generic point of the integral base.
The map first identifies sections on the ambient open with global sections of its open
subscheme by `V.topIso.inv`, and then pulls back along the actual fibre projection.

Source: Stacks Project, Tag 0AY8, proof of
`lemma-geometrically-connected-fibres-towards-normal`, reducedness and component dominance;
Tag 03GY, proof of `lemma-stein-universally-closed`, surjectivity paragraph.
(blueprint: lem-trf-reduced-dominant-generic-restriction)

Proof:
1. Let a section have zero pullback. Every component generic point in `V` maps to `ξ`
   by the hypothesis and therefore lifts to the fibre (def-pc-scheme-fibre). Evaluation
   of the pullback there is the image of the section's value in the induced residue-field
   map (def-weil-residue-field). A unital map of fields is injective, so the section
   vanishes at each such component generic point.
2. The nonvanishing locus is open (lem-weil-pbc-basic-open-function). A point of this
   locus belongs to an irreducible component (lem-sc-irreducible-components-cover).
   That component has a generic point (lem-sc-scheme-sober), and every open containing
   the original point contains this generic point (def-sc-generic-point). This
   contradicts step 1. Thus the section vanishes in every residue field on `V`.
3. Quasi-compactness makes the section nilpotent
   (lem-weil-pbc-qc-scheme-vanishing-section-nilpotent). Reducedness then makes it zero
   (def-pc-reduced-scheme). Apply this to the difference of two sections with equal
   pullbacks. This also covers the empty open without choosing a point. -/
theorem Scheme.Hom.injective_genericFiber_restriction_of_isReduced
    {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegral S] [IsReduced X]
    (ξ : S) (hξ : IsGenericPoint ξ Set.univ)
    (hcomponents : ∀ (C : Set X), C ∈ irreducibleComponents X →
      ∀ (η : X), IsGenericPoint η C → f η = ξ)
    (V : X.Opens) [CompactSpace V] :
    Function.Injective (V.topIso.inv ≫ ((V.ι ≫ f).fiberι ξ).appTop) := by
  sorry

end AlgebraicGeometry
