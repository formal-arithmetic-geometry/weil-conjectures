/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Defs.Filter
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Spectral.Basic
import WeilConjectures.Topology.SpectralGeneralizations

/-!
# Compact images of flat relations as intersections of compact opens

Source: Stacks Project, Groupoids, Tag 0APA (`lemma-first-observation`), proof.
(blueprint: lem-a1-flat-relation-qc-image-intersections).

The family consists of subsets of the ambient scheme contained in `H₂`. Since `H₂`
is open, these are exactly its relatively open compact subsets containing the image.
No relation laws are assumed.
-/

@[expose] public section

universe u

open CategoryTheory Set Topology

namespace AlgebraicGeometry

/-- For flat quasi-compact maps `s,t : R ⟶ V`, with `V` quasi-separated, the image
`t(s⁻¹(H))` of a compact open is compact and closed under generalization. It has a
compact open neighbourhood, and inside every such neighbourhood it is the intersection
of all compact opens containing it. The displayed family is a nonempty set of subsets
of `V`, and its membership predicate includes ambient openness and compactness.

Source: Stacks Project, Groupoids, Tag 0APA (`lemma-first-observation`), proof.
(blueprint: lem-a1-flat-relation-qc-image-intersections).

Proof plan:
1. Cover `H` by affine opens (lem-weil-pbc-affine-opens-basis) and extract a finite
   subcover. Quasi-compactness of `s` (def-weil-finite-type-morphism) makes each
   inverse image compact, hence their finite union `s⁻¹(H)` compact. Its continuous
   image under `t` is compact (lem-weil-pbc-continuous-image-quasi-compact).
2. Given `y = t(r)` in the image and `y ∈ closure {y'}`, lift the generalization
   along the flat map `t` (lem-weil-pbc-flat-generalizations-lift). The lifted point
   remains in the open `s⁻¹(H)`, so `y'` is in the image.
3. Affine open neighbourhoods of the image points cover it; compactness gives
   finitely many. Their union is open and compact by lem-weil-pbc-affine-opens-basis
   and lem-weil-pbc-affine-scheme-qcqs. For empty image take the empty union.
4. Every compact open `H₂` containing the image is quasi-separated: its affine
   opens are affine opens of `V`, with compact pairwise intersections by
   lem-weil-pbc-quasi-separated-affine-cover-criterion. Apply both clauses of that
   criterion, then lem-weil-pbc-qcqs-scheme-spectral, to make `H₂` spectral.
5. Apply lem-weil-pbc-spectral-generalizations-of-quasi-compact inside `H₂`.
   The image equals its generalization set by step 2 and reflexivity. Thus it is
   the intersection of all compact open supersets in `H₂`. Such opens are open in
   `V`; their induced topology, and hence compactness, is unchanged. The family
   contains `H₂` itself. Its nonemptiness makes the same intersection in `V`
   exclude points outside `H₂`, including when the image and `H₂` are empty. -/
theorem flat_relation_qc_image_intersections
    {R V : Scheme.{u}} [QuasiSeparatedSpace V] (s t : R ⟶ V)
    [Flat s] [QuasiCompact s] [Flat t] [QuasiCompact t]
    (H : V.Opens) (hH : IsCompact (H : Set V)) :
    IsCompact (t '' (s ⁻¹' (H : Set V))) ∧
      (∀ y ∈ t '' (s ⁻¹' (H : Set V)), ∀ y' : V,
        y ∈ closure ({y'} : Set V) → y' ∈ t '' (s ⁻¹' (H : Set V))) ∧
      (∃ H₂ : V.Opens, IsCompact (H₂ : Set V) ∧
        t '' (s ⁻¹' (H : Set V)) ⊆ (H₂ : Set V)) ∧
      (∀ H₂ : V.Opens, IsCompact (H₂ : Set V) →
        t '' (s ⁻¹' (H : Set V)) ⊆ (H₂ : Set V) →
        {U : Set V | U ⊆ (H₂ : Set V) ∧ IsOpen U ∧ IsCompact U ∧
          t '' (s ⁻¹' (H : Set V)) ⊆ U}.Nonempty ∧
        t '' (s ⁻¹' (H : Set V)) =
          ⋂₀ {U : Set V | U ⊆ (H₂ : Set V) ∧ IsOpen U ∧ IsCompact U ∧
            t '' (s ⁻¹' (H : Set V)) ⊆ U}) := by
  sorry

end AlgebraicGeometry
