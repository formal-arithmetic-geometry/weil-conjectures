/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen
import Mathlib.Topology.NoetherianSpace

/-!
# Bounded fibre-dimension loci pulled back from a Noetherian model

Source: Stacks Project, Algebra, Tag 00QJ,
lemma-dimension-fibres-bounded-quasi-compact-open-upstairs, inverse-image paragraph
and final Noetherian quasi-compactness sentence; Morphisms, Tags 02FY(1) and 02FZ
(blueprint: lem-trf-noetherian-model-dimension-locus-pullback).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The bounded local fibre-dimension locus is the inverse image of the corresponding
locus on a locally Noetherian quasi-compact model. Both loci are open and quasi-compact
when the projection to the model is quasi-compact. Local finite type of `h₀` suffices;
no finite presentation or Noetherianity of the base or the pullback is assumed.

Source: Stacks Project, Algebra, Tag 00QJ,
lemma-dimension-fibres-bounded-quasi-compact-open-upstairs, inverse-image paragraph
and final Noetherian quasi-compactness sentence
(blueprint: lem-trf-noetherian-model-dimension-locus-pullback).

Proof:
1. Apply `fibre_dimension_after_base_change` (lem-sc-fibre-dimension-after-base-change,
   Morphisms 02FY(1)) to `h₀`, `g`, and each point of `pullback h₀ g`. Its dimension
   equality makes membership in the pullback locus equivalent to membership of its
   image under `pullback.fst h₀ g` in the model locus. Extensionality gives the equality.
2. Apply `isOpen_localFibreDimension_le` (lem-weil-pbc-local-fibre-dimension-open,
   Morphisms 02FZ) to `h₀` and `n`. Continuity of the projection and step 1 give
   openness of the pullback locus.
3. Local Noetherianity gives an affine cover by Noetherian coordinate rings
   (pqf-def-locnoeth). Compactness of `X₀` supplies a finite subcover
   (def-weil-pbc-quasi-compact-scheme). Each chart has Noetherian underlying space by
   `noetherianSpace_of_isAffine` (lem-sc-affine-noetherian-underlying-space).
   The intersection of the model locus with each chart is compact by
   `TopologicalSpace.NoetherianSpace.isCompact`
   (lem-sfb-noetherian-space-compact-subsets). A finite union is compact: restrict
   an arbitrary open cover to each chart and combine its finitely many finite
   subcovers. This includes the empty scheme and the empty finite cover.
4. Apply `Scheme.Hom.isCompact_preimage`
   (lem-weil-pbc-quasi-compact-morphism-preimage-qc-open) to the quasi-compact
   projection and the compact open model locus. Step 1 identifies this compact
   inverse image with the pullback locus. -/
theorem noetherianModel_localFibreDimension_locus_pullback {X₀ S₀ S : Scheme.{u}}
    (h₀ : X₀ ⟶ S₀) [LocallyOfFiniteType h₀] [IsLocallyNoetherian X₀]
    [CompactSpace X₀] (g : S ⟶ S₀) [QuasiCompact (pullback.fst h₀ g)] (n : ℕ) :
    {x : ↥(pullback h₀ g) |
        topologicalKrullDimAt ((pullback.snd h₀ g).asFiber x) ≤ (n : WithBot ℕ∞)} =
      (pullback.fst h₀ g) ⁻¹'
        {x₀ : X₀ | topologicalKrullDimAt (h₀.asFiber x₀) ≤ (n : WithBot ℕ∞)} ∧
    (IsOpen {x₀ : X₀ | topologicalKrullDimAt (h₀.asFiber x₀) ≤ (n : WithBot ℕ∞)} ∧
      IsCompact {x₀ : X₀ | topologicalKrullDimAt (h₀.asFiber x₀) ≤ (n : WithBot ℕ∞)}) ∧
    (IsOpen {x : ↥(pullback h₀ g) |
        topologicalKrullDimAt ((pullback.snd h₀ g).asFiber x) ≤ (n : WithBot ℕ∞)} ∧
      IsCompact {x : ↥(pullback h₀ g) |
        topologicalKrullDimAt ((pullback.snd h₀ g).asFiber x) ≤ (n : WithBot ℕ∞)}) := by
  sorry

end AlgebraicGeometry
