/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.AlgebraicGeometry.OverlapPairCanonicalComparisons

/-! # A step of persistent pairwise overlap lifting

Source: Stacks Project, Tag 01ZR, first proof.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

/-- A compatible map on one pair stays compatible under refinement of the stage.
No finite presentation, quasi-coherence, affineness or limit hypothesis is used.
Source: Stacks Project, Tag 01ZR, first proof, successive Zariski restrictions;
Mathlib pseudofunctor pullHom composition and pullback overlapIteratedComparison coherence.
(blueprint: lem-pc-fp-overlap-pair-refinement-persistence).

Proof: For each chart use overlapRefinementHom U q q' r hr to map the later
chart to the earlier one. Pull the given pair map along the induced map of the
universal overlaps. Conjugate by pullback composition and the equality
of the composites with the original chart projections to obtain a map between
the prescribed later modules. The limit charts of the later cover map to those
of the earlier cover because p' followed by r is p. Pull back the given square
along the induced map of limit overlaps. Naturality of mapComp and the
pseudofunctor pentagon identify its left and right component comparisons with
overlapIteratedComparison U q' p' t h' N M e. PullHom composition identifies its middle map
with the pullback of the newly constructed stage map. The descent datum of M
is natural under this overlap map, so the resulting equality is the desired
square. These constructions use universal pullback maps, and still apply when
a chart or overlap is empty; no map is chosen from a mere existence statement. -/
theorem overlap_pair_map_refinement_persistence
    {X Y Y' Z : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (q' : Y' ⟶ X) (r : Y' ⟶ Y) (hr : r ≫ q = q')
    (p : Z ⟶ Y) (p' : Z ⟶ Y') (t : Z ⟶ X)
    (h : p ≫ q = t) (h' : p' ≫ q' = t) (hp : p' ≫ r = p)
    (N : (a : U.I₀) → (U.X a).Modules) (M : Z.Modules)
    (e : ∀ a, (Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a) ≅
      (Scheme.Modules.pullback ((U.pullback₁ t).f a)).obj M)
    (a b : U.I₀) :
    let V := U.pullback₁ q
    let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
    let W := V.pullback₁ p
    let D := (modulesPseudofunctor.toDescentData W.f).obj M
    let ε := overlapIteratedComparison U q p t h N M e
    (∃ φ : (Scheme.Modules.pullback (pullback.fst (V.f a) (V.f b))).obj (A a) ⟶
        (Scheme.Modules.pullback (pullback.snd (V.f a) (V.f b))).obj (A b),
      overlapPairSquare V A p D ε a b φ) →
    let V' := U.pullback₁ q'
    let A' := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q' d)).obj (N d)
    let W' := V'.pullback₁ p'
    let D' := (modulesPseudofunctor.toDescentData W'.f).obj M
    let ε' := overlapIteratedComparison U q' p' t h' N M e
    ∃ φ' : (Scheme.Modules.pullback (pullback.fst (V'.f a) (V'.f b))).obj (A' a) ⟶
        (Scheme.Modules.pullback (pullback.snd (V'.f a) (V'.f b))).obj (A' b),
      overlapPairSquare V' A' p' D' ε' a b φ' := by sorry

end AlgebraicGeometry
