/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Filtered-colimit comparison on finite spectral-sequence pages

Source: Stacks Project, Tag 0EZM, the finite-term comparison in the proof,
and Tag 00DB, homology commuting with directed colimits.
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

/-- Page-one comparison propagates to each finite page, without convergence hypotheses.

Source: Stacks Project, Tag 0EZM, the spectral-sequence comparison in the proof;
Tag 00DB, homology commuting with directed colimits.

Proof: induct on the natural number `r - 1`. The initial case is `hpage`.
For the induction step, form the diagram of page-r complexes. Evaluation of its
colimit is the colimit of its evaluations, since colimits of complexes are degreewise.
The compatible page maps give a chain map from this colimit complex to the target
page. Its components are isomorphisms by induction, so it is an isomorphism of
complexes. Filtered-colimit exactness (Tag 00DB) identifies the homology of this
colimit complex with the colimit of the page-r homologies. The spectral sequences'
page-to-page isomorphisms identify these homologies with page r+1, naturally in
all transition and comparison maps. Thus the canonical map on page r+1 is an
isomorphism. Any map satisfying the displayed cocone equations equals the canonical
one by the colimit universal property. If I is empty, all source colimits are zero;
the initial hypothesis then forces every target page-one term to be zero, and all
later pages are zero as well, so this case also satisfies the conclusion.
(blueprint: lem-weil-pbc-spectral-sequence-finite-page-comparison) -/
theorem spectral_sequence_finite_page_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (E : I ⥤ SpectralSequence AddCommGrpCat.{u}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
    (E' : SpectralSequence AddCommGrpCat.{u}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
    (v : ∀ i : I, E.obj i ⟶ E')
    (hv : ∀ {i j : I} (f : i ⟶ j), E.map f ≫ v j = v i)
    (hpage : ∀ (p q : ℤ)
      (φ : colimit (E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 1 ⋙
        HomologicalComplex.eval _ _ ⟨p, q⟩) ⟶ (E'.page 1).X ⟨p, q⟩),
      (∀ i : I, colimit.ι _ i ≫ φ = ((v i).hom 1).f ⟨p, q⟩) → IsIso φ) :
    ∀ (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
      (φ : colimit (E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 r hr ⋙
        HomologicalComplex.eval _ _ ⟨p, q⟩) ⟶ (E'.page r hr).X ⟨p, q⟩),
      (∀ i : I, colimit.ι _ i ≫ φ = ((v i).hom r hr).f ⟨p, q⟩) → IsIso φ := by
  sorry

end CategoryTheory
