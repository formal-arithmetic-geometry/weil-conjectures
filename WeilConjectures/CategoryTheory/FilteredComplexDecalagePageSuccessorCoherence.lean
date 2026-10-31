/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.FilteredComplexDecalagePageIso
public import WeilConjectures.CategoryTheory.FilteredComplexCanonicalModel
public import WeilConjectures.CategoryTheory.FilteredComplexDecalagePageData
import WeilConjectures.CategoryTheory.FilteredComplexDecalageTower
/-! Successor compatibility split from the normalized decalage page coherence.
Source: Stacks Project, Tag 015X, Remark 13.26.15; blueprint:
lem-sp-filtered-complex-decalage-page-successor-coherence. -/
@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C]
/-- The fixed normalized page comparison commutes with the successor homology maps.
Source: Stacks Project, Tag 015X, Remark 13.26.15, second filtration; blueprint:
lem-sp-filtered-complex-decalage-page-successor-coherence.
Proof. Cover successor cycles epimorphically, expand the spectral homology-data
factorization, apply the representative class transition equation, and cancel the target
interval monomorphism.
(blueprint: lem-sp-filtered-complex-decalage-page-successor-coherence). -/
theorem filteredComplex_decalage_page_successor_coherence
    (U : FilteredObject (CochainComplex C ℤ)) :
    ∀ (r : ℤ) (hr : 2 ≤ r)
    (f : ((filteredComplexCanonicalModel C).S.obj U).page r hr ⟶
      (((filteredComplexDecalageSpectralObjectFunctor C).obj U).E₂SpectralSequence).page r hr),
    (∀ pq : ℤ × ℤ, f.f pq = (filteredComplexDecalagePageIso U pq.1 pq.2 r hr).hom) →
    ∀ pq : ℤ × ℤ,
      HomologicalComplex.homologyMap f pq ≫
          ((((filteredComplexDecalageSpectralObjectFunctor C).obj U).E₂SpectralSequence).iso
            r (r + 1) pq rfl hr).hom =
        (((filteredComplexCanonicalModel C).S.obj U).iso r (r + 1) pq rfl hr).hom ≫
          (filteredComplexDecalagePageIso U pq.1 pq.2 (r + 1) (by omega)).hom := by
  sorry
end CategoryTheory
