module
public import Sheaf.CategoryTheory.FilteredComplexDecalagePageIso
public import Sheaf.CategoryTheory.FilteredComplexCanonicalModel
public import Sheaf.CategoryTheory.FilteredComplexDecalagePageData
import Sheaf.CategoryTheory.FilteredComplexDecalageTower
/-! Differential compatibility split from the normalized decalage page coherence.
Source: Stacks Project, Tag 012K, section-filtered-complex; blueprint:
lem-sp-filtered-complex-decalage-page-differential-coherence. -/
@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C]
/-- The fixed normalized page comparison commutes with the page differential.
Source: Stacks Project, Tag 012K, the displayed differential formula; blueprint:
lem-sp-filtered-complex-decalage-page-differential-coherence.
Proof. Compare both composites on the epimorphic family of unquotiented cycle representatives,
use the spectral-object differential formula and the interval connecting representative
equation, then cancel the target interval monomorphism.
(blueprint: lem-sp-filtered-complex-decalage-page-differential-coherence). -/
theorem filteredComplex_decalage_page_differential_coherence
    (U : FilteredObject (CochainComplex C ℤ)) :
    ∀ (r : ℤ) (hr : 2 ≤ r) (i j : ℤ × ℤ),
    (filteredComplexDecalagePageIso U i.1 i.2 r hr).hom ≫
        ((((filteredComplexDecalageSpectralObjectFunctor C).obj U).E₂SpectralSequence).page
          r hr).d i j =
      (((filteredComplexCanonicalModel C).S.obj U).page r hr).d i j ≫
        (filteredComplexDecalagePageIso U j.1 j.2 r hr).hom := by
  sorry
end CategoryTheory
