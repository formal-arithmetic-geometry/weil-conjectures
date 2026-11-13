/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.GlobalGenerationNonvanishingCover
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus

/-!
# Finite nonvanishing covers from global generation

## References

* Stacks Project, Varieties, Lemma 09NC.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A globally generated invertible module on a quasi-compact scheme has finitely many
sections whose nonvanishing loci `nonvanishingLocus L (t j)` cover the scheme
(Stacks, Lemma 09NC). -/
theorem finite_sections_cover_of_globally_generated (X : Scheme.{u}) [CompactSpace X]
    (L : X.Modules) [L.IsInvertible]
    (hgen : Nonempty (SheafOfModules.GeneratingSections L)) :
    ∃ (m : ℕ) (t : Fin m → L.val.presheaf.obj (Opposite.op ⊤)),
      ⋃ j, nonvanishingLocus L (t j) = Set.univ := by
  classical
  have hopen (s : L.val.presheaf.obj (Opposite.op ⊤)) :
      IsOpen (nonvanishingLocus L s) := by
    rw [nonvanishingLocus_eq_compl_support_zeroLocus X L s]
    exact (Hom.zeroLocus (homOfGlobalSection L s)).support.compl.isOpen
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (nonvanishingLocus L) hopen
    (by rw [globalGeneration_nonvanishing_cover X L hgen])
  let e := S.equivFin
  refine ⟨S.card, fun j ↦ (e.symm j).val, Set.eq_univ_of_forall fun x ↦ ?_⟩
  obtain ⟨s, hx⟩ := Set.mem_iUnion.mp (hS (Set.mem_univ x))
  obtain ⟨hs, hx⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨e ⟨s, hs⟩, by simpa using hx⟩

end AlgebraicGeometry.Scheme.Modules
