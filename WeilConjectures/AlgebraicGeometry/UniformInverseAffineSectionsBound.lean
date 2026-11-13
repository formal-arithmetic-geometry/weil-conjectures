/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleCohomology
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.LocalUniformHigherDirectImageBound
import WeilConjectures.AlgebraicGeometry.AffineOpenHigherDirectImageSectionsIso
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Uniform cohomological dimension of inverse images of affine opens

## References

* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A single positive bound works for ordinary module cohomology on the inverse image
of every affine open of the target. -/
theorem exists_uniform_inverse_affine_sections_bound
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] :
    ∃ N : ℕ, 0 < N ∧ ∀ (U : S.Opens), IsAffineOpen U →
      ∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)), M.IsQuasicoherent →
        ∀ p : ℕ, N ≤ p → IsZero
          (((RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ U)).rightDerived p).obj M) :=
  by
  classical
  choose V n hs hn using exists_local_uniform_higherDirectImage_bound f
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun s ↦ (V s : Set S))
    (fun s ↦ (V s).isOpen) (fun s _ ↦ Set.mem_iUnion.mpr ⟨s, hs s⟩)
  refine ⟨max 1 (t.sup n), lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), ?_⟩
  intro U hU M hM p hp
  have hcover : (⨆ s : t, V s) = ⊤ := by
    apply eq_top_iff.mpr
    intro s _
    obtain ⟨i, hi, hsi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ s))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hsi⟩
  have hz : IsZero
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj M) := by
    apply Scheme.Modules.isZero_of_iSup_eq_top _ (fun s : t ↦ V s) hcover
    intro s
    exact hn s M hM p ((Finset.le_sup s.property).trans ((le_max_right _ _).trans hp))
  obtain ⟨e⟩ := nonempty_affineOpen_higherDirectImage_sections_iso f U hU M hM p
  exact ((RingedSpace.openModuleSections S.toRingedSpace U).map_isZero hz).of_iso e

end AlgebraicGeometry
