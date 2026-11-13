/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.ConstructibleFilteredData
import WeilConjectures.AlgebraicGeometry.ConstructibleColimitCocone

/-!
# Constructible filtered presentations of etale module sheaves

Source: Stacks Project, Tag 03SA, part (3).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every module sheaf on the small etale site of a quasi-compact quasi-separated scheme,
with coefficients in a finite commutative ring, admits a filtered colimit presentation
by constructible module sheaves. The maps and the universal property are in the category
of module-valued sheaves, the constant-ring module-sheaf encoding used by
`IsConstructibleEtaleModuleSheaf`.

Source: Stacks Project, Tag 03SA(3). -/
theorem exists_filtered_colimit_constructible
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ (A : Type (u + 1)) (_ : SmallCategory A) (_ : IsFiltered A)
      (D : A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (∀ a : A, IsConstructibleEtaleModuleSheaf (D.obj a)) ∧
        ∃ ι : D ⟶ (Functor.const A).obj F,
          Nonempty (IsColimit (Cocone.mk F ι)) := by
  obtain ⟨A, hA, hfiltered, D, ι, hconstructible, hfactor, hrelations⟩ :=
    exists_filtered_constructible_data F
  let := hA
  let := hfiltered
  exact ⟨A, hA, hfiltered, D, hconstructible, ι,
    exists_constructible_colimit_cocone F A D ι hfactor hrelations⟩

end AlgebraicGeometry.Scheme
