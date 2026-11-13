/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

import WeilConjectures.AlgebraicGeometry.RestrictedCohomologyColimit

/-!
# Representatives of restricted cohomology classes from a supplied filtered colimit

Source: Stacks Project, Tag 03Q5, with the colimit
preservation and module compatibility used in the proof of Tag 03SA(3).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- A class in the restriction of a supplied filtered colimit of module sheaves is
represented at one of its stages. The diagram objects need not be constructible.
Source: Stacks Project, Tag 03Q5; used after Tag 03SA(3). -/
theorem exists_restriction_class_of_filtered_presentation
    {X X₀ : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace X₀] [QuasiSeparatedSpace X₀] (i : X₀ ⟶ X)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A : Type (u + 1)} [SmallCategory A] [IsFiltered A]
    {D : A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ι : D ⟶ (Functor.const A).obj F)
    (hc : Nonempty (IsColimit (Cocone.mk F ι)))
    (q : ℕ)
    (c : Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj ((i)^*[ModuleCat.{u + 1} Λ].obj F)) q) :
    ∃ (a : A) (z : Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj ((i)^*[ModuleCat.{u + 1} Λ].obj (D.obj a))) q),
      Sheaf.H.map ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
        AddCommGrpCat.{u + 1})).map ((i)^*[ModuleCat.{u + 1} Λ].map (ι.app a))) q z = c := by
  obtain ⟨h⟩ := restrictedCohomology_isColimit i Λ ι hc q
  exact Concrete.isColimit_exists_rep _ h c

end AlgebraicGeometry.Etale
