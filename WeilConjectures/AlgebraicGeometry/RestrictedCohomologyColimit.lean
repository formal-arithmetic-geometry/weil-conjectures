/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Mathlib.CategoryTheory.Presentable.Directed
import WeilConjectures.AlgebraicGeometry.ConstantModuleSheavesForgetColimits
import WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimit
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison

/-!
# Canonical filtered colimit cocones of restricted cohomology

## References

* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 03DB](https://stacks.math.columbia.edu/tag/03DB)
* [Stacks Project, Tag 03CO](https://stacks.math.columbia.edu/tag/03CO)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Restricted underlying abelian cohomology carries a supplied filtered colimit
cocone to a colimit cocone. This asserts the universal property, with the canonical
legs, before any representative is selected. -/
theorem restrictedCohomology_isColimit
    {X X₀ : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace X₀] [QuasiSeparatedSpace X₀] (i : X₀ ⟶ X)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A : Type (u + 1)} [SmallCategory A] [IsFiltered A]
    {D : A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ι : D ⟶ (Functor.const A).obj F)
    (hc : Nonempty (IsColimit (Cocone.mk F ι)))
    (q : ℕ) :
    Nonempty (IsColimit
      (((i)^*[ModuleCat.{u + 1} Λ] ⋙
        sheafCompose X₀.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙
        Sheaf.functorH X₀.smallEtaleTopology q).mapCocone (Cocone.mk F ι))) := by
  obtain ⟨hc⟩ := hc
  let U := (i)^*[ModuleCat.{u + 1} Λ]
  let V := sheafCompose X₀.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let E := Sheaf.functorH X₀.smallEtaleTopology q
  let c := V.mapCocone (U.mapCocone (Cocone.mk F ι))
  have : PreservesColimitsOfSize.{u + 1, u + 1} V :=
    constantModuleSheaves_forget_preservesColimits X₀ Λ
  have h : IsColimit c := isColimitOfPreserves V (isColimitOfPreserves U hc)
  obtain ⟨I, horder, hdirected, hnonempty, T, hfinal⟩ := IsFiltered.exists_directed A
  let := horder
  let := hdirected
  let := hnonempty
  let := hfinal
  have hT : IsColimit (c.whisker T) :=
    (Functor.Final.isColimitWhiskerEquiv T c).symm h
  obtain ⟨hR⟩ := Scheme.etaleCohomology_isColimit_of_isDirected X₀ hT q
  obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso X₀ q
  have hE : IsColimit (E.mapCocone (c.whisker T)) :=
    IsColimit.mapCoconeEquiv e.symm hR
  exact ⟨(Functor.Final.isColimitWhiskerEquiv T (E.mapCocone c)) hE⟩

end AlgebraicGeometry.Etale
