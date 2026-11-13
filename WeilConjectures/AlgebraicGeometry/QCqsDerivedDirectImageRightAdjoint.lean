/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSumsAux
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesDirectSums
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.AlgebraicGeometry.DerivedQCohCompactGeneration
import WeilConjectures.CategoryTheory.BrownRepresentabilityHomLocallySmall
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Right adjoint to derived direct image on quasi-coherent complexes

## References

* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- For a qcqs morphism between qcqs schemes, derived direct image preserves quasi-coherent
cohomology, and its restriction to the full quasi-coherent derived categories has a right
adjoint.
-/
theorem schemeDerivedDirectImage_qcqs_hasRightAdjoint (X Y : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    ∃ hpres : ∀ E : schemeDerivedCategory X, schemeDerivedQCohProperty X E →
        schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E),
      ((schemeDerivedQCohProperty Y).lift
        ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
        (fun E ↦ hpres E.obj E.property)).IsLeftAdjoint := by
  let hpres := schemeDerivedDirectImage_preserves_QCoh f
  refine ⟨hpres, ?_⟩
  obtain ⟨hX, hXs, hCg⟩ := schemeDerivedQCoh_compactlyGenerated X
  obtain ⟨hY, hYs, _⟩ := schemeDerivedQCoh_compactlyGenerated Y
  let := hX
  let := hY
  let := hXs
  let := hYs
  let F := (schemeDerivedQCohProperty Y).lift
    ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (fun E ↦ hpres E.obj E.property)
  let hshift : F.CommShift ℤ := inferInstance
  let hambient : (schemeDerivedDirectImage f).IsTriangulated := inferInstance
  let hcomp : ((schemeDerivedQCohProperty X).ι ⋙
      schemeDerivedDirectImage f).IsTriangulated := inferInstance
  let : F.IsTriangulated := by
    apply ObjectProperty.isTriangulated_lift
  let : LocallySmall.{u} (schemeDerivedQCohCategory X) := inferInstance
  let : LocallySmall.{u} (schemeDerivedQCohCategory Y) := inferInstance
  have hF : ∀ I : Type u, CategoryTheory.Limits.PreservesColimitsOfShape (Discrete I) F := by
    intro I
    let : CategoryTheory.Limits.HasCoproducts.{u} (schemeDerivedCategory X) :=
      derivedAmbientHasCoproducts X
    let : (schemeDerivedQCohProperty X).IsClosedUnderColimitsOfShape (Discrete I) :=
      schemeDerivedQCohClosedUnderCoproducts X I
    constructor
    intro K
    let : CategoryTheory.Limits.PreservesColimit (K ⋙ (schemeDerivedQCohProperty X).ι)
        (schemeDerivedDirectImage f) := by
      let : CategoryTheory.Limits.PreservesColimit
          (Discrete.functor ((K ⋙ (schemeDerivedQCohProperty X).ι).obj ∘ Discrete.mk))
          (schemeDerivedDirectImage f) :=
        derivedDirectImagePreservesDirectSums f I (fun i ↦ K.obj ⟨i⟩)
      exact CategoryTheory.Limits.preservesColimit_of_iso_diagram _
        Discrete.natIsoFunctor.symm
    let : CategoryTheory.Limits.PreservesColimit K
        ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) := inferInstance
    let : CategoryTheory.Limits.PreservesColimit K (F ⋙ (schemeDerivedQCohProperty Y).ι) :=
      CategoryTheory.Limits.preservesColimit_of_natIso K
        ((schemeDerivedQCohProperty Y).liftCompιIso _ _).symm
    exact CategoryTheory.Limits.preservesColimit_of_reflects_of_preserves F
      (schemeDerivedQCohProperty Y).ι
  apply Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
  funext E
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    exact brownHomRepresentabilityLocallySmall F hCg hF E

end AlgebraicGeometry
