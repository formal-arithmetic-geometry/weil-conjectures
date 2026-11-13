/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.AlgebraicGeometry.KoszulRegularImmersionDualizingProperty
import WeilConjectures.AlgebraicGeometry.KoszulRegularImmersionAlgebraDual
import WeilConjectures.AlgebraicGeometry.FiniteAffineDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.FiniteDualityDerivedHom
import WeilConjectures.AlgebraicGeometry.AffineDerivedHomEvaluationCounit

/-! # Dualizing object of a Koszul-regular closed immersion

## References

* Stacks Project, Duality for Schemes, Tag 0BR0, with Tag 0BQZ.
-/

@[expose] public section

universe u wZ wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The right adjoint applied to the structure sheaf is the shifted top exterior power
of the normal sheaf, with the shift allowed to vary on the clopen rank strata
(Stacks, Tag 0BR0).
The object `OY` is the structure sheaf in the quasi-coherent full subcategory; `hOY`
identifies its underlying derived object. The preservation witness `hpres` defines the
restriction of derived direct image, and `adj` says precisely that `a` is its right adjoint. -/
theorem koszulRegularImmersion_dualizing {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsNoetherian Y] [IsClosedImmersion i]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (hregular : ∀ z : Z, ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (n : ℕ) (f : Fin n → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (r : LocallyConstant Z ℕ)
    (hr : ∀ z : Z, r z = Module.finrank (Z.presheaf.stalk z)
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)))
    (hpres : ∀ E : schemeDerivedCategory Z, schemeDerivedQCohProperty Z E →
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage i).obj E))
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory Z)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage i)
      (fun E => hpres E.obj E.property) ⊣ a)
    (OY : schemeDerivedQCohCategory Y)
    (hOY : OY.obj = (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        (SheafOfModules.unit Y.ringCatSheaf)) :
    ∃ hdet : schemeDerivedQCohProperty Z ((DerivedCategory.Q (C :=
      SheafOfModules.{u} (moduleRings Z.toRingedSpace))).obj
        (Scheme.Modules.locallyRankedExteriorComplex
          (SheafOfModules.homObj (R := Z.sheaf)
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
            (SheafOfModules.unit Z.ringCatSheaf)) r)),
      Nonempty ((⟨(DerivedCategory.Q (C :=
      SheafOfModules.{u} (moduleRings Z.toRingedSpace))).obj
        (Scheme.Modules.locallyRankedExteriorComplex
          (SheafOfModules.homObj (R := Z.sheaf)
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
            (SheafOfModules.unit Z.ringCatSheaf)) r), hdet⟩ :
        schemeDerivedQCohCategory Z) ≅ a.obj OY) := by
  let hdet := koszulRegularImmersion_dualizing_property i hregular r hr
  let D : schemeDerivedQCohCategory Z := ⟨_, hdet⟩
  let R := (schemeDerivedQCohProperty Y).lift
    ((schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage i)
    (fun E => hpres E.obj E.property)
  let comparison : R ⋙ (schemeDerivedQCohProperty Y).ι ≅
      (schemeDerivedQCohProperty Z).ι ⋙ schemeDerivedDirectImage i := Iso.refl _
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
  let : IsNoetherian Z := ⟨⟩
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i)))
  obtain ⟨H, adjH, _, _⟩ := exists_affine_derivedHom_evaluation_counit i
  have hOYge : ∃ n : ℤ, OY.obj.IsGE n := by
    refine ⟨0, ?_⟩
    rw [hOY]
    infer_instance
  obtain ⟨_, _, φ, _, _, _⟩ :=
    finite_duality_derived_hom i R comparison a adj H adjH OY hOYge
  obtain ⟨κ⟩ := koszulRegularImmersion_algebraDual i hregular r hr H adjH
  obtain ⟨E, ⟨eE⟩, _⟩ := finite_affine_derived_equivalence i
  let κ' := κ ≪≫ H.mapIso (eqToIso hOY).symm ≪≫ φ.symm
  let e := eE.app D ≪≫ κ' ≪≫ (eE.app (a.obj OY)).symm
  exact ⟨hdet, ⟨E.fullyFaithfulFunctor.preimageIso
    ((directImageAlgebraDerivedQCohProperty i).fullyFaithfulι.preimageIso e)⟩⟩

end AlgebraicGeometry
