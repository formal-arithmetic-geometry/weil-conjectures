/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.EtaleZariskiQcohComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianZariskiCohomology
import WeilConjectures.AlgebraicGeometry.ZariskiDimensionBound

/-!
# Étale and Zariski cohomology of quasi-coherent modules on curves

The associated étale sheaf of the structure module `Scheme.Modules.unit C` is `Gₐ`.
Étale cohomology uses `Sheaf.H`; Zariski module cohomology uses the recorded right
derived functors `RingedSpace.moduleCohomology`, with their underlying additive groups.
The comparison with the derived-global-sections encoding of étale cohomology is a
comparison theorem.

## References

* Stacks Project, Tags 03DW, 02UZ
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option autoImplicit false

/-- Étale and Zariski cohomology agree for each quasi-coherent module on a curve.
Source: Stacks Project, Descent, Proposition 03DW (2). -/
theorem etale_zariski_cohomology_agree {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (F : C.Modules) [F.IsQuasicoherent] (q : ℕ) :
    Nonempty (Sheaf.H (Scheme.Modules.etaleTensorSectionsSheaf F) q ≃+
      ((RingedSpace.moduleCohomology C.toRingedSpace q).obj F)) := by
  obtain ⟨_, _, c, _, _⟩ := Scheme.Modules.etale_zariski_qcoh_comparison C
  -- Identify the small and large Ext models through one common derived category.
  let : HasDerivedCategory (Sheaf C.smallEtaleTopology AddCommGrpCat.{u}) :=
    HasDerivedCategory.standard _
  let : HasExt.{u + 1} (Sheaf C.smallEtaleTopology AddCommGrpCat.{u}) :=
    HasExt.standard _
  exact ⟨(Abelian.Ext.homAddEquiv.{u + 1, u}.trans
    Abelian.Ext.homAddEquiv.{u + 1, u + 1}.symm).trans (c F q).symm⟩

/-- The comparison specialized to `Gₐ = (𝒪_C)_et`.
Source: Stacks Project, Descent, Proposition 03DW (2), specialized to the structure
sheaf. -/
theorem etale_ga_cohomology_agree {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] (q : ℕ) :
    Nonempty (Sheaf.H (@Scheme.Modules.etaleTensorSectionsSheaf C (Scheme.Modules.unit C)
        (SheafOfModules.isQuasicoherent_unit (R := C.ringCatSheaf))) q ≃+
      ((RingedSpace.moduleCohomology C.toRingedSpace q).obj (Scheme.Modules.unit C))) := by
  have : (Scheme.Modules.unit C).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit (R := C.ringCatSheaf)
  exact etale_zariski_cohomology_agree f (Scheme.Modules.unit C) q

/-- Both cohomology groups of `Gₐ` and `𝒪_C` vanish in degree at least two on a smooth
connected curve. Source: Stacks Project, Descent, Proposition 03DW (2), and Cohomology,
Proposition 02UZ. -/
theorem subsingleton_etale_ga_and_structure_cohomology {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H
      (@Scheme.Modules.etaleTensorSectionsSheaf C (Scheme.Modules.unit C)
        (SheafOfModules.isQuasicoherent_unit (R := C.ringCatSheaf))) q) ∧
    Subsingleton ((RingedSpace.moduleCohomology C.toRingedSpace q).obj
      (Scheme.Modules.unit C)) := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  let F := Scheme.Modules.unit C
  -- Compare module-derived cohomology directly with H' of the underlying abelian sheaf.
  obtain ⟨e⟩ := module_cohomology_iso_underlying_abelian C F q
  have hz := isZero_zariskiCohomology_of_dimension_bound C 1
    (IsCurve.krullDim_le_one (f := f))
    ((SheafOfModules.toSheaf (moduleRings C.toRingedSpace)).obj F) q
    (lt_of_lt_of_le (by decide : 1 < 2) hq)
  have : Subsingleton (Sheaf.H'
      ((SheafOfModules.toSheaf (moduleRings C.toRingedSpace)).obj F) q ⊤) :=
    AddCommGrpCat.subsingleton_of_isZero hz
  have hzar : Subsingleton ((RingedSpace.moduleCohomology C.toRingedSpace q).obj F) :=
    e.addCommGroupIsoToAddEquiv.injective.subsingleton
  obtain ⟨c⟩ := etale_ga_cohomology_agree f q
  exact ⟨c.injective.subsingleton, hzar⟩

end AlgebraicGeometry
