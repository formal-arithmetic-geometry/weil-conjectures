/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.AlgebraicGeometry.Curve.ArtinSchreierDimension
import WeilConjectures.AlgebraicGeometry.Curve.EtaleSheafHLargeFilteredColimit
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalEtaleCohomologyRest
import WeilConjectures.AlgebraicGeometry.Curve.ConstantModCharPFiniteSumColimit
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Category.Grp.Zero

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

variable (Λ : Type (u + 1)) [CommRing Λ]
variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))

/-- Degree-two vanishing for the constant sheaf with arbitrary coefficients `Λ/pΛ`. -/
theorem subsingleton_sheafH_constantModSheaf_of_charP_two [IsCurve f] [Smooth f]
    [ConnectedSpace C] (p : ℕ) [Fact p.Prime] [CharP k p] :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C p)) 2) := by
  classical
  have hbase : CategoryTheory.Limits.IsZero
      ((Sheaf.functorH.{u + 1} C.smallEtaleTopology 2).obj (C.constantZMod p)) := by
    obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso C 2
    apply CategoryTheory.Limits.IsZero.of_iso _ (e.app (C.constantZMod p))
    by_cases hdim : topologicalKrullDim C = 1
    · let : IsConnectedCurve f :=
        { connectedSpace := inferInstance
          krullDim_eq_one := hdim }
      exact isZero_etaleCohomology_constantZMod_of_one_lt_of_charP f p 2 (by decide)
    · have hzero : topologicalKrullDim C ≤ 0 := by
        have hlt : topologicalKrullDim C < 1 :=
          lt_of_le_of_ne (IsCurve.krullDim_le_one (f := f)) hdim
        exact Order.le_of_lt_succ hlt
      have h := (zero_dimensional_etale_cohomology_rest k C f hzero (C.constantZMod p)
        (fun x ↦ AlgebraicClosure (C.residueField x)) C.algClosurePoint
        (fun x ↦ C.algClosurePoint_base x default)).1 2 (by decide)
      exact AddCommGrpCat.isZero_iff_subsingleton.mpr h
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨I, hI, hfiltered, D, ι, hc, hfinite⟩ :=
    Etale.exists_constantModSheaf_finite_sum_colimit Λ C p
  let := hI
  let := hfiltered
  let H := Sheaf.functorH.{u + 1} C.smallEtaleTopology 2
  have hD : CategoryTheory.Limits.IsZero (D ⋙ H) := by
    apply Functor.isZero
    intro i
    obtain ⟨n, ⟨e⟩⟩ := hfinite i
    apply CategoryTheory.Limits.IsZero.of_iso _
      (H.mapIso e ≪≫ H.mapBiproduct (fun _ : Fin n ↦ C.constantZMod p))
    rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
    apply CategoryTheory.Limits.biproduct.hom_ext
    intro j
    exact hbase.eq_of_tgt _ _
  obtain ⟨hH⟩ := Scheme.sheafH_isColimit_large_filtered C hc.some 2
  exact AddCommGrpCat.subsingleton_of_isZero (hH.isZero_pt hD)

end AlgebraicGeometry.IsCurve
