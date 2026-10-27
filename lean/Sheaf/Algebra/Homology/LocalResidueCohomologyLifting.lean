/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S7
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.MinimalComplex
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Lifting zeroth cohomology from a residue complex

Source: Stacks Project, Algebra, Tag 00MT; Cohomology of Schemes, Tag 07VK.
(blueprint: lem-sfb-local-residue-cohomology-lifting).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped ChangeOfRings

namespace CochainComplex

local instance extendScalarsAdditive {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) : (ModuleCat.extendScalars.{u, u, u} φ).Additive :=
  (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive

/-- Scalar extension to the residue field, regarded again as a complex over the local ring.
Source: Stacks, Tag 00MT (blueprint: lem-sfb-local-residue-cohomology-lifting). -/
noncomputable abbrev residueComplex {R : Type u} [CommRing R] [IsLocalRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  ((ModuleCat.restrictScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
    (.up ℤ)).obj
      (((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
        (.up ℤ)).obj C)

/-- The canonical reduction map on cohomology, induced by the extension-restriction unit.
Source: Stacks, Tag 00MT (blueprint: lem-sfb-local-residue-cohomology-lifting). -/
noncomputable def residueCohomologyMap {R : Type u} [CommRing R] [IsLocalRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    C.homology i ⟶ C.residueComplex.homology i :=
  HomologicalComplex.homologyMap
    (((ModuleCat.extendRestrictScalarsAdj
      (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex (.up ℤ)).unit.app C) i

private theorem minimal_residue_d_zero {R : Type u} [CommRing R] [IsLocalRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (hC : C.IsMinimal) (i j : ℤ) :
    C.residueComplex.d i j = 0 := by
  let φ := algebraMap R (IsLocalRing.ResidueField R)
  have he : (ModuleCat.extendScalars φ).map (C.d i j) = 0 := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    rw [ModuleCat.ExtendScalars.map_tmul]
    change (1 : IsLocalRing.ResidueField R) ⊗ₜ[R, φ] (C.d i j).hom x = 0
    refine Submodule.smul_induction_on
      (p := fun y : C.X j ↦
        ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R, φ] y :
          (ModuleCat.extendScalars φ).obj (C.X j)) = 0) (hC i j x) ?_ ?_
    · intro r hr y _
      rw [TensorProduct.tmul_smul]
      change (φ r * 1) ⊗ₜ[R, φ] y = 0
      have hr' : φ r = 0 := by
        change IsLocalRing.residue R r = 0
        exact (RingHom.mem_ker.mp ((IsLocalRing.ker_residue (R := R)).symm ▸ hr))
      rw [hr', zero_mul, TensorProduct.zero_tmul]
    · intro x y hx hy
      rw [TensorProduct.tmul_add, hx, hy, add_zero]
  change (ModuleCat.restrictScalars φ).map ((ModuleCat.extendScalars φ).map (C.d i j)) = 0
  rw [he, Functor.map_zero]

private theorem minimal_term_one_zero {R : Type u} [CommRing R] [IsLocalRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (hC : C.IsMinimal)
    [Module.Finite R (C.X 1)] (hH : Subsingleton (C.residueComplex.homology 1)) :
    IsZero (C.X 1) := by
  let D := C.residueComplex
  have hExact : (D.sc' 0 1 2).Exact :=
    (D.exactAt_iff' 0 1 2 (by simp) (by simp)).mp
      ((D.exactAt_iff_isZero_homology 1).mpr (ModuleCat.isZero_iff_subsingleton.mpr hH))
  have hD : Subsingleton (D.X 1) := by
    apply subsingleton_iff_forall_eq 0 |>.mpr
    intro x
    obtain ⟨y, hy⟩ := ((D.sc' 0 1 2).moduleCat_exact_iff.mp hExact) x (by
      change D.d 1 2 x = 0
      rw [minimal_residue_d_zero C hC]
      rfl)
    change D.d 0 1 y = x at hy
    rw [minimal_residue_d_zero C hC] at hy
    exact hy.symm
  have : Subsingleton ((ModuleCat.extendScalars
      (algebraMap R (IsLocalRing.ResidueField R))).obj (C.X 1)) := hD
  have ht : Subsingleton ((IsLocalRing.ResidueField R) ⊗[R] (C.X 1)) :=
    (ModuleCat.tensorEquivExtendScalars R
      (IsLocalRing.ResidueField R) (C.X 1)).injective.subsingleton
  exact ModuleCat.isZero_iff_subsingleton.mpr
    ((IsLocalRing.subsingleton_tensorProduct (R := R)).mp ht)

private theorem residue_unit_surjective {R : Type u} [CommRing R] [IsLocalRing R]
    (N : ModuleCat.{u} R) : Function.Surjective
      ((ModuleCat.extendRestrictScalarsAdj
        (algebraMap R (IsLocalRing.ResidueField R))).unit.app N) := by
  intro y
  change ∃ x : N, (1 : IsLocalRing.ResidueField R) ⊗ₜ[R,
    algebraMap R (IsLocalRing.ResidueField R)] x = y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r x =>
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective r
    refine ⟨a • x, ?_⟩
    rw [TensorProduct.tmul_smul]
    change ((algebraMap R (IsLocalRing.ResidueField R)) a * 1) ⊗ₜ x = r ⊗ₜ x
    change IsLocalRing.residue R a = r at ha
    rw [IsLocalRing.ResidueField.algebraMap_eq, ha, mul_one]
  | add y z hy hz =>
    obtain ⟨x, hx⟩ := hy
    obtain ⟨w, hw⟩ := hz
    exact ⟨x + w, (TensorProduct.tmul_add _ _ _).trans (congrArg₂ (· + ·) hx hw)⟩

private theorem residue_h0_surjective_of_term_one_zero
    {R : Type u} [CommRing R] [IsLocalRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (hC : IsZero (C.X 1)) :
    Function.Surjective (C.residueCohomologyMap 0) := by
  let η := ((ModuleCat.extendRestrictScalarsAdj
    (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex (.up ℤ)).unit.app C
  have hd : C.d 0 1 = 0 := hC.eq_of_tgt _ _
  have : IsIso (C.iCycles 0) := C.isIso_iCycles 0 1 (by simp) hd
  have : Epi (η.f 0) := (ModuleCat.epi_iff_surjective _).mpr (residue_unit_surjective (C.X 0))
  have : Epi (HomologicalComplex.cyclesMap η 0) := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    intro z
    obtain ⟨x, hx⟩ := residue_unit_surjective (C.X 0) (C.residueComplex.iCycles 0 z)
    change η.f 0 x = C.residueComplex.iCycles 0 z at hx
    let ec := asIso (C.iCycles 0)
    refine ⟨ec.inv x, ?_⟩
    apply (ModuleCat.mono_iff_injective (C.residueComplex.iCycles 0)).mp inferInstance
    have hc := congrArg (fun k ↦ k (ec.inv x)) (HomologicalComplex.cyclesMap_i η 0)
    change C.residueComplex.iCycles 0 (HomologicalComplex.cyclesMap η 0 (ec.inv x)) =
      η.f 0 (ec.hom (ec.inv x)) at hc
    have hc' :
        C.residueComplex.iCycles 0 (HomologicalComplex.cyclesMap η 0 (ec.inv x)) =
          η.f 0 x := by
      simpa only [Iso.inv_hom_id_apply] using hc
    exact hc'.trans hx
  have : Epi (HomologicalComplex.homologyMap η 0) :=
    ShortComplex.epi_homologyMap_of_epi_cyclesMap' _ ‹_›
  exact (ModuleCat.epi_iff_surjective _).mp this

/-- Vanishing of first residue cohomology makes reduction on zeroth cohomology surjective.
Source: Stacks, Algebra, Tag 00MT and Cohomology of Schemes, Tag 07VK.
(blueprint: lem-sfb-local-residue-cohomology-lifting).

Proof: Replace the bounded finite free complex by its minimal homotopy representative.
All residue differentials of the representative vanish. Its first residue cohomology
is its first residue term, so Nakayama makes its first term zero. Every vector in degree
zero is therefore a cycle. The residue quotient is surjective on vectors, hence on
cycles and then on cohomology. Naturality of the scalar-extension unit transports this
surjectivity back along the homotopy equivalence. No reducedness, or vanishing in other
degrees, is used. Empty complexes are included. -/
theorem surjective_residueCohomologyMap_zero {R : Type u} [CommRing R] [IsLocalRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    [∀ i : ℤ, Module.Free R (C.X i)] [∀ i : ℤ, Module.Finite R (C.X i)]
    (hH : Subsingleton (C.residueComplex.homology 1)) :
    Function.Surjective (C.residueCohomologyMap 0) := by
  let φ := algebraMap R (IsLocalRing.ResidueField R)
  let E := ModuleCat.extendScalars φ
  let G := ModuleCat.restrictScalars φ
  have : (ModuleCat.extendScalars φ).Additive :=
    (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive
  obtain ⟨D, hm, _, _, hf, hfin, ⟨e⟩⟩ := exists_homotopyEquiv_isMinimal C a b
  have (i : ℤ) := hfin i
  let er := G.mapHomotopyEquiv (E.mapHomotopyEquiv e)
  let := hH
  have hHD : Subsingleton (D.residueComplex.homology 1) :=
    (er.toHomologyIso 1).symm.toLinearEquiv.injective.subsingleton
  have hs := residue_h0_surjective_of_term_one_zero D (minimal_term_one_zero D hm hHD)
  intro x
  obtain ⟨y, hy⟩ := hs ((er.toHomologyIso 0).hom x)
  refine ⟨(e.toHomologyIso 0).inv y, ?_⟩
  apply (ModuleCat.mono_iff_injective (er.toHomologyIso 0).hom).mp inferInstance
  have hn := ((ModuleCat.extendRestrictScalarsAdj φ).mapHomologicalComplex (.up ℤ)).unit.naturality
     e.hom
  have hc := congrArg (fun k ↦ HomologicalComplex.homologyMap k 0) hn
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hc
  have hv := congrArg (fun k ↦ k ((e.toHomologyIso 0).inv y)) hc
  change D.residueCohomologyMap 0
      ((e.toHomologyIso 0).hom ((e.toHomologyIso 0).inv y)) =
    (er.toHomologyIso 0).hom (C.residueCohomologyMap 0 ((e.toHomologyIso 0).inv y)) at hv
  simpa only [Iso.inv_hom_id_apply, hy] using hv.symm

end CochainComplex
