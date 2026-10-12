/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.Normalization
public import WeilConjectures.RingTheory.Etale.IntegralClosureSpreading

/-!
# Étaleness of the normalization over the generic point

In the situation of the spreading theorem (blueprint `sbc-thm-spreading-finite-etale-galois`)
over a Noetherian base, the relative normalization of `C` in the Galois cover is étale in a
neighbourhood of every point lying over the generic point of `S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.SpreadingDatum

variable {G : Type (u + 1)} [Group G] [Finite G] (D : SpreadingDatum G)

set_option backward.isDefEq.respectTransparency false in
/-- Step of the proof of blueprint `sbc-thm-spreading-finite-etale-galois`: over a Noetherian
base, the normalization `N ⟶ C` of `C` in `Z.P` is étale in a neighbourhood of every point lying
over the generic point `η` of `S`.

Proof: work over affine opens `Spec A ⊆ S`, `Spec B ⊆ c⁻¹(Spec A)`, so that the preimage of
`Spec B` in `Z.P` is `Spec L` with `L` finite étale over `B_K = B ⊗_A K`, `K = Frac A`. By
`Algebra.exists_etale_integralClosure_of_isLocalization` there is `a ≠ 0` in `A` such that the
integral closure of `B_a` in `L` is étale over `B_a`; it is the ring of sections of the
normalization over `D(a) ⊆ Spec B`
(`AlgebraicGeometry.Scheme.Hom.etale_fromNormalization_of_isAffineOpen`), since `a` is already
invertible on `Spec L`, and `D(a)` contains every point over `η`. -/
theorem etaleOver_genericPoint [IsNoetherian D.S] : D.EtaleOver (genericPoint D.S) := by
  intro x hx
  obtain ⟨W, hW, U, hU, hUW, hxU, hne⟩ := D.exists_affineOpens (D.ν.fromNormalization x)
  let := (D.c.appLE W U hUW).hom.toAlgebra
  let := (D.j.appLE U (D.j ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  let := (D.Z.π.app (D.j ⁻¹ᵁ U)).hom.toAlgebra
  let := (D.j.app U ≫ D.Z.π.app (D.j ⁻¹ᵁ U)).hom.toAlgebra
  have : IsScalarTower Γ(D.C, U) Γ(D.Cη, D.j ⁻¹ᵁ U) Γ(D.Z.P, D.Z.π ⁻¹ᵁ D.j ⁻¹ᵁ U) :=
    .of_algebraMap_eq' (by
      simp only [RingHom.algebraMap_toAlgebra, ← Scheme.Hom.app_eq_appLE]
      rfl)
  have : IsIntegrallyClosed Γ(D.S, W) :=
    isIntegrallyClosed_of_isIntegrallyClosed_stalk D.isIntegrallyClosed_stalk W
  have : Algebra.Smooth Γ(D.S, W) Γ(D.C, U) :=
    HasRingHomProperty.appLE @Smooth D.c inferInstance ⟨W, hW⟩ ⟨U, hU⟩ hUW
  have : IsLocallyNoetherian D.C := LocallyOfFiniteType.isLocallyNoetherian D.c
  have : IsNoetherianRing Γ(D.C, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have := D.isLocalization_appLE_j hW hU hUW
  have hjU : IsAffineOpen (D.j ⁻¹ᵁ U) := D.isAffineOpen_preimage_j hW hU hUW
  have : Module.Finite Γ(D.Cη, D.j ⁻¹ᵁ U) Γ(D.Z.P, D.Z.π ⁻¹ᵁ D.j ⁻¹ᵁ U) :=
    IsFinite.finite_app D.Z.π _ hjU
  have : Algebra.Etale Γ(D.Cη, D.j ⁻¹ᵁ U) Γ(D.Z.P, D.Z.π ⁻¹ᵁ D.j ⁻¹ᵁ U) := by
    have := HasRingHomProperty.appLE @Etale D.Z.π inferInstance ⟨_, hjU⟩
      ⟨_, hjU.preimage D.Z.π⟩ le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at this
  obtain ⟨a, ha, H⟩ := Algebra.exists_etale_integralClosure_of_isLocalization
    (R := Γ(D.S, W)) (B := Γ(D.C, U)) (Bk := Γ(D.Cη, D.j ⁻¹ᵁ U))
    (L := Γ(D.Z.P, D.Z.π ⁻¹ᵁ D.j ⁻¹ᵁ U))
  let b : Γ(D.C, U) := algebraMap Γ(D.S, W) Γ(D.C, U) a
  have hUb : IsAffineOpen (D.C.basicOpen b) := hU.basicOpen b
  let := (D.C.presheaf.map (homOfLE (D.C.basicOpen_le b)).op).hom.toAlgebra
  have : IsLocalization.Away b Γ(D.C, D.C.basicOpen b) := hU.isLocalization_basicOpen b
  let := (D.ν.app (D.C.basicOpen b)).hom.toAlgebra
  let : Algebra Γ(D.C, U) Γ(D.Z.P, D.ν ⁻¹ᵁ D.C.basicOpen b) :=
    ((algebraMap Γ(D.C, D.C.basicOpen b) Γ(D.Z.P, D.ν ⁻¹ᵁ D.C.basicOpen b)).comp
      (algebraMap Γ(D.C, U) Γ(D.C, D.C.basicOpen b))).toAlgebra
  have : IsScalarTower Γ(D.C, U) Γ(D.C, D.C.basicOpen b) Γ(D.Z.P, D.ν ⁻¹ᵁ D.C.basicOpen b) :=
    .of_algebraMap_eq' rfl
  have hunit : IsUnit (algebraMap Γ(D.C, U) Γ(D.Z.P, D.Z.π ⁻¹ᵁ D.j ⁻¹ᵁ U) b) := by
    rw [IsScalarTower.algebraMap_apply Γ(D.C, U) Γ(D.Cη, D.j ⁻¹ᵁ U)]
    exact (IsLocalization.map_units Γ(D.Cη, D.j ⁻¹ᵁ U)
      (⟨b, Algebra.mem_algebraMapSubmonoid_of_mem (⟨a, ha⟩ : nonZeroDivisors Γ(D.S, W))⟩ :
        Algebra.algebraMapSubmonoid Γ(D.C, U) (nonZeroDivisors Γ(D.S, W)))).map _
  have hEq : D.ν ⁻¹ᵁ D.C.basicOpen b = D.Z.π ⁻¹ᵁ D.j ⁻¹ᵁ U := by
    have hunit' : IsUnit (D.ν.app U b) := hunit
    rw [Scheme.preimage_basicOpen, Scheme.basicOpen_of_isUnit _ hunit', Scheme.Hom.comp_preimage]
  let e : Γ(D.Z.P, D.Z.π ⁻¹ᵁ D.j ⁻¹ᵁ U) ≃ₐ[Γ(D.C, U)] Γ(D.Z.P, D.ν ⁻¹ᵁ D.C.basicOpen b) :=
    { (D.Z.P.presheaf.mapIso (eqToIso hEq).op).commRingCatIsoToRingEquiv with
      commutes' r := by
        change (D.Z.P.presheaf.map (eqToHom hEq).op) ((D.j.app U ≫ D.Z.π.app _) r) =
          D.ν.app _ (D.C.presheaf.map (homOfLE (D.C.basicOpen_le b)).op r)
        rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality,
          ← Scheme.Hom.comp_app]
        rfl }
  have := H Γ(D.C, D.C.basicOpen b) Γ(D.Z.P, D.ν ⁻¹ᵁ D.C.basicOpen b) e
  refine ⟨_, ?_, Scheme.Hom.etale_fromNormalization_of_isAffineOpen D.ν hUb this⟩
  have hb : D.C.basicOpen b = U ⊓ D.c ⁻¹ᵁ D.S.basicOpen a := by
    simp only [b, RingHom.algebraMap_toAlgebra, Scheme.Hom.appLE]
    rw [CommRingCat.comp_apply, Scheme.basicOpen_res, Scheme.preimage_basicOpen]
  change D.ν.fromNormalization x ∈ D.C.basicOpen b
  rw [hb]
  refine ⟨hxU, ?_⟩
  change D.c (D.ν.fromNormalization x) ∈ D.S.basicOpen a
  rw [hx]
  have hηW : genericPoint D.S ∈ W := genericPoint_mem_of_nonempty W
  rw [D.S.mem_basicOpen a _ hηW]
  exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (D.S.germToFunctionField_injective W)).mpr
    (nonZeroDivisors.ne_zero ha))

end AlgebraicGeometry.Scheme.SpreadingDatum
