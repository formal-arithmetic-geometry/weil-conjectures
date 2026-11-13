/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.PerfectAffineMapRepresentative

/-! # A strictly perfect model for a cone on an affine open

## References

* Stacks Project, Tag 08CR (second proof, mapping cone construction).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme

private theorem strictlyPerfect_mappingCone (X : Scheme.{u}) (U : X.Opens)
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hA : IsStrictlyPerfect X U A) (hB : IsStrictlyPerfect X U B) (α : A ⟶ B) :
    IsStrictlyPerfect X U (CochainComplex.mappingCone α) := by
  classical
  obtain ⟨⟨a₁, b₁, hb₁⟩, hp₁⟩ := hA
  obtain ⟨⟨a₂, b₂, hb₂⟩, hp₂⟩ := hB
  constructor
  · refine ⟨min (a₁ - 1) a₂, max (b₁ - 1) b₂, fun i hi ↦ ?_⟩
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨hb₁ (i + 1) (by omega), hb₂ i (by omega)⟩
  · intro i
    obtain ⟨m, j₁, r₁, hj₁⟩ := hp₁ (i + 1)
    obtain ⟨n, j₂, r₂, hj₂⟩ := hp₂ i
    let R := (moduleRings X.toRingedSpace).over U
    have : HasBinaryBiproducts (SheafOfModules.{u} R) := inferInstance
    have : HasBinaryBiproduct (A.X (i + 1)) (B.X i) := inferInstance
    have e₁ := HomologicalComplex.homotopyCofiber.XIsoBiprod α i (i + 1) rfl
    have e₂ : (SheafOfModules.free (R := R) (ULift.{u} (Fin m))) ⊞
        (SheafOfModules.free (R := R) (ULift.{u} (Fin n))) ≅
        SheafOfModules.free (R := R)
          (ULift.{u} (Fin (Fintype.card (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin n))))) :=
      biprod.isoCoprod _ _ ≪≫ SheafOfModules.freeSumIso _ _ ≪≫
        (SheafOfModules.freeFunctor (R := R)).mapIso
          ((Fintype.equivFin (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin n))).trans
            Equiv.ulift.symm).toIso
    refine ⟨_, e₁.hom ≫ biprod.map j₁ j₂ ≫ e₂.hom,
      e₂.inv ≫ biprod.map r₁ r₂ ≫ e₁.inv, ?_⟩
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have hbip : biprod.map j₁ j₂ ≫ biprod.map r₁ r₂ = 𝟙 _ := by
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.map_fst, ← Category.assoc, biprod.map_fst,
          Category.assoc, hj₁, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, biprod.map_snd, ← Category.assoc, biprod.map_snd,
          Category.assoc, hj₂, Category.comp_id, Category.id_comp]
    rw [← Category.assoc (biprod.map j₁ j₂), hbip]
    simp only [Category.id_comp, Iso.hom_inv_id]

/-- On an affine open, strictly perfect models of the first two objects of a distinguished
triangle give a strictly perfect model of its third object (Stacks, Tag 08CR). -/
theorem perfect_affine_cone_model (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (U : X.Opens) (hU : IsAffineOpen U)
    (T : Triangle (schemeDerivedCategory X)) (hT : T ∈ distTriang (schemeDerivedCategory X))
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hA : IsStrictlyPerfect X U A) (hB : IsStrictlyPerfect X U B)
    (eA : Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj T.obj₁ ≅ DerivedCategory.Q.obj A))
    (eB : Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj T.obj₂ ≅
        DerivedCategory.Q.obj B)) :
    ∃ K : CochainComplex
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
      IsStrictlyPerfect X U K ∧
      Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj T.obj₃ ≅
        DerivedCategory.Q.obj K) := by
  obtain ⟨eA⟩ := eA
  obtain ⟨eB⟩ := eB
  let F := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
  let S := F.mapTriangle.obj T
  have hS : S ∈ distTriang _ := F.map_distinguished T hT
  obtain ⟨α, hα⟩ := perfect_affine_map_representative X U hU A B
    hA hB (eA.inv ≫ F.map T.mor₁ ≫ eB.hom)
  have hcomm : DerivedCategory.Q.map α ≫ eB.inv = eA.inv ≫ F.map T.mor₁ := by
    rw [hα]
    simp
  obtain ⟨e, _, _⟩ := exists_iso_of_arrow_iso
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle α)) S
    (DerivedCategory.mappingCone_triangle_distinguished α) hS
    (Arrow.isoMk eA.symm eB.symm hcomm.symm)
  exact ⟨CochainComplex.mappingCone α, strictlyPerfect_mappingCone X U A B hA hB α,
    ⟨(Triangle.π₃.mapIso e).symm⟩⟩

end AlgebraicGeometry.Scheme
