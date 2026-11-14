/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ShiftedKoszulAugmentation
import WeilConjectures.AlgebraicGeometry.KoszulOpenConeComparison
import WeilConjectures.AlgebraicGeometry.KoszulRestrictionZeroBase

@[expose] public section

universe a b
open CategoryTheory
namespace AlgebraicGeometry

set_option maxHeartbeats 500000 in
-- Elaborating the cone comparison unfolds both presentations of the Koszul tail.
/-- The canonical shifted Koszul augmentation is invertible on the principal-open union
(Stacks, Tags 08CX, 0626 and 0663). -/
theorem affine_perfect_koszul_principal_unit_iso
    (A : Type a) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) (he : 1 ≤ e)
    [HasDerivedCategory.{b}
      (SheafOfModules.{a} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ U : (Spec (.of A)).Opens,
      HasDerivedCategory.{b}
        (SheafOfModules.{a} ((moduleRings (Spec (.of A)).toRingedSpace).over U))] :
    IsIso (((SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace)
        (⨆ i : Fin r, (Spec (.of A)).basicOpen
          ((Scheme.ΓSpecIso (.of A)).inv (f i)))).mapDerivedCategory).map
            (affineKoszulAugmentation A r (fun i ↦ f i ^ e))) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
  let U : (Spec (.of A)).Opens := ⨆ i : Fin r, (Spec (.of A)).basicOpen
    ((Scheme.ΓSpecIso (.of A)).inv (f i))
  let R := (SheafOfModules.overFunctor
    (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory
  let F := @Functor.mapHomologicalComplex ℤ (ModuleCat.{a} A)
    (SheafOfModules.{a} (moduleRings (Spec (.of A)).toRingedSpace))
    _ _ _ _ (tilde.functor (.of A)) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)
  let u := shiftedKoszulAugmentation A r (fun i ↦ f i ^ (d + 1))
  obtain ⟨c₀, _⟩ := koszulOpen_module_cone_comparison A r f d
  have hu : HomologicalComplex.extendMap (koszulOpenAugmentation A r f d)
      ComplexShape.embeddingDownNat = u := by
    rfl
  rw [hu] at c₀
  have : (tilde.functor (.of A)).Additive :=
    ⟨fun {X Y} g h ↦ tilde.map_add (R := .of A) g h⟩
  let c := (CochainComplex.mappingCone.mapHomologicalComplexIso
    u (tilde.functor (.of A))).symm ≪≫ F.mapIso c₀
  have hU : U = ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i ^ (d + 1)) := by
    dsimp only [U]
    apply iSup_congr
    intro i
    rw [PrimeSpectrum.basicOpen_pow _ _ (by omega)]
    exact basicOpen_eq_of_affine (R := .of A) (f i)
  have hz := isZero_restrict_koszul_base A r (fun i ↦ f i ^ (d + 1)) U hU
  let T := R.mapTriangle.obj
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (F.map u)))
  have hT := R.map_distinguished _
    (DerivedCategory.mappingCone_triangle_distinguished (F.map u))
  have hcone : Limits.IsZero T.obj₃ := hz.of_iso (R.mapIso (DerivedCategory.Q.mapIso c))
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ T hT).1 hcone

end AlgebraicGeometry
