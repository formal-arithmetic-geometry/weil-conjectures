/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.DirectSum.Module
public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.AffineModuleCorrespondence
import WeilConjectures.AlgebraicGeometry.AffineModuleFiniteType
import WeilConjectures.AlgebraicGeometry.GradedModuleQuasicoherentRealization
import WeilConjectures.AlgebraicGeometry.GradedModuleRealizationFiniteType
/-! # The algebra-module part of graded affine realization

## References

* [Stacks Project, Tags 0897, 01SB, 01PB]
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry

/-- The homogeneous action and local generators give a finite-type quasi-coherent
module over the direct image algebra, before applying the affine correspondence.
(Stacks, Tag 0897) -/
theorem exists_finiteType_graded_algebra_module
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (graded : ℕ → Submodule A B)
    (hgrading : DirectSum.IsInternal graded)
    (hunit : (1 : B) ∈ graded 0)
    (hmul : ∀ (k l : ℕ) {x y : B}, x ∈ graded k → y ∈ graded l → x * y ∈ graded (k + l))
    (hscalar : ∀ (a : A), algebraMap A B a ∈ graded 0)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (G : ℕ → X.Modules)
    (hG : ∀ m : ℕ, (G m).IsQuasicoherent)
    (mu : ∀ (m k : ℕ), graded k → (G m ⟶ G (m + k)))
    (hmu_add : ∀ (m k : ℕ) (b b' : graded k),
      mu m k (b + b') = mu m k b + mu m k b')
    (hmu_mul : ∀ (m k l : ℕ) (b : graded k) (b' : graded l),
      HEq (mu m l b' ≫ mu (m + l) k b)
        (mu m (k + l) ⟨b.val * b'.val, hmul k l b.property b'.property⟩))
    (hmu_scalar : ∀ (m : ℕ) (a : A) (U : X.Opens)
      (t : (G m).val.obj (op U)),
      HEq ((mu m 0 ⟨algebraMap A B a, hscalar a⟩).val.app (op U) t)
        ((X.presheaf.map (homOfLE (le_top (a := U))).op).hom
          (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a) • t))
    (hfinite : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      ∃ (r : ℕ) (d : Fin r → ℕ) (s : ∀ i : Fin r, (G (d i)).val.obj (op U)),
        ∀ (m : ℕ) (V : X.Opens) (hVU : V ≤ U) (t : (G m).val.obj (op V))
          (y : X), y ∈ V → ∃ (W : X.Opens) (hWV : W ≤ V), y ∈ W ∧
            (G m).val.map (homOfLE hWV).op t ∈
              Submodule.span ((moduleRings X.toRingedSpace).obj.obj (op W))
                {z | ∃ (i : Fin r), d i ≤ m ∧
                  ∃ b : graded (m - d i),
                    HEq z ((mu (d i) (m - d i) b).val.app (op W)
                      ((G (d i)).val.map (homOfLE (hWV.trans hVU)).op (s i)))}) :
    let b : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let Y := pullback f b
    let pi := pullback.fst f b
    let C := (TopCat.Sheaf.pushforward CommRingCat.{u} pi.base).obj Y.sheaf
    let CR := (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj C
    let rho : X.sheaf ⟶ C := ⟨pi.c⟩
    let S := SheafOfModules.restrictScalars.{u}
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map rho)
    ∃ N : SheafOfModules.{u} CR, N.IsQuasicoherent ∧ N.IsFiniteType ∧
      Nonempty (S.obj N ≅ ∐ G) := by
  classical
  dsimp only
  let b := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let pi := pullback.fst f b
  let C := (TopCat.Sheaf.pushforward CommRingCat.{u} pi.base).obj (pullback f b).sheaf
  let CR := (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj C
  let R := SheafOfModules.pushforward.{u} (F := TopologicalSpace.Opens.map pi.base)
    (S := CR) (R := (pullback f b).ringCatSheaf) (𝟙 CR)
  have : IsAffineHom b := inferInstance
  have : IsAffineHom pi := MorphismProperty.pullback_fst _ _ ‹IsAffineHom b›
  obtain ⟨F, hF, iota, hcoprod, hcompat⟩ := gradedModule_quasicoherent_realization
    graded hgrading hunit hmul hscalar f G hG mu hmu_add hmu_mul hmu_scalar
  have hFfinite := gradedModule_realization_isFiniteType graded f G mu hfinite
    F hF iota hcoprod hcompat
  have hN := (Scheme.Modules.affine_module_correspondence pi).2.1 F hF
  have hNfinite := (Scheme.Modules.affine_module_finite_type pi (R.obj F) hN F hF
    (Iso.refl _)).mpr hFfinite
  obtain ⟨hc⟩ := hcoprod
  refine ⟨R.obj F, hN, hNfinite, ⟨?_⟩⟩
  exact hc.coconePointUniqueUpToIso (coproductIsCoproduct G)

end AlgebraicGeometry
