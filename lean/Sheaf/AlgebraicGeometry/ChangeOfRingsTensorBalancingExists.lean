/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-! # Universal property of the change-of-rings balancing map

Source: Stacks Project, Morphisms, proof of Lemma 01SB; Sheaves, Lemma 0089.
(blueprint: lem-weil-pbc-change-of-rings-tensor-balancing-universal).
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a

/-- Existence clause for the balancing factorization.
Source: Stacks Project, Morphisms, proof of Lemma 01SB.
(blueprint: aux-lem-weil-pbc-change-of-rings-tensor-balancing-universal-exists)
The sectionwise balanced map factors through the change-of-rings sheafification by
the tensor universal property and sheafification universal property. -/
theorem changeOfRings_tensor_balancing_universal_exists (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right)) :
    let P₀ := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P
    let S := tensorObj C.toModule P₀
    let T := (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
      (SheafOfModules.changeOfRings.{u, u, u} φ.right P)
    ∀ (a d : tensorObj B.toModule S ⟶ S) (g : S ⟶ T),
      (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
          (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        a.app W (tmulSection (M := B.toModule)
          b (tmulSection (M := C.toModule) (N := P₀) c p)) =
          tmulSection (M := C.toModule) (N := P₀) c (b • p)) →
      (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
          (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        d.app W (tmulSection (M := B.toModule)
          b (tmulSection (M := C.toModule) (N := P₀) c p)) =
          tmulSection (M := C.toModule) (N := P₀)
            (φ.right.hom.app (op W) b * c) p) →
      (∀ (W : Y.Opens) (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        g.app W (tmulSection (M := C.toModule) (N := P₀) c p) =
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (𝓡 C.right).obj)).unit.app
            (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P)).app
              (op W))
              (c ⊗ₜ[B.right.obj.obj (op W), (φ.right.hom.app (op W)).hom] p)) →
      ∀ (Q : Y.Modules) (f : S ⟶ Q), a ≫ f = d ≫ f → ∃ t : T ⟶ Q, g ≫ t = f := by
  sorry


end AlgebraicGeometry.Scheme.Modules
