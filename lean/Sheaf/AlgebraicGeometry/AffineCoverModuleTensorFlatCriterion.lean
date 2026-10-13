/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.TensorPullback
import Mathlib.RingTheory.Flat.Localization
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections

/-! # Tensor flatness on a specified affine cover

Source: Stacks Project, Morphisms, Tag 01U4; Algebra, Tag 00HT;
Limits, Tag 05LY, affine-local reduction.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry

/-- Flatness after an affine base change is equivalent to tensor flatness of the actual
section modules on a specified affine covering. No finiteness or descent is asserted.
Source: Stacks Project, Morphisms, Tag 01U4; Algebra, Tag 00HT; Limits, Tag 05LY.
(blueprint: lem-pc-affine-cover-module-tensor-flat-criterion).

Proof: Each inverse image of U_b in the fibre product is affine: identify U_b with
Spec of its section ring and use the spectrum tensor-product pullback formula. The
quasi-coherent pullback has sections T tensor_A Gamma(M,U_b), compatibly with the
map to Spec T. The multiplication map T tensor_A A -> T and t -> t tensor 1 are
inverse ring maps. Their induced module isomorphism identifies the tensor module
in the statement with those sections, respecting the base action. The isomorphism
e identifies the arbitrary affine base Y with Spec T over Spec A, so the same
comparisons apply to the chosen pullback along p. Flatness over Y implies flatness
of these sections by the affine-section criterion (01U4). Conversely, tensor
flatness gives flatness of each chart's sections over T, hence flatness of every
module stalk over the corresponding base local ring, by localization. The inverse
images of the U_b cover the fibre product, so all its relative stalks are flat.
Quasi-coherence and the prime-local flatness criterion (00HT) then imply flatness
of sections on any affine source open over any affine base open, which is exactly
IsFlatOver. An empty covering forces X empty; all pulled-back sections are zero.
The zero ring and zero modules satisfy the same tensor and localization formulas. -/
theorem affine_cover_module_tensor_flat_criterion
    (A T : CommRingCat.{u}) {X Y : Scheme.{u}} (f : X ⟶ Spec A)
    (M : X.Modules) [M.IsQuasicoherent]
    {n : ℕ} (U : Fin n → X.affineOpens) (hcover : ∀ x : X, ∃ b, x ∈ (U b).1)
    (q : A ⟶ T) (p : Y ⟶ Spec A) (e : Y ≅ Spec T)
    (he : e.hom ≫ Spec.map q = p) :
    let a := fun b ↦ ((Scheme.ΓSpecIso A).inv ≫
      f.appLE ⊤ (U b).1 (by simp)).hom
    Scheme.Modules.IsFlatOver
      ((Scheme.Modules.tensorPullback (pullback.fst f p)).obj M) (pullback.snd f p) ↔
    (∀ b, letI : Module (A : Type u) Γ(M, (U b).1) := Module.compHom _ (a b)
      letI : Algebra (A : Type u) (T : Type u) := q.hom.toAlgebra
      letI : Algebra (A : Type u) ((T : Type u) ⊗[(A : Type u)] (A : Type u)) :=
        Algebra.TensorProduct.rightAlgebra
      letI : Module (A : Type u) ((T : Type u) ⊗[(A : Type u)] (A : Type u)) :=
        Algebra.toModule
      Module.Flat ((T : Type u) ⊗[(A : Type u)] (A : Type u))
        (((T : Type u) ⊗[(A : Type u)] (A : Type u)) ⊗[(A : Type u)] Γ(M, (U b).1))) := by sorry

end AlgebraicGeometry
