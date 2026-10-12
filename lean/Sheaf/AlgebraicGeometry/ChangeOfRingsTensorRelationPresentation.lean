/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! # Change of rings as a tensor relation cokernel

Source: Stacks Project, Morphisms, proof of Lemma 01SB; Sheaves, Lemma 0089.
(blueprint: lem-weil-pbc-change-of-rings-tensor-relation-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a

/-- The tensor relation presentation, without any quasi-coherence hypotheses.
Source: Stacks Project, Morphisms, proof of Lemma 01SB (change of rings), and
Sheaves, Lemma 0089 (sheafification universal property).
(blueprint: lem-weil-pbc-change-of-rings-tensor-relation-presentation).

Proof: on the tensor presheaf C tensor_O P, define the two B-actions by acting
on P and by multiplication through φ on C. They commute with restrictions and
extend uniquely to its sheafification S. Their difference induces δ from B tensor_O S.
The balanced tensor map from C tensor_O P to C tensor_B P kills δ and gives a map
from coker δ to change of rings. Conversely, the cokernel projection composed with
the tensor sheafification unit kills all B-balancing relations, hence factors through
C tensor_B P and then through its sheafification. Both composites are identities:
on S this follows from the sheafification universal property and cancellation of the
cokernel projection; on change of rings use surjectivity of the presheaf balancing
map followed by uniqueness of sheafification. These maps give e. Evaluating the
constructions on pure tensors gives the displayed relation and comparison formulas.
-/
theorem changeOfRings_tensor_relation_presentation (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right)) :
    let P₀ := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P
    let S := tensorObj C.toModule P₀
    ∃ (δ : tensorObj B.toModule S ⟶ S)
      (e : (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
        (SheafOfModules.changeOfRings.{u, u, u} φ.right P) ≅ cokernel δ),
      (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
          (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        δ.app W (tmulSection (M := B.toModule) b
          (tmulSection (M := C.toModule) (N := P₀) c p)) =
          tmulSection (M := C.toModule) (N := P₀) c (b • p) -
            tmulSection (M := C.toModule) (N := P₀) (φ.right.hom.app (op W) b * c) p) ∧
      (∀ (W : Y.Opens) (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        e.hom.val.app (op W)
          ((((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C.right).obj)).unit.app
            (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P)).app (op W))
              (c ⊗ₜ[B.right.obj.obj (op W), (φ.right.hom.app (op W)).hom] p)) =
          (cokernel.π δ).app W (tmulSection (M := C.toModule) (N := P₀) c p)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
