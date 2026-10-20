/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Sheaf.AlgebraicGeometry.Modules.ExteriorSheafPowerComparison
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorQuotient

/-!
# Transport of the official exterior tensor quotient

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
The canonical exterior-power comparison transports the official epimorphism and
its formula to the older exterior sheaves used by the determinant constructions.
-/

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_inv_tensor_wedge {X : Scheme.{v}} (A B : X.Modules)
    (r s : ℕ) (U : X.Opens) (a : Fin r → A.val.obj (op U))
    (b : Fin s → B.val.obj (op U)) :
    (tensorIso (exteriorSheafPowerIso A r) (exteriorSheafPowerIso B s)).inv.app U
        (tmulSection (wedge (M := A) (r := r) a) (wedge (M := B) (r := s) b)) =
      tmulSection (M := exteriorSheaf A r) (N := exteriorSheaf B s)
        (exteriorSheafSection A r U a) (exteriorSheafSection B s U b) := by
  change ((exteriorSheafPowerIso A r).inv ⊗ₘ (exteriorSheafPowerIso B s).inv).app U _ = _
  rw [tensorHom_app_tmulSection, exteriorSheafPowerIso_inv_wedge,
    exteriorSheafPowerIso_inv_wedge]

set_option backward.isDefEq.respectTransparency false in
/-- The official exterior tensor quotient transported to the older exterior sheaves.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
Proof: take the epimorphism furnished by the official exteriorTensor_quotient_exists.
Conjugate it by the tensor comparison isomorphisms for A,B and A,C. Composing an
epimorphism with isomorphisms preserves epimorphy. Precomposing the conjugate with
the inverse source comparison cancels that comparison. Evaluate this equality on
an official tensor of wedges; the inverse comparison preserves each wedge and
tensorHom_app_tmulSection preserves their tensor. The official quotient formula
therefore gives exactly the required formula. This works without rank assumptions,
also in degree zero, on empty opens, on the empty scheme, and over zero rings.
(blueprint: lem-sc-exterior-sheaf-tensor-quotient-comparison). -/
theorem exteriorSheafTensor_quotient_exists {X : Scheme.{v}} (A B C : X.Modules)
    (g : B ⟶ C) [Epi g] (r s : ℕ) :
    ∃ q : exteriorSheaf A r ⊗ exteriorSheaf B s ⟶
        exteriorSheaf A r ⊗ exteriorSheaf C s,
      Epi q ∧ ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
        (c : Fin s → B.val.obj (op U)),
        q.val.app (op U)
            (tmulSection (exteriorSheafSection A r U a) (exteriorSheafSection B s U c)) =
          tmulSection (M := exteriorSheaf A r) (N := exteriorSheaf C s)
            (exteriorSheafSection A r U a)
            (exteriorSheafSection C s U (fun i ↦ g.val.app (op U) (c i))) := by
  obtain ⟨q, hqepi, hq⟩ := exteriorTensor_quotient_exists A B C g r s
  let : Epi q := hqepi
  let eAB := tensorIso (exteriorSheafPowerIso A r) (exteriorSheafPowerIso B s)
  let eAC := tensorIso (exteriorSheafPowerIso A r) (exteriorSheafPowerIso C s)
  let q' := eAB.hom ≫ q ≫ eAC.inv
  refine ⟨q', inferInstance, ?_⟩
  intro U a c
  have hcomp : eAB.inv ≫ q' = q ≫ eAC.inv := by
    simp only [q', Iso.inv_hom_id_assoc]
  have he := congrArg (fun k ↦ k.app U
    (tmulSection (wedge (M := A) (r := r) a) (wedge (M := B) (r := s) c))) hcomp
  change q'.app U (eAB.inv.app U _) = eAC.inv.app U (q.app U _) at he
  rw [comparison_inv_tensor_wedge A B r s U a c] at he
  exact he.trans ((congrArg (eAC.inv.app U) (hq U a c)).trans
    (comparison_inv_tensor_wedge A C r s U a (fun i ↦ g.val.app (op U) (c i))))

end AlgebraicGeometry.Scheme.Modules
