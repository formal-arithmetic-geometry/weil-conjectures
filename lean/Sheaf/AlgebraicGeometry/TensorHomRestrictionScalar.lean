/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import all WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison

/-! # Restricting a tensor-Hom transpose with prescribed scalar values

Source: Stacks Project, Modules, Tag 01CN and Tag 01YB, tensor-Hom paragraph.
(blueprint: lem-pc-tensor-hom-restriction-scalar)
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option maxHeartbeats 600000 in
-- Normalizing the slice and scheme restriction comparisons requires extra elaboration fuel.
set_option backward.isDefEq.respectTransparency false in
/-- Transposition sends a local scalar multiple of a Hom section to multiplication
followed by the local morphism. No coherence or ideal-power hypothesis is required.
Source: Stacks Project, Modules, Tag 01CN, and Tag 01YB, tensor-Hom paragraph.
(blueprint: lem-pc-tensor-hom-restriction-scalar)

Proof: For W contained in U, the assumed equality says that alpha_W(a) is
ι_W(a) times the restriction of the local morphism s. Evaluating at g gives
ι_W(a) times s_W(g). The tensor-Hom characterization therefore says beta on
local pure tensors is this same value. Multiplication is the map ι tensor id
followed by the left unitor; its value on a tensor g is ι_W(a) times g.
Linearity of s gives equality of these two local tensor maps. Pure tensors
generate the presheaf tensor product. The universal property of sheafification
then gives equality of the restricted sheaf maps. Finally, naturality of
Scheme.Modules.overFunctorEquiv transports the slice morphism represented by
s to the displayed restrictFunctor morphism. This also applies to the empty
open and zero modules; no generation by global sections of U is assumed. -/
theorem tensorHom_restriction_of_local_scalar
    {X : Scheme.{u}} (A H F : X.Modules)
    (ι : A ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens)
    (s : (SheafOfModules.homObj (R := X.sheaf) H F).val.obj (op U))
    (α : A ⟶ SheafOfModules.homObj (R := X.sheaf) H F)
    (hα : ∀ (W : X.Opens) (h : W ≤ U) (a : A.val.obj (op W)),
      α.val.app (op W) a = ι.val.app (op W) a •
        (SheafOfModules.homObj (R := X.sheaf) H F).val.map (homOfLE h).op s) :
    letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    ∀ (β : A ⊗ H ⟶ F),
      (∀ (W : X.Opens) (a : A.val.obj (op W)) (g : H.val.obj (op W)),
        β.val.app (op W)
          ((SheafOfModules.tensorObjIsoSheafification A H).inv.val.app (op W)
            (((PresheafOfModules.sheafificationAdjunction.{u}
              (𝟙 X.ringCatSheaf.obj)).unit.app (A.val ⊗ H.val)).app (op W)
                (a ⊗ₜ[X.sheaf.obj.obj (op W)] g))) =
          (α.val.app (op W) a).app (op (Over.mk (𝟙 W))) g) →
      (restrictFunctor U.ι).map β =
        (restrictFunctor U.ι).map (ι ▷ H ≫ (λ_ H).hom) ≫
          (overFunctorEquiv U).inv.app H ≫
          (overEquiv U).functor.map (⟨s⟩ : H.over U ⟶ F.over U) ≫
          (overFunctorEquiv U).hom.app F := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  intro β hβ
  obtain ⟨e, he⟩ := exists_restriction_tensor_comparison U.ι A H
  -- Test the two restricted maps on pure tensors after the comparison.
  apply (cancel_epi e.inv).mp
  apply tensor_hom_ext
  intro V a g
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  have ht := he V a g
  change e.inv.app V (tmulSection a g) =
    tmulSection (M := A) (N := H) a g at ht
  rw [ht]
  change β.val.app (op (U.ι ''ᵁ V))
    ((SheafOfModules.tensorObjIsoSheafification A H).inv.val.app _
      ((toSheafifyTensor A H).app _ (a ⊗ₜ[X.sheaf.obj.obj _] g))) = _
  rw [hβ]
  rw [hα (U.ι ''ᵁ V) (U.ι_image_le V) a]
  -- The slice comparison components act identically on these sections.
  change _ = s.app (op (Over.mk (homOfLE (U.ι_image_le V))))
    ((ι ▷ H ≫ (λ_ H).hom).app (U.ι ''ᵁ V) (tmulSection a g))
  rw [Hom.comp_app, ConcreteCategory.comp_apply, whiskerRight_app_tmulSection]
  erw [leftUnitor_hom_app_tmulSection']
  change _ = s.app (op (Over.mk (homOfLE (U.ι_image_le V))))
    ((show Γ(X, U.ι ''ᵁ V) from ι.val.app (op (U.ι ''ᵁ V)) a) •
      (show Γ(H, U.ι ''ᵁ V) from g))
  erw [(s.app (op (Over.mk (homOfLE (U.ι_image_le V))))).hom.map_smul]
  -- The internal-Hom scalar action restricts the scalar along the identity.
  change X.sheaf.obj.map (𝟙 (op (U.ι ''ᵁ V)))
      (show Γ(X, U.ι ''ᵁ V) from ι.val.app (op (U.ι ''ᵁ V)) a) •
      s.app (op (Over.mk (𝟙 (U.ι ''ᵁ V) ≫ homOfLE (U.ι_image_le V)))) g = _
  exact congrArg (fun r : Γ(X, U.ι ''ᵁ V) ↦
    r • (s.app (op (Over.mk (homOfLE (U.ι_image_le V))))).hom g)
    (ConcreteCategory.congr_hom (X.sheaf.obj.map_id (op (U.ι ''ᵁ V))) _)

end AlgebraicGeometry.Scheme.Modules
