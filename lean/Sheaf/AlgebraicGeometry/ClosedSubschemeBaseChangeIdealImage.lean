/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# The ideal sheaf of a base-changed closed subscheme

Source: Stacks Project, Schemes, Lemma 26.17.6, Tag 01JU (1)
(blueprint: lem-pc-closed-subscheme-base-change-ideal-image).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

/-- The projection of the base change of a closed immersion is a closed immersion,
and its kernel ideal is the image of the pulled-back ideal inclusion followed by the
adjoint of the structure-sheaf map. The adjunction is the one supplied by the tensor
pullback dependency; its choice does not affect the image subobject.
Source: Stacks Project, Schemes, Tag 01JU (1)
(blueprint: lem-pc-closed-subscheme-base-change-ideal-image).
Proof: apply `lem-pc-closed-imm-base-change` to `i : Z ⟶ S` and `g : Y ⟶ S`.
Its projection and ideal-image assertions are precisely these two conclusions.
Equivalently, Tag 01JU constructs the closed subscheme defined by this image ideal,
identifies it with the fibre product of locally ringed spaces, and observes it is a scheme. -/
theorem closedSubscheme_baseChange_ideal_image {S Z Y : Scheme.{u}}
    (i : Z ⟶ S) [IsClosedImmersion i] (g : Y ⟶ S) :
    IsClosedImmersion (pullback.snd i g) ∧
      Subobject.mk (pullback.snd i g).ker.toModulesι =
        imageSubobject
          ((Scheme.Modules.tensorPullback g).map i.ker.toModulesι ≫
            ((Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction g)).homEquiv
              (SheafOfModules.unit S.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf)).symm
                (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)) := by
  sorry

end
end AlgebraicGeometry
