/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Topology.PresheafModuleStalkFunctor
import Sheaf.LinearAlgebra.TensorProduct.ColimitVaryingRings

/-! # Stalks of sectionwise extension of scalars

Source: Stacks Project, Sheaves, Lemma 007K (blueprint:
lem-weil-pbc-presheaf-stalk-change-of-rings-tensor).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite TopCat.Presheaf
open scoped ChangeOfRings

namespace SheafOfModules

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The stalk comparison before sheafification, with its germ formula.
Source: Stacks Project, Sheaves, Lemma 007K (lemma-stalk-tensor-presheaf-modules).
(blueprint: lem-weil-pbc-presheaf-stalk-change-of-rings-tensor).

Proof: Restrict the ring and module presheaves to the directed system of neighborhoods
of x, ordered by reverse inclusion. Apply the varying-ring tensor-colimit theorem to
R₂(U) and F(U) over R₁(U), using α for the action on R₂(U). Naturality of α and
semilinearity of module restrictions give the transition hypotheses. The stalk action
on germs gives the three colimit action hypotheses. Tensor commutation identifies the
coefficient-first convention used here with the usual tensor order. Invert the colimit
comparison. To see R₂,x-linearity, represent a scalar and both tensor factors on a common
neighborhood; scalar multiplication is multiplication on the coefficient factor there.
The germ formula follows from the comparison equation on colimit coprojections. This
formula uniquely determines each isomorphism because pure tensors generate and pairs
of germs have representatives on a common neighborhood. -/
theorem stalkChangeOfRingsPresheafIso (X : TopCat.{u})
    (R₁ R₂ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (α : R₁ ⟶ R₂) (x : X) :
    ∃ Φ : ∀ F : SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁),
      (ModuleCat.extendScalars ((TopCat.Presheaf.stalkFunctor CommRingCat x).map α.hom).hom).obj
        (ModuleCat.of (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) R₁.obj x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) F.val.presheaf x)) ≅
      ModuleCat.of (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) R₂.obj x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) (changeOfRingsPresheaf α F).presheaf x),
      (∀ (F : SheafOfModules.{u}
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁))
        (U : Opens X) (hx : x ∈ U) (s : F.val.obj (op U)) (a : R₂.obj.obj (op U)),
        (Φ F).hom
          (TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := X) R₂.obj U x hx a
          ⊗ₜ[TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) R₁.obj x,
            ((TopCat.Presheaf.stalkFunctor CommRingCat x).map α.hom).hom]
            TopCat.Presheaf.germ (C := Ab.{u}) (X := X) F.val.presheaf U x hx s) =
          TopCat.Presheaf.germ (C := Ab.{u}) (X := X) (changeOfRingsPresheaf α F).presheaf U x hx
            (a ⊗ₜ[R₁.obj.obj (op U), (α.hom.app (op U)).hom] s)) := by sorry

end SheafOfModules
