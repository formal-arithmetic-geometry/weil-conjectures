/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # EtaleModuleRingIsoTensor

Source: Stacks Project, Tags 03D3, 03D6, 03D7.
(blueprint: lem-weil-pbc-etale-module-ring-iso-tensor). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Identify extension along a ring isomorphism using a restriction comparison.
Source: Stacks Project, Definition 03D6 and Lemma 03D7; the tensor-restriction
adjunction in Tag 03CZ, specialized to an isomorphism.

Proof: at W send a pure tensor a tensor m to t.inv(G)(c.inv(a) times m).
The scalar-linearity of t.inv and the inverse-ring identities prove that this map
is RU(W)-linear and balanced over Lr(RV)(W). The tensor universal property extends
it to all tensors. Its inverse sends n to 1 tensor t.hom(G)(n). The composite on
n is n by the inverse comparison equation and the unit action. The composite on
a tensor m is itself: use c.hom(c.inv(a)) = a and the balancing relation to move
c.inv(a) from m onto the first factor. Pure tensors generate the tensor product.
Naturality of c and t proves compatibility with restriction maps. Consequently
the section maps give inverse presheaf morphisms to the underlying presheaf of
LM(G). Sheafification, whose unit is invertible on that sheaf, produces d(G) and
preserves the pure-tensor formula. For a module map G to H, the two composites
agree on pure tensors by naturality of t and linearity of L0.map; sheafification
then proves the displayed naturality of d.
(blueprint: lem-weil-pbc-etale-module-ring-iso-tensor). -/
theorem etaleModuleRingIsoTensor (U V : Scheme.{u}) (f : U ⟶ V)
    (RV : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
    (RU : Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
    (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤ Sheaf U.smallEtaleTopology
      CommRingCat.{u + 1})
    (c : Lr.obj RV ≅ RU)
    (L0 : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
      1} RingCat.{u + 1})).obj RV) ⥤ SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj RV)))
    (LM : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
        1} RingCat.{u + 1})).obj RV) ⥤ SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU))
    (t : LM ⋙ SheafOfModules.pushforward (F := 𝟭 U.Etale) ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).hom ≅ L0) :
    (∃ (d : ∀ G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂
      CommRingCat.{u + 1} RingCat.{u + 1})).obj RV),
        SheafOfModules.changeOfRings.{u, u + 1, u + 1} (J := U.smallEtaleTopology) c.hom (L0.obj
          G) ≅ LM.obj G),
      (∀ (G H : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u
        + 1} RingCat.{u + 1})).obj RV)) (h : G ⟶ H),
        SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} (J := U.smallEtaleTopology) c.hom
          (L0.obj G) (L0.map h) ≫ (d H).hom =
          (d G).hom ≫ LM.map h) ∧
      (∀ (G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
        1} RingCat.{u + 1})).obj RV)) (W : U.Etaleᵒᵖ)
        (a : RU.obj.obj W) (m : (L0.obj G).val.obj W),
        (d G).hom.val.app W
          ((toSheafify U.smallEtaleTopology
            (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (J := U.smallEtaleTopology)
              c.hom (L0.obj G)).presheaf).app W
              (a ⊗ₜ[(Lr.obj RV).obj.obj W, (c.hom.hom.app W).hom] m)) =
          (t.inv.app G).val.app W ((c.inv.hom.app W a) • m))) := by sorry

end AlgebraicGeometry
