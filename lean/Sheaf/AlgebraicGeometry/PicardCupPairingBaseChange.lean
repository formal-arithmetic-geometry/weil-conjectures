/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.PicardCanonicalBaseChange

/-! # Compatibility of the cup pairing with arbitrary base change
Source: Stacks Project, Tag 0BDP, final two paragraphs.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme

/-- The degree-zero cup pairing commutes with the canonical direct-image maps.
This statement does not assume the direct-image maps are invertible and does not
assert any dual-pullback comparison is invertible.

Source: Stacks Project, Tag 0BDP, compatibility with arbitrary change of base
and the evaluation formula for the cup product in the final two paragraphs.
(blueprint: lem-sc-picard-cup-pairing-base-change)

Proof: Expand picardCupProductMap and uncurry its defining transpose, obtaining
the pushed-forward evaluation pairing. Apply the tensor comparison for h. Take
the adjoint along p_T of the two proposed pairings. Expand each canonical
base-change map as the mate of the top pullback unit. Naturality of the units
and counits, together with the two triangle identities, replaces the two
base-change maps followed by the p_T counits with the pullbacks of the p_W
counits. Tensor-composition comparisons transport their evaluations to X_T.
Both adjoints are then the pullback of E tensor dual E to X_T, followed by the
pulled evaluation and the inverse structure-sheaf unit. The structure units
commute with base change because their section formula is m mapped to 1 tensor m.
The tensor comparisons commute by naturality and tensor associativity. Thus the
adjoints agree; injectivity of the adjunction Hom equivalence proves the formula.
This calculation uses neither local freeness nor any flatness of h. Zero pairings
and empty bases satisfy the same identities. -/
theorem picardCupPairing_baseChange
    {X S W T : Scheme.{u}} (f : X ⟶ S) (E : X.Modules)
    (j : W ⟶ S) (h : T ⟶ W)
    (hO : IsIso ((Classical.choose
      (Modules.exists_tensorPullbackAdjunction (pullback.snd f j))).unit.app
        (SheafOfModules.unit W.ringCatSheaf)))
    (hOT : IsIso ((Classical.choose
      (Modules.exists_tensorPullbackAdjunction (pullback.snd f (h ≫ j)))).unit.app
        (SheafOfModules.unit T.ringCatSheaf))) :
    ((Modules.picardDirectImageBaseChangeMap f j h E) ⊗ₘ
        (Modules.picardDirectImageBaseChangeMap f j h (Modules.dual E))) ≫
      MonoidalClosed.uncurry (picardCupProductMap f E (h ≫ j) hOT) =
    (Modules.picardTensorObjIso h
      ((Modules.pushforward (pullback.snd f j)).obj
        ((Modules.tensorPullback (pullback.fst f j)).obj E))
      ((Modules.pushforward (pullback.snd f j)).obj
        ((Modules.tensorPullback (pullback.fst f j)).obj (Modules.dual E)))).inv ≫
      (Modules.tensorPullback h).map (MonoidalClosed.uncurry (picardCupProductMap f E j hO)) ≫
        (Modules.picardTensorUnitIso h).hom := by sorry

end AlgebraicGeometry.Scheme
