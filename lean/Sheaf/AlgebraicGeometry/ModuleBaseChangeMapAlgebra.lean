/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
public import Sheaf.AlgebraicGeometry.ModulePullbackTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.AlgebraicGeometry.TensorPullback

/-!
# Algebra compatibility of the structure-sheaf base change map

Source: Stacks Project, Cohomology, Remark 08HY; Sheaves, Tags 0093, 0095, 0096;
Modules, Tag 01CD. The algebra compatibility is the agent-written argument in the node,
not a separately stated Stacks lemma
(blueprint: lem-weil-pbc-module-base-change-map-algebra).
-/

@[expose] public section

universe v

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false

/-- The canonical base change map on structure sheaves has adjoint `f_*(g'^sharp)`
and preserves multiplication and units. The multiplications are characterized on pure
section tensors, so they are the actual ring multiplications, not arbitrary algebra data.

Source: Stacks Project, Cohomology, Remark 08HY; Sheaves, Tags 0093, 0095, 0096;
Modules, Tag 01CD; algebra compatibility is agent-written
(blueprint: lem-weil-pbc-module-base-change-map-algebra).
Proof:
(1) Use the Hom bijection of def-pc-module-pullback and its natural unit. Identify
`f_* g'_*` with `g_* f'_*` through the pushforward composition and square comparisons;
0093 identifies the module actions.
(2) By lem-weil-pbc-module-pullback-structure-sheaf, the adjoint of epsilon is sharp.
Functoriality and the defining adjoint of beta therefore give the displayed adjoint of gamma;
on sections this is exactly gamma(eta(a)) = g'^sharp(a).
(3) Multiplication on the pushforward is induced by sectionwise ring multiplication,
using def-pur-sheaf-tensor-product and def-weil-presheaf-modules-sheafification.
Compare the adjoints of the two multiplication composites. Uniqueness of sheafification
reduces equality to pure tensors. Naturality of eta gives g'^sharp(ab) on the first side;
lem-weil-pbc-module-pullback-tensor gives g'^sharp(a) g'^sharp(b) on the second.
These agree because g'^sharp is a ring homomorphism (def-pc-scheme).
(4) Compare adjoints of the unit composites. Naturality and step (2) give
(f composed with g')^sharp; the epsilon characterization gives (g composed with f')^sharp.
They agree by the square and 0093. Thus gamma is an O_S'-algebra morphism. -/
theorem moduleBaseChangeMap_algebra
    {X S X' S' : Scheme.{v}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) :
    ∃ (mu : (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) ⊗
          (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
        (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
      (mu' : (pushforward f').obj (SheafOfModules.unit X'.ringCatSheaf) ⊗
          (pushforward f').obj (SheafOfModules.unit X'.ringCatSheaf) ⟶
        (pushforward f').obj (SheafOfModules.unit X'.ringCatSheaf)),
      (∀ (W : S.Opens) (a b : Γ(X, f ⁻¹ᵁ W)), mu.app W (tmulSection a b) = a * b) ∧
      (∀ (W : S'.Opens) (a b : Γ(X', f' ⁻¹ᵁ W)), mu'.app W (tmulSection a b) = a * b) ∧
      (Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
          ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) ≫
          (pushforward g).map
            (moduleBaseChangeMap f f' g g' h (SheafOfModules.unit X.ringCatSheaf) ≫
          (pushforward f').map (tensorPullbackObjUnitToUnit g')) =
        (pushforward f).map (SheafOfModules.unitToPushforwardObjUnit g'.toRingCatSheafHom) ≫
          (pushforwardComp g' f).hom.app (SheafOfModules.unit X'.ringCatSheaf) ≫
          (pushforwardCongr h).hom.app (SheafOfModules.unit X'.ringCatSheaf) ≫
          (pushforwardComp f' g).inv.app (SheafOfModules.unit X'.ringCatSheaf) ∧
      (tensorPullback g).map mu ≫
          (moduleBaseChangeMap f f' g g' h (SheafOfModules.unit X.ringCatSheaf) ≫
          (pushforward f').map (tensorPullbackObjUnitToUnit g')) =
        (Classical.choose (module_pullback_tensor g)
            ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
            ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))).hom ≫
          ((moduleBaseChangeMap f f' g g' h (SheafOfModules.unit X.ringCatSheaf) ≫
          (pushforward f').map (tensorPullbackObjUnitToUnit g')) ⊗ₘ
            (moduleBaseChangeMap f f' g g' h (SheafOfModules.unit X.ringCatSheaf) ≫
          (pushforward f').map (tensorPullbackObjUnitToUnit g'))) ≫ mu' ∧
      (tensorPullback g).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          (moduleBaseChangeMap f f' g g' h (SheafOfModules.unit X.ringCatSheaf) ≫
          (pushforward f').map (tensorPullbackObjUnitToUnit g')) =
        tensorPullbackObjUnitToUnit g ≫
          SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
