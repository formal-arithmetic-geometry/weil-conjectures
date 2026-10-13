/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Sheaf.AlgebraicGeometry.RestrictedAffineSingleMaps

/-! # Explicit maps for restricted degree-zero complexes

Source: Stacks Project, Tags 09Z1 and 0EZM.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Composition law for restricted single transitions.
Source: Stacks Project, Tags 09Z1 and 03CB, inverse-image coherence in restriction.
(blueprint: lem-sbc-restricted-affine-single-composition-law).

Proof: Expand all three transitions. Their pullback second-projection equations give
two adjacent commuting squares and their outer rectangle. Substitute D.map_comp
and hφcomp into the outer restricted coefficient. Horizontal pasting for
squareUpperStarIso expresses the outer inverse comparison as upperStarComp for
the restricted arrows followed by the pulled-back first inverse square comparison
and the second inverse square comparison. Use naturality of the second comparison
to move the first coefficient map past it. Cancel each comparison with its inverse;
the result is the coefficient composition law on the restricted sheaves, with the
transport along restrictedAffineDiagram.map_comp. Apply HomologicalComplex.hom_ext.
In degree zero, the evaluation isomorphisms singleObjXSelf and their naturality
identify the single-complex comparison maps with this sheaf calculation; cancel
the intervening evaluation isomorphisms. In every other degree the target single
complex is zero. No directedness, cone, nonemptiness, affineness or nonzero sheaf
assumption is used, so the empty and zero cases satisfy the same equation. -/
theorem restrictedAffineSingleTransition_composition_law {S : Scheme.{v}}
    {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (U : S.Etale) :
    let D' := restrictedAffineDiagram D U
    let K := restrictedAffineK D F U
    let ψ := fun {i j : Iᵒᵖ} (f : j ⟶ i) ↦ restrictedAffineSingleTransition D F φ U f
    ( ∀ (i j k : Iᵒᵖ) (f : j ⟶ i) (g : k ⟶ j),
      ψ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (D'.map g) (D'.map f)
            (D'.map (g ≫ f)) (D'.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (D'.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ ψ g) := by sorry

end AlgebraicGeometry.Etale
