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

/-- Identity law for restricted single transitions.
Source: Stacks Project, Tags 09Z1 and 03CB, inverse-image coherence in restriction.
(blueprint: lem-sbc-restricted-affine-single-identity-law).

Proof: Expand the transition as the single comparison followed by the image of the
restricted coefficient. The pullback second-projection equation gives its commuting
square. Use D.map_id to replace both horizontal arrows by identities, and hφid to
replace the original coefficient with upperStarId. The identity square comparison
is the composite of the two unit comparisons, whiskered along the second projection.
Its inverse cancels the pulled-back coefficient unit, leaving the unit on the
restricted sheaf, transported along restrictedAffineDiagram.map_id. Apply
HomologicalComplex.hom_ext. At degree zero use singleObjXSelf and naturality of the
unit comparison to identify the single-complex map with this sheaf equality. At all
other degrees the target single complex is zero, so its morphisms agree. The
calculation also applies to zero sheaves and empty schemes; for an empty index type
there is no identity equation to check. -/
theorem restrictedAffineSingleTransition_identity_law {S : Scheme.{v}}
    {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (U : S.Etale) :
    let D' := restrictedAffineDiagram D U
    let K := restrictedAffineK D F U
    let ψ := fun {i j : Iᵒᵖ} (f : j ⟶ i) ↦ restrictedAffineSingleTransition D F φ U f
    ( ∀ i : Iᵒᵖ, ψ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{v + 1}) (D'.map_id i)))
        (ComplexShape.up ℤ)).hom.app (K i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{v + 1} (D'.obj i))
        (ComplexShape.up ℤ)).hom.app (K i)) := by sorry

end AlgebraicGeometry.Etale
