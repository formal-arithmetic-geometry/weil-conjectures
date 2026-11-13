/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleMaps
import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleIdentityLaw
import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleCompositionLaw

/-! # Explicit maps for restricted degree-zero complexes

## References

* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
* [Stacks Project, Tag 0EZM](https://stacks.math.columbia.edu/tag/0EZM)
* [Stacks Project, Tag 03CB](https://stacks.math.columbia.edu/tag/03CB)
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The explicit restricted transitions satisfy the unit and composition laws. -/
theorem restrictedAffineSingleTransition_laws {S : Scheme.{v}}
    {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (U : S.Etale) :
    let D' := restrictedAffineDiagram D U
    let K := restrictedAffineK D F U
    let ψ := fun {i j : Iᵒᵖ} (f : j ⟶ i) ↦ restrictedAffineSingleTransition D F φ U f
    ( ∀ i : Iᵒᵖ, ψ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{v + 1}) (D'.map_id i)))
        (ComplexShape.up ℤ)).hom.app (K i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{v + 1} (D'.obj i))
        (ComplexShape.up ℤ)).hom.app (K i))
    ∧ ( ∀ (i j k : Iᵒᵖ) (f : j ⟶ i) (g : k ⟶ j),
      ψ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (D'.map g) (D'.map f)
            (D'.map (g ≫ f)) (D'.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (D'.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ ψ g) := by
  exact ⟨restrictedAffineSingleTransition_identity_law D F φ hφid U,
    restrictedAffineSingleTransition_composition_law D F φ hφcomp U⟩

end AlgebraicGeometry.Etale
