/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.PinnedSingleTensorShifts
import WeilConjectures.AlgebraicGeometry.IsomorphicSingleTensorCounitEquation
/-! # Pinned single tensor counits under an isomorphism

## References

* Stacks Project, Tags 08HY, 0096 and 0D5S.
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry
/-- The single tensor counit factors through pullback along a scheme isomorphism.
(Stacks, Tags 08HY, 0096, 0D5S) -/
theorem exists_isomorphic_single_tensor_counit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X P Z : Scheme.{u}} (p : P ⟶ X) (e : Z ≅ P) :
    let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    let a := fun {A B : Scheme.{u}} (s : A ⟶ B) ↦
      Classical.choose (exists_schemeDerivedAdjunction s
        (hAdd := (Classical.choose exists_derivedPullbackComposition) s)
        ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) s)
        ((Classical.choose (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))) s))
    ∃ t : (Scheme.Modules.tensorPullback (e.hom ≫ p) ⋙
          DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0) ⋙
          schemeDerivedDirectImage e.hom ≅
        Scheme.Modules.tensorPullback p ⋙ DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings P.toRingedSpace)) 0,
      ∀ M : X.Modules,
        let K := (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
        (a e.hom).unit.app ((derivedPullback p).obj K) ≫
            (schemeDerivedDirectImage e.hom).map
              ((c e.hom p).hom.app K ≫ pinnedSingleTensorCounit (e.hom ≫ p) 0 M) ≫
            t.hom.app M = pinnedSingleTensorCounit p 0 M := by
  refine ⟨Classical.choose (exists_isomorphic_single_tensor_counit_transport p e), ?_⟩
  intro M
  exact isomorphic_single_tensor_counit_transport_equation p e M
end AlgebraicGeometry
