/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.PinnedSingleTensorShifts
/-! # Canonical transport under an isomorphic source
Source: Stacks Project, Tags 08HY, 0096 and 0D5S.
(blueprint: lem-pc-isomorphic-single-tensor-counit-transport). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry
/-- The canonical transport isomorphism for an isomorphic source.
Source: Stacks Project, Tags 08HY, 0096 and 0D5S.
(blueprint: lem-pc-isomorphic-single-tensor-counit-transport).
Proof: tensor pullback along the isomorphism is an equivalence, and its
selected derived adjunction transports the single-complex functor. More precisely,
the inverse components are the derived adjunction unit on (p^*M)[0], followed
by direct image of the pinned single tensor comparison for e and the single
complex image of the canonical underived composition comparison b. Each
factor is natural. Since e is an isomorphism, tensor pullback is an exact
equivalence, so its derived unit and single comparison are invertible;
b is invertible as well. These component maps therefore form a natural
isomorphism whose inverse is t. The displayed inverse components determine
t uniquely. This also works for zero modules and empty schemes. -/
theorem exists_isomorphic_single_tensor_counit_transport
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X P Z : Scheme.{u}} (p : P ⟶ X) (e : Z ≅ P) :
    let a := Classical.choose (exists_schemeDerivedAdjunction e.hom
      (hAdd := (Classical.choose exists_derivedPullbackComposition) e.hom)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) e.hom)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) e.hom))
    let b := (conjugateIsoEquiv
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (e.hom ≫ p)))
      ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p)).comp
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction e.hom)))).symm
          (Scheme.Modules.pushforwardComp e.hom p).symm
    ∃ t : (Scheme.Modules.tensorPullback (e.hom ≫ p) ⋙
      DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0) ⋙
      schemeDerivedDirectImage e.hom ≅
      Scheme.Modules.tensorPullback p ⋙ DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings P.toRingedSpace)) 0,
      ∀ M : X.Modules,
        t.inv.app M =
          a.unit.app ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings P.toRingedSpace)) 0).obj
              ((Scheme.Modules.tensorPullback p).obj M)) ≫
          (schemeDerivedDirectImage e.hom).map
            (pinnedSingleTensorCounit e.hom 0 ((Scheme.Modules.tensorPullback p).obj M) ≫
              (DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).map (b.hom.app M))
      := by sorry
end AlgebraicGeometry
