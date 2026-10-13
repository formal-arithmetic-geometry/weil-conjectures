/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.IsomorphicSingleTensorCounitTransport
/-! # Counit equation for canonical transport
Source: Stacks Project, Tags 08HY, 0096 and 0D5S.
(blueprint: lem-pc-isomorphic-single-tensor-counit-equation). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry
/-- The canonical transported isomorphism satisfies the counit equation.
Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: lem-pc-isomorphic-single-tensor-counit-equation).
Proof: transpose the composition-pinned counit through the adjunction of the
isomorphism. Use the inverse-component formula in the transport theorem:
it is the unit at (p^*M)[0] followed by direct image of the single tensor
counit for e and the underived tensor composition comparison. Naturality
of this unit moves the counit for p across it. The defining left-derived
composition factorization then identifies the direct-image term with
c(e,p) followed by the counit for e p. Thus the first two factors in the
displayed equation equal the counit for p followed by t.inv.app M.
Compose with t.hom.app M and cancel by the inverse identity. This argument
uses the pinned comparisons and includes zero modules and empty schemes;
it would not apply to an arbitrary natural isomorphism. -/
theorem isomorphic_single_tensor_counit_transport_equation
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
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
    let t := Classical.choose (exists_isomorphic_single_tensor_counit_transport p e)
    ∀ M : X.Modules,
      let K := (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
      (a e.hom).unit.app ((derivedPullback p).obj K) ≫
          (schemeDerivedDirectImage e.hom).map
            ((c e.hom p).hom.app K ≫ pinnedSingleTensorCounit (e.hom ≫ p) 0 M) ≫
          t.hom.app M = pinnedSingleTensorCounit p 0 M := by sorry
end AlgebraicGeometry
