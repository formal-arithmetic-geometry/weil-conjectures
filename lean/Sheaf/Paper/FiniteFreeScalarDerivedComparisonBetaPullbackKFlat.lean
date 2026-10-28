module

public import Sheaf.Paper.IntegralFiniteScalarModelDefinitions

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing

/--
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/det-prop-scalar-six-direct-image.proof.md, formal-properties
paragraphs. For a K-flat representative, transport the representative comparison
through exact point pullback. The normalized augmentation equation identifies the
scalar-first map with the tensor pullback comparison; the K-flat counits are
isomorphisms, so cancellation gives the displayed equation.
(blueprint: new-sfb-finite-free-scalar-derived-comparison-beta-pullback-kflat)
-/
theorem finiteFreeScalarDerivedComparison_beta_pullback_kflat
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    (β : ∀ Z : Scheme.{u}, tensorLeft (DerivedCategory.Q.obj (complex Λ S Z)) ≅
      scalarSixChange a Z ⋙ restriction a Z)
    (hβ : ∀ Z, AugmentationNormalized a S t Z (β Z))
    (X Y : Scheme.{u}) (f : X ⟶ Y)
    (C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Y) ℤ)
    (hC : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C) :
    (scalarSixPull Λ f).map ((β Y).hom.app (DerivedCategory.Q.obj C)) ≫
        (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app
          ((scalarSixChange a Y).obj (DerivedCategory.Q.obj C)) ≫
        (restriction a X).map ((D.theta a f).inv.app (DerivedCategory.Q.obj C)) =
      tensorPull Λ f (DerivedCategory.Q.obj (complex Λ S Y)) (DerivedCategory.Q.obj C) ≫
        ((modelPull Λ S f).hom ⊗ₘ 𝟙 ((scalarSixPull Λ f).obj (DerivedCategory.Q.obj C))) ≫
        (β X).hom.app ((scalarSixPull Λ f).obj (DerivedCategory.Q.obj C)) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
