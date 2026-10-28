/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralFiniteScalarModelDefinitions

/-! The scalar mate identity for the normalized finite-free beta.
(blueprint: new-sfb-finite-free-scalar-derived-comparison-beta-mate)
-/

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
paragraphs. This is the mate step after the normalized construction and its
pullback square have been supplied.
(blueprint: new-sfb-finite-free-scalar-derived-comparison-beta-mate)

Proof: transport the normalized section adjunctions through coefficient change.
The ring-sheaf change-adjunction identity rewrites the restricted scalar mate.
Substituting the pullback square and using beta naturality at the geometric
counit yields exactly the scalar-first projection arrow.
-/
theorem finiteFreeScalarDerivedComparison_beta_mate
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    (β : ∀ Z : Scheme.{u}, tensorLeft (DerivedCategory.Q.obj (complex Λ S Z)) ≅
      scalarSixChange a Z ⋙ restriction a Z)
    (hβ : ∀ Z, AugmentationNormalized a S t Z (β Z))
    (hpull : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
        (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)),
      (scalarSixPull Λ f).map ((β Y).hom.app K) ≫
        (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app
          ((scalarSixChange a Y).obj K) ≫
        (restriction a X).map ((D.theta a f).inv.app K) =
      tensorPull Λ f (DerivedCategory.Q.obj (complex Λ S Y)) K ≫
        ((modelPull Λ S f).hom ⊗ₘ 𝟙 ((scalarSixPull Λ f).obj K)) ≫
        (β X).hom.app ((scalarSixPull Λ f).obj K)) :
    ∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)),
      (β Y).hom.app ((moduleObjectDerivedPushforward Λ.X f).obj K) ≫
        (restriction a Y).map (gamma D a f K) ≫
        (restrictionPush D a f).hom.app ((scalarSixChange a X).obj K) ≫
        (moduleObjectDerivedPushforward Λ.X f).map ((β X).inv.app K) =
      projection Λ f (DerivedCategory.Q.obj (complex Λ S Y))
        (DerivedCategory.Q.obj (complex Λ S X)) (modelPull Λ S f) K := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
