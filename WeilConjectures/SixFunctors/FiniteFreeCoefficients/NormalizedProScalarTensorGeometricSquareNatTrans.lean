/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData

/-! # Naturality of the pro-scalar tensor geometric square -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

private def uncurryPostcompose
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] {F : Type u₄} [Category.{v₄} F]
    (T : C ⥤ D ⥤ E) (G : E ⥤ F) :
    Functor.uncurry.obj ((Functor.postcompose₂.obj G).obj T) ≅
      Functor.uncurry.obj T ⋙ G :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    dsimp
    simp only [Category.comp_id, Category.id_comp, G.map_comp])

/-- The two displayed routes form natural transformations of bifunctors.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, final paragraph:
scheme-isomorphism naturality, specifically the localization descent subargument.
Use naturality of the scalar/pullback comparison, the tensor comparison, and the
derived upper-star tensor isomorphism.
Proof: take the product of the scalar/pullback comparison with itself and whisker by
tensor, then compose with the pullback of the inverse tensor comparison and the scalar
image of the inverse geometric tensor comparison. For the other route, whisker the
inverse geometric comparison by the scalar product, then compose with the pullback of
the inverse tensor comparison and the tensor-precomposition of scalar/pullback.
Their components are the displayed composites by the definitions of whiskering.
(blueprint: new-sf-normalized-pro-scalar-tensor-geometric-square-nat-trans). -/
theorem normalized_pro_scalar_tensor_geometric_square_natTrans
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : Sites.TensorComparison true φ X)
    (Y : Scheme.{u}) (e : Y ≅ X) (δ : Sites.TensorComparison true φ Y) :
    ∃ (lhs rhs :
        ((Sites.scalar true φ X).prod (Sites.scalar true φ X) ⋙
          (Sites.proPull B e.hom).prod (Sites.proPull B e.hom) ⋙
          Functor.uncurry.obj (Sites.tensor true B Y)) ⟶
        (Functor.uncurry.obj (Sites.tensor true A X) ⋙
          Sites.proPull A e.hom ⋙ Sites.scalar true φ Y)),
        (∀ K L : Sites.D true A X,
          lhs.app (K, L) =
            ((Sites.proScalarPull φ e.hom).hom.app K ⊗ₘ
              (Sites.proScalarPull φ e.hom).hom.app L) ≫
            δ.inv.app ((Sites.proPull A e.hom).obj K,
              (Sites.proPull A e.hom).obj L) ≫
            (Sites.scalar true φ Y).map
              (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A)
                e.hom K L).inv) ∧
        (∀ K L : Sites.D true A X,
          rhs.app (K, L) =
            (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} B)
              e.hom ((Sites.scalar true φ X).obj K)
              ((Sites.scalar true φ X).obj L)).inv ≫
            (Sites.proPull B e.hom).map (μ.inv.app (K, L)) ≫
            (Sites.proScalarPull φ e.hom).hom.app (K ⊗ L)) := by
  classical
  unfold Sites.TensorComparison at μ δ
  let c := (Sites.proScalarPull φ e.hom).hom
  let a := Functor.uncurry.map
    (ProEtale.leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) e.hom).inv ≫
    (uncurryPostcompose (Sites.tensor true A X) (Sites.proPull A e.hom)).hom
  let b := Functor.uncurry.map
    (ProEtale.leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} B) e.hom).inv ≫
    (uncurryPostcompose (Sites.tensor true B X) (Sites.proPull B e.hom)).hom
  let lhs := Functor.whiskerRight (c.prod c) (Functor.uncurry.obj (Sites.tensor true B Y)) ≫
    Functor.whiskerLeft ((Sites.proPull A e.hom).prod (Sites.proPull A e.hom)) δ.inv ≫
    Functor.whiskerRight a (Sites.scalar true φ Y)
  let rhs := Functor.whiskerLeft ((Sites.scalar true φ X).prod (Sites.scalar true φ X)) b ≫
    Functor.whiskerRight μ.inv (Sites.proPull B e.hom) ≫
    Functor.whiskerLeft (Functor.uncurry.obj (Sites.tensor true A X)) c
  have ha (K L : Sites.D true A X) : a.app (K, L) =
      (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) e.hom K L).inv := by
    exact Category.comp_id _
  have hb (K L : Sites.D true B X) : b.app (K, L) =
      (ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} B) e.hom K L).inv := by
    exact Category.comp_id _
  refine ⟨lhs, rhs, ?_, ?_⟩
  · intro K L
    change (c.app K ⊗ₘ c.app L) ≫
      δ.inv.app ((Sites.proPull A e.hom).obj K, (Sites.proPull A e.hom).obj L) ≫
      (Sites.scalar true φ Y).map (a.app (K, L)) = _
    rw [ha]
  · intro K L
    change b.app ((Sites.scalar true φ X).obj K, (Sites.scalar true φ X).obj L) ≫
      (Sites.proPull B e.hom).map (μ.inv.app (K, L)) ≫ c.app (K ⊗ L) = _
    rw [hb]

end WeilConjectures.FiniteFreeCoefficients
