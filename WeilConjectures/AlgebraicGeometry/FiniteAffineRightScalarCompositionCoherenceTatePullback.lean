/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceData
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatSingleTensorCompatibilityDataSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-! # Finite Tate scalar naturality under geometric inverse image -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.Etale
open WeilConjectures.PurityFiniteSetting

/-- Source: latest blueprint, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts, finite Tate reassociation.
(blueprint: lem-sp-finite-affine-right-scalar-composition-coherence-tate-pullback)

Proof: Use the assumed balanced beta families. On an inverse-image root generator, both ordinary
maps send (z tensor a) tensor b to f*z tensor phi(a)b. The adjunction bijection and sheaf tensor
universal property prove the degree-one square. The zero-power square is the coefficient unit law.
Induct on the nonnegative power, using the normalized successor tensor formulas for beta and root
pullback and the monoidality of scalar pullback. Flatness of the Tate sheaves allows localization
of these ordinary equalities through the specified scalar/single and geometric single comparisons.
For the final equation paste the two squares, move beta past the compositor by naturality, and use
scalar and root-pullback composition. -/
theorem finiteAffineRightScalarCompositionCoherenceTatePullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (hX : ∀ x : X, IsUnit (N : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (N : Y.presheaf.stalk y))
    (hZ : ∀ z : Z, IsUnit (N : Z.presheaf.stalk z))
    (u : X ⟶ Y) (v : Y ⟶ Z) :
    let globalUnit := fun (W : Scheme.{u})
      (hW : ∀ w : W, IsUnit (N : W.presheaf.stalk w)) ↦
        W.toRingedSpace.isUnit_of_isUnit_germ ⊤ (N : Γ(W, ⊤))
          (fun w _ ↦ by simpa only [map_natCast] using hW w)
    let line := fun (R : Type (u + 1)) [CommRing R] (hR : (N : R) = 0)
      (W : Scheme.{u}) (r : ℕ) ↦ Scheme.finiteEtaleTateTwist W N R hR r
    let single := fun (R : Type (u + 1)) [CommRing R] (hR : (N : R) = 0)
      (W : Scheme.{u}) (r : ℕ) ↦ (DerivedCategory.singleFunctor _ 0).obj (line R hR W r)
    let betaType := fun (W : Scheme.{u}) ↦
      ∀ r : ℕ, (purityScalarSheaf φ W).obj (line A hA W r) ≅ line B hB W r
    let betaMap := fun (W : Scheme.{u}) (β : betaType W) (r : ℕ) ↦
      purityScalarSingleMap φ W (line A hA W r) ≫
        (DerivedCategory.singleFunctor _ 0).map (β r).hom
    let rho := fun (R : Type (u + 1)) [CommRing R] (hR : (N : R) = 0)
      {S T : Scheme.{u}} (f : S ⟶ T)
      (hT : ∀ t : T, IsUnit (N : T.presheaf.stalk t))
      (hS : ∀ s : S, IsUnit (N : S.presheaf.stalk s)) (r : ℕ) ↦
        singleFunctorPullbackMap f
          ((Scheme.finiteEtaleTwistPullbackData R N hN hR).c f
            (globalUnit T hT) (globalUnit S hS) (r : ℤ)).hom
    let betaSquare := fun {S T : Scheme.{u}} (f : S ⟶ T)
      (hT : ∀ t : T, IsUnit (N : T.presheaf.stalk t))
      (hS : ∀ s : S, IsUnit (N : S.presheaf.stalk s))
      (βT : betaType T) (βS : betaType S) ↦
      ∀ r : ℕ,
        L(upperStar (ModuleCat.{u + 1} B) f).map (betaMap T βT r) ≫
            rho B hB f hT hS r =
          (scalarPullbackIso φ f).hom.app (single A hA T r) ≫
            (scalarExtension φ S).map (rho A hA f hT hS r) ≫ betaMap S βS r
    (∀ (βX : betaType X) (βY : betaType Y) (βZ : betaType Z),
      IsFiniteTateScalarBalancing φ N hA hB X βX →
      IsFiniteTateScalarBalancing φ N hA hB Y βY →
      IsFiniteTateScalarBalancing φ N hA hB Z βZ →
      betaSquare u hY hX βY βX ∧ betaSquare v hZ hY βZ βY ∧
      betaSquare (u ≫ v) hZ hX βZ βX ∧
      (∀ r : ℕ,
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) u v).hom.app
            ((scalarExtension φ Z).obj (single A hA Z r)) ≫
          L(upperStar (ModuleCat.{u + 1} B) u).map
            (L(upperStar (ModuleCat.{u + 1} B) v).map (betaMap Z βZ r) ≫ rho B hB v hZ hY r) ≫
          rho B hB u hY hX r =
        (scalarPullbackIso φ (u ≫ v)).hom.app (single A hA Z r) ≫
          (scalarExtension φ X).map (rho A hA (u ≫ v) hZ hX r) ≫ betaMap X βX r)) := by
  sorry

end AlgebraicGeometry.Etale
