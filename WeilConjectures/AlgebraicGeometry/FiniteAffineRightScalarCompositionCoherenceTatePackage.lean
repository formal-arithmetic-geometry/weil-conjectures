/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineTatePairing
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceData
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatSingleTensorCompatibilityDataSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import WeilConjectures.AlgebraicGeometry.FiniteAffineRightScalarCompositionCoherenceTatePullback
import WeilConjectures.AlgebraicGeometry.FiniteAffineRightScalarCompositionCoherenceTateTensor

/-! # Finite Tate balancing, pullback, and ordered tensor compatibility -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.Etale
open WeilConjectures.PurityFiniteSetting

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar
  WeilConjectures.PurityFiniteSetting.purityScalarSingleMap

private theorem assembleTateFields {P Q R S T U V : Prop}
    (hp : P ∧ Q ∧ R ∧ V) (ht : S ∧ T ∧ U) : P ∧ Q ∧ R ∧ S ∧ T ∧ U ∧ V :=
  ⟨hp.1, hp.2.1, hp.2.2.1, ht.1, ht.2.1, ht.2.2, hp.2.2.2⟩

set_option maxHeartbeats 2000000 in
-- The nested Tate comparisons require a larger elaboration and kernel-check budget.
/-- Source: latest blueprint, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts, finite Tate factors of the
canonical reassociation.
(blueprint: lem-sp-finite-affine-right-scalar-composition-coherence-tate-package)

Proof: apply the finite Tate pullback lemma to the three balanced beta families.
It supplies the three beta/rho squares and the pasted compositor equation.
Apply the ordered tensor lemma to the same families to obtain the three binary
product equations. Assemble the seven conjuncts in their displayed order. -/
theorem finiteAffineRightScalarCompositionCoherenceTatePackage
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
    let tateTensor := fun (R : Type (u + 1)) [CommRing R] [Finite R] (hR : (N : R) = 0)
      (W : Scheme.{u}) (hW : ∀ w : W, IsUnit (N : W.presheaf.stalk w)) (r s : ℕ) ↦
        finiteAffineTatePairing R N hN hR W hW r s
    let betaSquare := fun {S T : Scheme.{u}} (f : S ⟶ T)
      (hT : ∀ t : T, IsUnit (N : T.presheaf.stalk t))
      (hS : ∀ s : S, IsUnit (N : S.presheaf.stalk s))
      (βT : betaType T) (βS : betaType S) ↦
      ∀ r : ℕ,
        L(upperStar (ModuleCat.{u + 1} B) f).map (betaMap T βT r) ≫
            rho B hB f hT hS r =
          (scalarPullbackIso φ f).hom.app (single A hA T r) ≫
            (scalarExtension φ S).map (rho A hA f hT hS r) ≫ betaMap S βS r
    let betaTensor := fun (W : Scheme.{u})
      (hW : ∀ w : W, IsUnit (N : W.presheaf.stalk w)) (β : betaType W) ↦
      ∀ r s : ℕ,
        (scalarExtension φ W).map (tateTensor A hA W hW r s) ≫ betaMap W β (r+s) =
          (ExceptionalCoefficients.tensorIso φ W).hom.app (single A hA W r, single A hA W s) ≫
            derivedTensorHom (ModuleCat.{u + 1} B) (betaMap W β r) (betaMap W β s) ≫
            tateTensor B hB W hW r s
    (∀ (βX : betaType X) (βY : betaType Y) (βZ : betaType Z),
      IsFiniteTateScalarBalancing φ N hA hB X βX →
      IsFiniteTateScalarBalancing φ N hA hB Y βY →
      IsFiniteTateScalarBalancing φ N hA hB Z βZ →
      betaSquare u hY hX βY βX ∧ betaSquare v hZ hY βZ βY ∧
      betaSquare (u ≫ v) hZ hX βZ βX ∧
      betaTensor X hX βX ∧ betaTensor Y hY βY ∧ betaTensor Z hZ βZ ∧
      (∀ r : ℕ,
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) u v).hom.app
            ((scalarExtension φ Z).obj (single A hA Z r)) ≫
          L(upperStar (ModuleCat.{u + 1} B) u).map
            (L(upperStar (ModuleCat.{u + 1} B) v).map (betaMap Z βZ r) ≫ rho B hB v hZ hY r) ≫
          rho B hB u hY hX r =
        (scalarPullbackIso φ (u ≫ v)).hom.app (single A hA Z r) ≫
          (scalarExtension φ X).map (rho A hA (u ≫ v) hZ hX r) ≫ betaMap X βX r)) := by
  intro globalUnit line single betaType betaMap rho tateTensor betaSquare betaTensor
  intro βX βY βZ hβX hβY hβZ
  exact assembleTateFields
    (finiteAffineRightScalarCompositionCoherenceTatePullback
      φ N hN hA hB hX hY hZ u v βX βY βZ hβX hβY hβZ)
    (finiteAffineRightScalarCompositionCoherenceTateTensor
      φ N hN hA hB hX hY hZ u v βX βY βZ hβX hβY hβZ)

end AlgebraicGeometry.Etale
