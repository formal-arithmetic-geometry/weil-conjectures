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

/-! # Finite Tate scalar compatibility with ordered products -/

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
(blueprint: lem-sp-finite-affine-right-scalar-composition-coherence-tate-tensor)

Proof: Use the assumed generator normalization of beta. The finite Tate pairing concatenates the
ordered roots. On a balanced pure tensor both paths keep this ordered tuple and give coefficient
phi(a*a_prime)*b*b_prime. The sheaf tensor universal property proves equality. For an empty tuple
use the zero-power unit normalization. Equivalently induct on the two powers using the successor
normalization, associativity and the unit equations of the canonical Tate pairing. Each Tate sheaf
is flat, so its single complex is K-flat; the specified flat-single pairing and scalar tensorator
represent exactly these ordinary maps. Localizing the equality gives the displayed derived
equation on X, Y and Z. -/
theorem finiteAffineRightScalarCompositionCoherenceTateTensor
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
    let tateTensor := fun (R : Type (u + 1)) [CommRing R] [Finite R] (hR : (N : R) = 0)
      (W : Scheme.{u}) (hW : ∀ w : W, IsUnit (N : W.presheaf.stalk w)) (r s : ℕ) ↦
        finiteAffineTatePairing R N hN hR W hW r s
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
      betaTensor X hX βX ∧ betaTensor Y hY βY ∧ betaTensor Z hZ βZ) := by
  sorry

end AlgebraicGeometry.Etale
