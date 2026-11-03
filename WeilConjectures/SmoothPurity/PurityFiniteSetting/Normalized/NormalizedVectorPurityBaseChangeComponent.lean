/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityBaseChange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorIntegrationCartesianTrace
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Normalized.FiniteNormalizedBaseChange

/-! # The component calculation for two integration-normalized vector purity families. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry.Etale

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

/-- Cache the actual family with the ordinary-functor presentation of its type. -/
private def retypeGamma (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (B : Scheme.{u}) [IsNoetherian B]
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    (γ : VectorPurityGamma A N hA B d F) :
    RfPullback A (VectorBundleZeroSection.π B d F) ⋙
      tensorLeft (Etale.vectorIntegrationCoefficient A N hA B d F) ⟶
    RfUpper A (VectorBundleZeroSection.π B d F) := γ

private theorem normalization_explicit (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hB : IsUnit (N : Γ(B, ⊤)))
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    (γ : VectorPurityGamma A N hA B d F)
    (hn : VectorPurityGammaNormalized A N hN hA B hB d F γ) :
  IntegrationGammaNormalized
    (RfShriek A (VectorBundleZeroSection.π B d F))
    (RfUpper A (VectorBundleZeroSection.π B d F))
    (RfPullback A (VectorBundleZeroSection.π B d F))
    (Etale.rightDerivedUpperShriekAdjunction A
      (VectorBundleZeroSection.π B d F))
    (Etale.vectorIntegrationCoefficient A N hA B d F)
    (Etale.vectorBundleIntegration N hN A hA B hB d F ≫
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) B).hom)
    ((Etale.projectionMap (ModuleCat.{u + 1} A)
      (VectorBundleZeroSection.π B d F)).app
        (Etale.vectorIntegrationCoefficient A N hA B d F)) (retypeGamma A N hA B d F γ) := by
  exact hn

/-- The canonical coefficient comparison, with its bundle coefficient type cached. -/
private def bundleCoefficientComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {B B' : Scheme.{u}} [IsNoetherian B] [IsNoetherian B']
    (hB : IsUnit (N : Γ(B, ⊤))) (d : ℕ) (F : B.Modules) (F' : B'.Modules)
    [F.IsFiniteLocallyFreeOfRank d] [F'.IsFiniteLocallyFreeOfRank d]
    {g : B' ⟶ B}
    {g' : VectorBundleZeroSection.scheme B' d F' ⟶ VectorBundleZeroSection.scheme B d F}
    (sq : IsPullback g' (VectorBundleZeroSection.π B' d F')
      (VectorBundleZeroSection.π B d F) g)
    : (RfPullback A g').obj (Etale.vectorIntegrationCoefficient A N hA B d F) ≅
      Etale.vectorIntegrationCoefficient A N hA B' d F' :=
  purityPullbackSquare A sq (Etale.affineLinearBaseCoefficient A N hA B d) ≪≫
    (RfPullback A (VectorBundleZeroSection.π B' d F')).mapIso
      (Etale.vectorIntegrationBaseCoefficientPullback A N hA
        (purityTwistTransport A N hN hA) g hB d)

/-- The canonical bundle comparison has its displayed tensor-comparison formula. -/
private theorem assocHom (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {B B' : Scheme.{u}} [IsNoetherian B] [IsNoetherian B']
    (hB : IsUnit (N : Γ(B, ⊤))) (d : ℕ) (F : B.Modules) (F' : B'.Modules)
    [F.IsFiniteLocallyFreeOfRank d] [F'.IsFiniteLocallyFreeOfRank d]
    {g : B' ⟶ B}
    {g' : VectorBundleZeroSection.scheme B' d F' ⟶ VectorBundleZeroSection.scheme B d F}
    (sq : IsPullback g' (VectorBundleZeroSection.π B' d F')
      (VectorBundleZeroSection.π B d F) g)
    (K : Etale.DerivedCategoryModule A B) :
    HEq ((Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g'
    (Etale.vectorIntegrationCoefficient A N hA B d F)
    ((RfPullback A (VectorBundleZeroSection.π B d F)).obj K) ≪≫
    ((purityPullbackSquare A sq (Etale.affineLinearBaseCoefficient A N hA B d) ≪≫
        (RfPullback A (VectorBundleZeroSection.π B' d F')).mapIso
          (Etale.vectorIntegrationBaseCoefficientPullback A N hA
            (purityTwistTransport A N hN hA) g hB d)) ⊗ᵢ purityPullbackSquare A sq K)).hom)
      (purityBundleBaseChangeAssociator A N hN hA hB d F F' sq K).hom := HEq.rfl

-- The inferred type is needed to cache this specialization without duplicating its expansion.
set_option linter.defProp false in
/-- Specialize the geometric data before supplying the normalized families.
Caching this partial application separates the derived-functor data checks from checking the
normalization proofs. The definition infers the full specialized type from the proved
finite-coefficient calculation; its value is that complete proof, with no new assumption. -/
private def bundle_mate_rule
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {B B' : Scheme.{u}} [IsNoetherian B] [IsNoetherian B']
    (hB : IsUnit (N : Γ(B, ⊤))) (hB' : IsUnit (N : Γ(B', ⊤)))
    (d : ℕ) (F : B.Modules) (F' : B'.Modules)
    [F.IsFiniteLocallyFreeOfRank d] [F'.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    [HasCompactification (VectorBundleZeroSection.π B' d F')]
    [QuasiCompact (VectorBundleZeroSection.π B' d F')]
    {g : B' ⟶ B}
    {g' : VectorBundleZeroSection.scheme B' d F' ⟶ VectorBundleZeroSection.scheme B d F}
    (sq : IsPullback g' (VectorBundleZeroSection.π B' d F')
      (VectorBundleZeroSection.π B d F) g) :=
  let f := VectorBundleZeroSection.π B d F
  let f' := VectorBundleZeroSection.π B' d F'
  let W := Etale.vectorIntegrationCoefficient A N hA B d F
  let W' := Etale.vectorIntegrationCoefficient A N hA B' d F'
  let l := bundleCoefficientComparison A N hN hA hB d F F' sq
  let t : (RfShriek A f).obj W ⟶ 𝟙_ (Etale.DerivedCategoryModule A B) :=
    Etale.vectorBundleIntegration N hN A hA B hB d F ≫
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) B).hom
  let t' : (RfShriek A f').obj W' ⟶ 𝟙_ (Etale.DerivedCategoryModule A B') :=
    Etale.vectorBundleIntegration N hN A hA B' hB' d F' ≫
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) B').hom
  finiteIntegrationNormalized_baseChange A
    (f := f) (f' := f') (g := g) (g' := g') sq W W' l t t'
    (fun K ↦ purityBundleBaseChangeAssociator A N hN hA hB d F F' sq K)
    (fun K ↦ assocHom A N hN hA hB d F F' sq K)

/-- The component base-change equation after both normalized families have been supplied.
Source: current blueprint sk-prop-an, cor-pur-vector-bundle-purity.proof.md, paragraph 2.
Proof: apply the finite-coefficient projection and mate calculation to the actual bundle
coefficient comparison and scalar Cartesian integration identity.
(blueprint: lem-pur-normalized-vector-purity-base-change-component). -/
theorem vectorIntegrationCounit_baseChange_component
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {B B' : Scheme.{u}} [IsNoetherian B] [IsNoetherian B']
    (hB : IsUnit (N : Γ(B, ⊤))) (hB' : IsUnit (N : Γ(B', ⊤)))
    (d : ℕ) (F : B.Modules) (F' : B'.Modules)
    [F.IsFiniteLocallyFreeOfRank d] [F'.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    [HasCompactification (VectorBundleZeroSection.π B' d F')]
    [QuasiCompact (VectorBundleZeroSection.π B' d F')]
    {g : B' ⟶ B}
    {g' : VectorBundleZeroSection.scheme B' d F' ⟶ VectorBundleZeroSection.scheme B d F}
    (sq : IsPullback g' (VectorBundleZeroSection.π B' d F')
      (VectorBundleZeroSection.π B d F) g)
    (γ : VectorPurityGamma A N hA B d F) (γ' : VectorPurityGamma A N hA B' d F')
    (hn : VectorPurityGammaNormalized A N hN hA B hB d F γ)
    (hn' : VectorPurityGammaNormalized A N hN hA B' hB' d F' γ')
    (hi : ∀ K : Etale.DerivedCategoryModule A B, IsIso (γ.app K))
    (hi' : ∀ K : Etale.DerivedCategoryModule A B', IsIso (γ'.app K))
    (K : Etale.DerivedCategoryModule A B) :
    IsIso ((Etale.rightDerivedUpperShriekBaseChangeMap A sq).app K) ∧
      (RfPullback A g').map (γ.app K) ≫
        (Etale.rightDerivedUpperShriekBaseChangeMap A sq).app K =
      (purityBundleBaseChangeAssociator A N hN hA hB d F F' sq K).hom ≫
        γ'.app ((RfPullback A g).obj K) := by
  exact bundle_mate_rule A N hN hA hB hB' d F F' sq
    (retypeGamma A N hA B d F γ) (retypeGamma A N hA B' d F' γ')
    (normalization_explicit A N hN hA B hB d F γ hn)
    (normalization_explicit A N hN hA B' hB' d F' γ' hn') hi hi'
    (vectorIntegration_cartesianTrace A N hN hA hB hB' d F F' sq) K

end WeilConjectures.PurityFiniteSetting
