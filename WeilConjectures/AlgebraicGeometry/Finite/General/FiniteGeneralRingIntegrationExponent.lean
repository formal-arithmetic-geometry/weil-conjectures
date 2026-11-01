/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingLocalTraceExponent

/-! # Kummer exponent comparison of the vector-bundle integration

Source: general-ring smooth purity, proof (3), Kummer exponent independence.
(blueprint: lem-sp-general-ring-integration-exponent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

private theorem integration_eq_of_normalization
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d]
    (k : Etale.vectorIntegrationSource A N hA S d F ⟶
      Etale.ordinaryFiniteUnit A S)
    (hk : Etale.VectorIntegrationNormalization N hN A hA S hS d F k) :
    k = Etale.vectorBundleIntegration N hN A hA S hS d F := by
  let p := Etale.vectorIntegrationGluing N hN A hA S hS d F
  obtain ⟨ell, hell⟩ := (_root_.DerivedCategory.singleFunctor _ 0).map_surjective
    (p.1.inv ≫ k)
  have he : p.1.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map ell = k := by
    rw [hell, ← Category.assoc, p.1.hom_inv_id, Category.id_comp]
  have hp' : (_root_.DerivedCategory.homologyFunctor _ 0).map p.1.hom ≫
      (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app
        (Etale.vectorIntegrationSheaf A N hA S d F) =
        𝟙 (Etale.vectorIntegrationSheaf A N hA S d F) ∧
      Etale.VectorIntegrationNormalization N hN A hA S hS d F
        (p.1.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map p.2) := by
    dsimp only [p]
    unfold Etale.vectorIntegrationGluing
    exact (Etale.existsUnique_vectorIntegrationGluing N hN A hA S hS d F).2.exists.choose_spec
  have heq : (p.1, ell) = p :=
    (Etale.existsUnique_vectorIntegrationGluing N hN A hA S hS d F).2.unique
      ⟨hp'.1, by rw [he]; exact hk⟩ hp'
  have hell' : ell = p.2 := congrArg Prod.snd heq
  rw [← he, hell']
  unfold Etale.vectorBundleIntegration
  rfl

/-- A root-normalized Kummer exponent comparison preserves actual vector-bundle
integration, before taking an adjunction transpose or restricting to the zero section.

Source: general-ring smooth purity, proof (3), exponent independence, and proof (2),
the Kummer projective-line normalization and vector-bundle integration step.
(blueprint: lem-sp-general-ring-integration-exponent).

Proof: write M = N times k. The morphism from the M-Kummer sequence to the N-Kummer
sequence has k-th power on the units term containing the roots, and identity on
the last units term. Boundary naturality sends the M-boundary of O(1) to its
N-boundary. After extension to A, the scalar/root generator equation for b
identifies the two Chern classes. The projective-line decomposition has these
Chern classes as its second columns and the twisted units as its first columns.
Naturality of the unit and normalized Tate pullback identifies the first columns.
Thus the decompositions, their inverses and second-projection traces commute with
the root-line comparison. Naturality of the open-extension counit gives the same
identity on the affine line. Iterate in the prescribed coordinate order, using
counit naturality at each step: the zero-coordinate transition and counit are
identities; at a successor the counit is the preceding counit after the preceding
left functor applied to the last affine-line counit. This proves the ordered
affine trace identity without permuting factors. On each frame of F the actual
bundle integration restricts to this affine trace after inverse-frame exchange
and normalized Tate pullback. Those comparisons are natural on scalar/root
generators, so the coefficient map in this identity is exactly pullback of
finiteGeneralRingLevelPower. The equations on all frames identify the global
integration maps: the sources have only degree-zero cohomology by the affine
trace isomorphism, so derived single full faithfulness reduces the equality to
sheaf-Hom equality, detected by the frame cover. This includes the empty cover
on an empty scheme. At rank zero the tensor and the counit are identities; for
the zero ring every displayed morphism is the unique morphism.
-/
theorem finiteGeneralRingIntegrationExponent
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (M N : ℕ) (hMpos : 0 < M) (hNpos : 0 < N) (hdiv : N ∣ M)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (M : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (q : S.rootsOfUnitySheaf M ⟶ S.rootsOfUnitySheaf N)
    (b : Scheme.finiteEtaleTateLine S M A hM ≅
      Scheme.finiteEtaleTateLine S N A hN)
    (hb : FiniteGeneralRingKummerComparison A M N hM hN S q b) :
    (Etale.vectorBundlePurityLower A S d F).map
        ((Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).map
          (finiteGeneralRingLevelPower A M N hM hN S b d).hom) ≫
        Etale.vectorBundleIntegration N hNpos A hN S hS' d F =
      Etale.vectorBundleIntegration M hMpos A hM S hS d F := by
  let P := Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)
  let e := finiteGeneralRingLevelPower A M N hM hN S b d
  let k := (Etale.vectorBundlePurityLower A S d F).map (P.map e.hom) ≫
    Etale.vectorBundleIntegration N hNpos A hN S hS' d F
  have hk : Etale.VectorIntegrationNormalization M hMpos A hM S hS d F k := by
    intro t D V eV
    have hl := finiteGeneralRingLocalTraceExponent A M N hMpos hNpos hdiv
      hM hN S hS hS' d F q b hb t D V eV
    dsimp only [k, P, e]
    simpa only [Functor.map_comp, Category.assoc] using hl
  change k = Etale.vectorBundleIntegration M hMpos A hM S hS d F
  exact integration_eq_of_normalization M hMpos A hM S hS d F k hk

end AlgebraicGeometry.ProEtale
