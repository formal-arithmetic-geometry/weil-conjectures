/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts

import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationLocalTraceCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.DerivedDegreeZeroNormalization
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSheafHomFamilyGluing

/-!
# Integration along a vector bundle

The coefficient is expressed by the existing ordered tensor of shifted finite Tate lines:
its pullback to E is A_E(d)[2d]. The local map is the actual compact-support exchange for
the inverse frame, followed by the canonical Tate comparison and the existing affine trace.
The global map is the unique morphism obtained by gluing these local traces.

## Main definitions

- `vectorIntegrationCoefficient`, `vectorIntegrationSource`: A_E(d)[2d] and C_pi.
- `vectorIntegrationLocalTrace`: the prescribed trace on each linear trivialization.
- `VectorIntegrationNormalization`: the local characterization, for every frame.
- `vectorBundleIntegration`: the unique global map with those restrictions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem local_normalization_iff (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    {L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : vectorIntegrationSource A N hA S d F ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj L)
    (ell : L ⟶ ordinaryFiniteConstant A S) :
    VectorIntegrationNormalization N hN A hA S hS d F
        (α.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map ell) ↔
      ∀ (t : OrdinaryFiniteTwistTransport A N hA)
        (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
          OrdinaryFiniteP1Datum A N hA t T hT)
        (V : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F V),
        (localizationRestriction (ModuleCat.{u + 1} A) V.ι inferInstance).map ell =
          vectorIntegrationLocalSheafTrace N hN A hA t D S hS d F α V e := by
  constructor
  · intro h t D V e
    exact (vectorIntegrationLocalSheafTrace_normalization_iff
      N hN A hA t D S hS d F α ell V e).1 (h t D V e)
  · intro h t D V e
    exact (vectorIntegrationLocalSheafTrace_normalization_iff
      N hN A hA t D S hS d F α ell V e).2 (h t D V e)

private theorem existsUnique_normalized_sheaf_trace (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    {L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : vectorIntegrationSource A N hA S d F ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj L) :
    ∃! ell : L ⟶ ordinaryFiniteConstant A S,
      VectorIntegrationNormalization N hN A hA S hS d F
        (α.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map ell) := by
  classical
  obtain ⟨t, D, _, _⟩ := exists_affineSpaceTopTrace N hN A hA
  obtain ⟨I, V, hV, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := d)
  let ψ := fun i : I ↦
    vectorIntegrationLocalSheafTrace N hN A hA t D S hS d F α (V i) (e i).some
  have hcover : ∀ x : S, ∃ (i : I) (y : (V i).toScheme), (V i).ι.base y = x := by
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hV.ge (Set.mem_univ x) : x ∈ ⨆ i, V i)
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  obtain ⟨ell, hell, huniq⟩ := existsUnique_etaleSheafHom_of_family A
    (fun i : I ↦ (V i).ι) hcover L (ordinaryFiniteConstant A S) ψ
    (fun W i j q q' ↦ vectorIntegrationLocalSheafTrace_compatible N hN A hA
      S hS d F α t t D D (V i) (V j) (e i).some (e j).some W q q')
  have hnorm : VectorIntegrationNormalization N hN A hA S hS d F
      (α.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map ell) := by
    apply (local_normalization_iff N hN A hA S hS d F α ell).2
    intro t' D' V' e'
    apply etaleSheafHom_restriction_eq_of_compatible A
      (fun i : I ↦ (V i).ι) hcover L (ordinaryFiniteConstant A S) ψ
      (fun W i j q q' ↦ vectorIntegrationLocalSheafTrace_compatible N hN A hA
        S hS d F α t t D D (V i) (V j) (e i).some (e j).some W q q') ell hell V'.ι
    · intro W i q q'
      exact vectorIntegrationLocalSheafTrace_compatible N hN A hA
        S hS d F α t t' D D' (V i) V' (e i).some e' W q q'
    · intro W q q'
      exact descentComponent_eq_of_mono A V'.ι _ W q q'
  refine ⟨ell, hnorm, ?_⟩
  intro μ hμ
  exact huniq μ (fun i ↦
    (local_normalization_iff N hN A hA S hS d F α μ).1 hμ t D (V i) (e i).some)

/-- The unique sheaf-glued derived trace. This is the existence and uniqueness needed
by the definition, not a choice of a morphism from a mere nonempty Hom set.
-/
theorem existsUnique_vectorIntegrationGluing (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    (∀ q : ℤ, q ≠ 0 → IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      (vectorIntegrationSource A N hA S d F))) ∧
    ∃! p :
        (vectorIntegrationSource A N hA S d F ≅
          (_root_.DerivedCategory.singleFunctor _ 0).obj
            (vectorIntegrationSheaf A N hA S d F)) ×
        (vectorIntegrationSheaf A N hA S d F ⟶ ordinaryFiniteConstant A S),
      (_root_.DerivedCategory.homologyFunctor _ 0).map p.1.hom ≫
          (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app
            (vectorIntegrationSheaf A N hA S d F) =
        𝟙 (vectorIntegrationSheaf A N hA S d F) ∧
      VectorIntegrationNormalization N hN A hA S hS d F
        (p.1.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map p.2) := by
  dsimp only [vectorIntegrationSheaf]
  have hz := vectorIntegration_cohomology_zero N hN A hA S hS d F
  refine ⟨hz, _root_.DerivedCategory.existsUnique_normalized_iso_and_map
    (vectorIntegrationSource A N hA S d F) (ordinaryFiniteConstant A S) hz
    (VectorIntegrationNormalization N hN A hA S hS d F) ?_⟩
  intro α
  exact existsUnique_normalized_sheaf_trace N hN A hA S hS d F α

/-- The canonical truncation identification alpha_pi and the glued sheaf map lambda.
The H^0 normalization determines alpha_pi, and all frame restrictions determine lambda. -/
def vectorIntegrationGluing (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    (vectorIntegrationSource A N hA S d F ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj (vectorIntegrationSheaf A N hA S d F)) ×
    (vectorIntegrationSheaf A N hA S d F ⟶ ordinaryFiniteConstant A S) :=
  (existsUnique_vectorIntegrationGluing N hN A hA S hS d F).2.exists.choose

/-- Integration t_pi, the unique map restricting on each linear trivialization to the
specified affine-space trace. -/
def vectorBundleIntegration (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    vectorIntegrationSource A N hA S d F ⟶ ordinaryFiniteUnit A S :=
  (vectorIntegrationGluing N hN A hA S hS d F).1.hom ≫
    (_root_.DerivedCategory.singleFunctor _ 0).map
      (vectorIntegrationGluing N hN A hA S hS d F).2

end AlgebraicGeometry.Etale
