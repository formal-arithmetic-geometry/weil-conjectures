/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCoefficientLayerTriangle
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerLocalComplexes
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientPreviousLocalComplexes

/-! # The controlled outer terms of the coefficient-filtration triangle

Source: Stacks Project, sites-cohomology.tex, Tags 0942, 094I and 094H.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Tensoring the coefficient-layer sequence gives a distinguished triangle
whose middle term is the actual successor reduction and whose outer terms have
bounded finite etale-local cohomology. No assertion is made about the homology of
the middle term.

Source: proetale.tex, Tag 09C2. -/
theorem finiteQuotient_cohomology_filtration_triangle
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (a b : ℤ) (hab : a ≤ b)
    (hresidue : FinitePerfectModelsOn X d φ M 0 V a b) (n : ℕ)
    (hprevious : FinitePerfectModelsOn X d φ M n V a b) :
    let B := A ⧸ d.ideal ^ (n + 1 + 1)
    let R₀ := completedAdicFiniteRing X d (n + 1)
    let K := (completedAdicQuotientReduction X d (n + 1)).obj M
    let P : ObjectProperty (SheafOfModules.{t + 1} R₀) := fun F ↦
      ∀ (W : X.Etale) (_g : W ⟶ V),
        ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧
          ∀ (Z : X.Etale) (f : Z ⟶ W), S f →
            ∃ N : ModuleCat.{t} B, Module.Finite B N ∧ Nonempty
              ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj F ≅
                (SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj
                  ((completedAdicChange X (φ (n + 1))).obj
                    ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                      ModuleCat.restrictScalars.{t + 1}
                        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
                      koszulConstantFunctor X B).obj N)))
    ∃ T : Triangle (DerivedCategory (SheafOfModules.{t + 1} R₀)),
      T ∈ distTriang _ ∧ Nonempty (T.obj₂ ≅ K) ∧
        (∀ q : ℤ, q < a ∨ b < q →
          IsZero ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj V)).obj
            ((DerivedCategory.homologyFunctor _ q).obj T.obj₁)) ∧
          IsZero ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj V)).obj
            ((DerivedCategory.homologyFunctor _ q).obj T.obj₃))) ∧
        DerivedCategory.homologyProperty P T.obj₁ ∧
        DerivedCategory.homologyProperty P T.obj₃ := by
  have : Finite (A ⧸ d.ideal ^ (n + 1 + 1)) := d.quotientFinite (n + 1)
  obtain ⟨T, hT, ⟨e₁⟩, e₂, ⟨e₃⟩⟩ :=
    finiteQuotient_coefficient_layer_triangle X d M n
  have h₁ := finiteCoefficient_local_homology_models X
    (A ⧸ d.ideal ^ (n + 1 + 1)) (φ (n + 1))
    (finiteQuotientLayerObject X d M n) V a b
    (finiteQuotient_layer_local_complexes X d φ hφ hcompat M V a b hab n hresidue)
  have h₃ := finiteCoefficient_local_homology_models X
    (A ⧸ d.ideal ^ (n + 1 + 1)) (φ (n + 1))
    (finiteQuotientPreviousObject X d M n) V a b
    (finiteQuotient_previous_local_complexes X d φ hφ hcompat M V a b hab n hprevious)
  refine ⟨T, hT, e₂, ?_, ?_, ?_⟩
  · intro q hq
    exact ⟨(h₁.1 q hq).of_iso
        ((SheafOfModules.overFunctor _ ((toProEt X).obj V)).mapIso
          ((DerivedCategory.homologyFunctor _ q).mapIso e₁)),
      (h₃.1 q hq).of_iso
        ((SheafOfModules.overFunctor _ ((toProEt X).obj V)).mapIso
          ((DerivedCategory.homologyFunctor _ q).mapIso e₃))⟩
  · intro q W g
    obtain ⟨S, hS, hs⟩ := h₁.2 q W g
    refine ⟨S, hS, ?_⟩
    intro Z f hf
    obtain ⟨N, hN, ⟨e⟩⟩ := hs Z f hf
    exact ⟨N, hN, ⟨(SheafOfModules.overFunctor _ ((toProEt X).obj Z)).mapIso
      ((DerivedCategory.homologyFunctor _ q).mapIso e₁) ≪≫ e⟩⟩
  · intro q W g
    obtain ⟨S, hS, hs⟩ := h₃.2 q W g
    refine ⟨S, hS, ?_⟩
    intro Z f hf
    obtain ⟨N, hN, ⟨e⟩⟩ := hs Z f hf
    exact ⟨N, hN, ⟨(SheafOfModules.overFunctor _ ((toProEt X).obj Z)).mapIso
      ((DerivedCategory.homologyFunctor _ q).mapIso e₃) ≪≫ e⟩⟩

end AlgebraicGeometry.Scheme
