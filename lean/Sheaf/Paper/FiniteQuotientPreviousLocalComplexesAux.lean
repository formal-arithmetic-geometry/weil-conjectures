/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.FiniteQuotientCoefficientLayerData
public import Sheaf.Paper.FiniteCoefficientLocalHomologyModels

/-! # Single-chart conversion for the previous quotient model
Source: Stacks Project, Tags 0942, 094H and 094I.
(blueprint: lem-weil-pbc-finite-quotient-previous-local-complexes-chart).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The algebraic conversion on one etale chart.  This is the local algebra step
in the proof of `finiteQuotient_previous_local_complexes`; the covering-sieve
assembly is performed there. -/
theorem finiteQuotient_previous_local_complexes_chart
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n))
    (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d))
    (V : X.Etale) (W Z : X.Etale) (g : W ⟶ V) (f : Z ⟶ W)
    (a b : ℤ) (hab : a ≤ b) (n : ℕ)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))) ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hfinite : ∀ i : ℤ,
      Module.Projective (A ⧸ d.ideal ^ (n + 1)) (P.X i) ∧
        Module.Finite (A ⧸ d.ideal ^ (n + 1)) (P.X i))
    (e : Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj Z) ((completedAdicQuotientReduction X d n).obj M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj Z) ((completedAdicDerivedChange X (φ n)).obj
            (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P))))) :
    ∃ Q : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1 + 1))) ℤ,
      Q.IsStrictlyGE a ∧ Q.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Finite (A ⧸ d.ideal ^ (n + 1 + 1)) (Q.X i)) ∧
        ∀ q : ℤ, Nonempty
          ((SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
              ((DerivedCategory.homologyFunctor _ q).obj
                (finiteQuotientPreviousObject X d M n)) ≅
            (SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
              ((finiteCoefficientConstantFunctor X
                (A ⧸ d.ideal ^ (n + 1 + 1)) (φ (n + 1))).obj (Q.homology q))) := by
  sorry

end AlgebraicGeometry.Scheme
