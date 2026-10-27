/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.Paper.FiniteQuotientCoefficientLayerData
public import Sheaf.Paper.FiniteCoefficientLocalHomologyModels

/-! # Homology transport for the previous quotient chart model
Source: Stacks Project, Tags 0942, 094H and 094I.
(blueprint: lem-weil-pbc-finite-quotient-previous-local-complexes-chart-homology).

The hard comparison step is isolated here: after restriction of scalars along
the quotient from the successor coefficient ring, the supplied chart
comparison identifies every slice homology object with the corresponding
constant realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Transport the supplied chart comparison to homology after restriction of scalars.

Source: Stacks Project, sites-cohomology.tex, Tags 0942, 094H and 094I.
The quotient map from `A ⧸ I^(n+2)` to `A ⧸ I^(n+1)` is exact on modules,
slice restriction, and constant realization. Applying the derived homology
functor to the supplied comparison and composing the coefficient compatibility
isomorphisms gives the displayed isomorphism in every degree.
(blueprint: lem-weil-pbc-finite-quotient-previous-local-complexes-chart-homology).
-/
theorem finiteQuotient_previous_local_complexes_chart_homology
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
    (e : Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj Z) ((completedAdicQuotientReduction X d n).obj M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj Z) ((completedAdicDerivedChange X (φ n)).obj
            (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P))))) :
    let qring : A ⧸ d.ideal ^ (n + 1 + 1) →+* A ⧸ d.ideal ^ (n + 1) :=
      Ideal.Quotient.factorPowSucc d.ideal (n + 1)
    let Q := ((ModuleCat.restrictScalars qring).mapHomologicalComplex (.up ℤ)).obj P
    ∀ q : ℤ, Nonempty
      ((SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            (finiteQuotientPreviousObject X d M n)) ≅
        (SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
          ((finiteCoefficientConstantFunctor X
            (A ⧸ d.ideal ^ (n + 1 + 1)) (φ (n + 1))).obj (Q.homology q))) := by
  sorry

end AlgebraicGeometry.Scheme
