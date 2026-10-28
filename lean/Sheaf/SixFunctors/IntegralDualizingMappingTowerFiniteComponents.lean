/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import Sheaf.SixFunctors.IntegralDualizingMappingTower

/-! # Coherent component comparisons for strict mapping towers

Source: current blueprint prop-coef-integral-dualizing, second proof paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/--
The finite exceptional adjunctions provide a coherent component comparison before
those components are assembled into a natural isomorphism of functors.  The
component family is indexed by the opposite integral constructible category, and
its equation is the naturality square for every morphism in that category.

Source: current blueprint prop-coef-integral-dualizing, middle and final displayed
comparisons in the second proof paragraph, and its final counit-compatibility sentence.
(blueprint: lem-coef-integral-dualizing-mapping-tower-finite-comparison).

Proof: resolve the completed-coefficient tower simultaneously.  Residue Tor
invariance and compact-support reduction identify the finite compact-support
complexes with reductions of the integral value, while point sections preserve
those identifications and their maps.  Scalar tensor-restriction adjunction and
the finite exceptional adjunction then give the component isomorphisms.  The
specified equation `he`, together with the counit compatibility of the finite
adjunction, identifies their transitions under every quotient map.  Evaluation
naturality and injectivity of currying give the displayed naturality equation.
The construction is made before any inverse limit and does not choose an
unrelated trace.  For zero inputs and empty schemes the same construction has
zero source and target and remains valid.
-/
theorem integralDualizing_mapping_tower_finite_components
    (T : NormalizedDVRTower l E X D hl)
    (e : ∀ n : ℕ, T.M n ≅ integralDualizingFiniteTerm l E D X n)
    (he : ∀ {m n : ℕ} (h : n ≤ m),
      T.tau h ≫ (normalizedDVRRes l E X h).map (e n).hom =
        (e m).hom ≫
          (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
            (integralDualizingFiniteComparison l E D X hl h)) :
    ∃ (a : ∀ K : (sfIntegralConstructibleCategory l E X)ᵒᵖ,
      (integralDualizingMappingTower l E X T.tower).obj K ≅
        ((integralDualizingCompactSections l E D hl X).op ⋙
          integralDualizingCoefficientHomTower l E).obj K),
      ∀ {K L : (sfIntegralConstructibleCategory l E X)ᵒᵖ} (f : K ⟶ L),
        (integralDualizingMappingTower l E X T.tower).map f ≫ (a L).hom =
          (a K).hom ≫
            ((integralDualizingCompactSections l E D hl X).op ⋙
              integralDualizingCoefficientHomTower l E).map f := by
  sorry

end WeilConjectures
