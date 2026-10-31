/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
import WeilConjectures.AlgebraicGeometry.System.SystemTensorReductionFormula
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictSystemGeometricRealization
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictPlusComparisonsRealization
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictPlusEvaluationRealization
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictOpenWordEvaluation
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictFiniteWordIdentification
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Assembly of normalized strict compactification comparisons

Source: blueprint operations proof (2).
(blueprint: lem-sp-strict-compactification-comparison-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

private noncomputable def comparison_module_model_equivalence (X : Scheme.{u})
    (A : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    SheafOfModules.{u + 1}
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
        RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj A) ≌
      SheafOfModules.{u + 1} A := by
  let B := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj A
  let : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsContinuous
      (ProEt.topology X) (proEtaleModelTopology X) := proEtaleModelUp_isContinuous X
  let : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsContinuous
      (proEtaleModelTopology X) (ProEt.topology X) := by
    change AsSmall.down.IsContinuous (proEtaleModelTopology X) (ProEt.topology X)
    infer_instance
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)) (𝟙 A) (𝟙 B)
    (by ext U; dsimp [AsSmall.equiv]; erw [B.obj.map_id]; rfl)
    (by ext U; dsimp [AsSmall.equiv]; erw [A.obj.map_id]; rfl)


namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Simultaneous normalized realization of the compactification comparisons.
Source: blueprint main-20261015, operations proof (2)
(blueprint: lem-sp-strict-compactification-comparison-realization).

Proof:
1. Identify Tow with the ringed sequence-site modules by the identity on all
   sections, restrictions, actions and maps (det-sp-coefficient-towers-abelian).
   Transport the existing semilinear-derived-sections calculus through that
   exact equivalence. These are operations on ordinary unbounded localizations.
2. The system-tensor reduction formula gives tensorReduction on arbitrary
   inputs. Apply its actual reduction cocycles and normalized tensor associators
   twice to obtain compatibility for three indices, including equal indices.
3. The geometric calculus fixes direct-image transitions as G(t) b, with b the
   specified counit mate. Mate-pasting identifies the composite coefficient mate
   with the composite scalar square. Naturality and the input reduction cocycle
   give the three-index direct-image coherence, without invertibility of b.
4. The tower category has enough injectives. A bounded-below injective complex
   is K-injective, so the same representative computes both right derived
   functors. Uniqueness of right derivation gives plusComparison with its
   normalization. The adjunction and evaluation comparisons come from the same
   ordinary squares, so units and counits are preserved.
5. Apply the open tensor normalization on the ringed sequence site to get the
   open tensor and exchange isomorphisms. Their inverses are the displayed
   open-adjunction transposes. Evaluation preserves these transposes, hence
   gives the finite normalized maps, with no sign ambiguity.
6. Form the proper counit projection followed by G_p of the open tensor map
   and pullback compositor. Its functorial factors give projectionNaturality;
   evaluation of each factor gives projectionEvaluation. On the finite-field
   domain this is exactly the composite of def-exchange-projection. The actual
   ideals identify R_n with A_(E,e(n+1)), since ell = unit times uniformizer^e.
   Fix the finite realization's underlying comparison to the additive
   sheafification counit (Stacks 00YV). Its inverse is the unit on sections;
   the pure-total and resolving-representative pins therefore identify the
   finite tensor comparison itself, without independent scalar rescalings.
7. Form the proper square mate followed by the open exchange. Evaluating its
   unit, square, counit and open factor proves exchangeEvaluation. The finite
   exchange-transport theorem identifies this word, on each bounded-below
   etale-origin witness, with the exchange transported from def-cbc-exchange-map
   in thm-cbc-finite-level-proetale. The open is quasi-compact since f is
   quasi-compact and the proper factor is separated. Witnesses are used one
   level at a time, with no equation between different witnesses.
8. Tensor evaluation and tensorReduction apply to every second input. In
   particular substitute any specified coefficient-twist tower on a scheme
   where ell is invertible. Its actual quotient transitions are retained.
-/
theorem strictCompactificationComparisonRealization :
    ∃ b : Base l E, ∃ o : Operations l E b, ∃ x : OpenExchange l E b o,
      StrictCompactificationComparisons l E b o x := by
  obtain ⟨b, o, hsections, hscalar, hmate⟩ := strictSystemGeometricRealization l E
  have hsystem : StrictSystemComparisons l E b o := by
    refine ⟨hsections, ?_, hscalar, hmate⟩
    intro T K L m n h
    exact SemilinearSections.tensor_reduction_formula
      (Scheme.ProEt.topology T) (B l E T) (tau l E T) (b.calculus T) K L h
  obtain ⟨x, levels, hword⟩ := strictOpenWordEvaluation l E b o hsystem
  let h : ∀ T : Scheme.{u}, EnoughInjectives (S l E T) := fun T ↦ by
    let := (b.calculus T).grothendieck
    infer_instance
  let hl : ∀ (T : Scheme.{u}) (n : ℕ),
      EnoughInjectives (proEtaleRingModules.{u} T (proEtaleConstantRing T (R l E n))) :=
    fun T n ↦ by
      let A := (sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing T (R l E n))
      let B := ((AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).sheafPushforwardContinuous
        RingCat.{u + 1} (proEtaleModelTopology T) (ProEt.topology T)).obj A
      let e := comparison_module_model_equivalence T A
      let := SheafOfModules.isGrothendieckAbelian B
      let : IsGrothendieckAbelian.{u + 1}
          (proEtaleRingModules.{u} T (proEtaleConstantRing.{u} T (R l E n))) :=
        IsGrothendieckAbelian.of_equivalence e
      exact IsGrothendieckAbelian.enoughInjectives.{u + 1, u + 1, u + 2}
  refine ⟨b, o, x, levels, hsystem, h, strictPlusComparisonsRealization l E b o, hl,
    strictPlusEvaluationRealization l E b o, hword, ?_⟩
  exact strictFiniteWordIdentification l E b o levels

end AlgebraicGeometry.ProEtale.SpTowerShriek
