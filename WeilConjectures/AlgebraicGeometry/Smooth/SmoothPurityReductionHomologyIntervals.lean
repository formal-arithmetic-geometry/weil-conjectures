/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTorAmplitude
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor

/-! Cohomological support transport for the normalized smooth-purity reduction tower.
Source: blueprint latest, normalized-towers, uniform Tor and cohomological bounds.
(blueprint: lem-sp-reduction-tower-tor-intervals).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall in
/-- Every specified integral Tor interval bounds the homology of every evaluated
reduction, with the same endpoints.

Source: blueprint latest, sec-smooth-purity/sk-def-sp-normalized-towers/_section.md,
uniform bounds; the reduction argument of lem-sp-reduction-tower-tor-intervals;
Stacks Tags 06YY and 08FZ
(blueprint: lem-sp-reduction-tower-homology-helper).

Proof: apply sp_reduction_tower_tor_amplitude in the specified interval and level.
The proved bounded-flat characterization of the intrinsic Tor predicate supplies a
representative P whose terms outside [a,b] are zero. In such a degree i, the short
complex centered at P.X i has zero middle object, hence zero homology. Transport
this fact through the representative isomorphism and homologyFunctorFactors.
The argument includes the zero complex and the empty scheme. -/
theorem sp_reduction_tower_homology_interval
    (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (red : DerivedCategory (spIntegralSectionModules l E T) ⥤
      spDerivedCoefficientTowers l E T D)
    (evaluation : spReductionDerivedEvaluations l E T D coefficient red)
    [CompactSpace T] [QuasiSeparatedSpace T]
    (M : DerivedCategory (spIntegralSectionModules l E T))
    (hM : constantModelBoundedConstructible (spIntegralCondensed l E) T
      ((spIntegralInternalization l E T).obj M)) :
    ∀ (a b : ℤ), a ≤ b →
      DerivedCategory.torAmplitudeIn.{u + 1, u + 1, u + 2}
        (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (spIntegralCondensed l E) T)) a b
        ((spIntegralInternalization l E T).obj M) →
      ∀ n : ℕ, ∀ i : ℤ, (i < a ∨ b < i) → IsZero
          ((@DerivedCategory.homologyFunctor
            (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T
              (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))
            _ _ (HasDerivedCategory.standard _) i).obj
            ((spDerivedCoefficientEvaluation l E T D n).obj (red.obj M))) := by
  intro a b hab htor n i hi
  have ht := (sp_reduction_tower_tor_amplitude l E T D coefficient red evaluation M hM).2
    a b hab htor n
  obtain ⟨P, _, hb, ⟨e⟩⟩ := (scalarExtension_tor_flat_model T _ _ a b hab).mp ht
  exact ((P.sc i).isZero_homology_of_isZero_X₂ (hb i hi)).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app P)
end AlgebraicGeometry.ProEtale
