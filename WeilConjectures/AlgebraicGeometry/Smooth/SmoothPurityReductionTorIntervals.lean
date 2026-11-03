/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTorAmplitude
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionHomologyIntervals

/-! # Integral and finite-level Tor bounds in the fixed presentations

Source: blueprint latest, normalized-towers-reduction, final Tor-bound sentence;
Stacks Tags 0651, 06YY, 08FZ.
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

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

/-- On a qcqs scheme a bounded constructible integral complex has finite Tor
amplitude. Every one of its Tor intervals transfers to all evaluated reductions,
both as a Tor interval and as a cohomological interval.

Source: blueprint latest, sec-smooth-purity, normalized-towers-reduction, Tor bounds;
Stacks Tags 0651, 06YY, 08FZ
(blueprint: lem-sp-reduction-tower-tor-intervals).

Proof:
1. Identify the condensed integer ring of E with the integer ring of its image in
an algebraic closure, and apply the integral bounded-constructibility theorem.
This gives finite Tor amplitude of the internalization.
2. For any specified Tor interval [a,b], take a bounded flat internal representative.
The exact section-module equivalence transports it to a site-flat representative
of M with zero terms outside [a,b]. Bounded-above site-flatness gives K-flatness.
3. Extend this representative termwise by the reduction scalar map. Its terms stay
flat and its zero terms stay zero. The scalar model's K-flat counit and the supplied
evaluation comparison identify its derived image with the evaluated reduction.
The bounded-flat characterization of HasProEtaleTorAmplitude gives the same Tor
interval at each level. Zero terms outside the interval give zero homology, which
transports through the representative isomorphism.
The helpers prove these steps without assuming flatness of the quotient map.
The order assumption and all levels, degrees, zero complexes and empty schemes
are retained.
-/
theorem sp_reduction_tower_tor_intervals
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
    DerivedCategory.finiteTorAmplitude _ ((spIntegralInternalization l E T).obj M) ∧
    ∀ (a b : ℤ), a ≤ b →
      DerivedCategory.torAmplitudeIn _ a b ((spIntegralInternalization l E T).obj M) →
      ∀ n : ℕ,
        Scheme.HasProEtaleTorAmplitude T
          (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
          ((spDerivedCoefficientEvaluation l E T D n).obj (red.obj M)) a b ∧
        ∀ i : ℤ, (i < a ∨ b < i) → IsZero
          ((@DerivedCategory.homologyFunctor
            (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T
              (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))
            _ _ (HasDerivedCategory.standard _) i).obj
            ((spDerivedCoefficientEvaluation l E T D n).obj (red.obj M))) := by
  constructor
  · exact (sp_reduction_tower_tor_amplitude l E T D coefficient red evaluation M hM).1
  · intro a b hab htor n
    exact ⟨
      (sp_reduction_tower_tor_amplitude l E T D coefficient red evaluation M hM).2
        a b hab htor n,
      sp_reduction_tower_homology_interval l E T D coefficient red evaluation M hM
        a b hab htor n⟩

end AlgebraicGeometry.ProEtale
