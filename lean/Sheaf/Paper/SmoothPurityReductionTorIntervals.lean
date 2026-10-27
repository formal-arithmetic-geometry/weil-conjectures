/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Paper.SmoothPurityReductionTowerData


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

/-- On a qcqs scheme a bounded constructible integral complex has finite Tor
amplitude. Every one of its Tor intervals transfers to all evaluated reductions,
both as a Tor interval and as a cohomological interval.

Source: blueprint latest, sec-smooth-purity, normalized-towers-reduction, Tor bounds;
Stacks Tags 0651, 06YY, 08FZ
(blueprint: lem-sp-reduction-tower-tor-intervals).

Proof:
1. The exact section/internal module equivalence identifies the source coefficient
ring and its derived tensor with the pulled-back condensed integer coefficients.
The integral clause of localizingClosure_ctf_equals_bc gives Tor amplitude [r-1,s]
for a bounded constructible complex with cohomology in [r,s]. Transport a finite
extension E to its isomorphic finite subextension of the algebraic closure, when
applying that theorem; the induced coefficient and module equivalences preserve
the finite constant models and derived tensor. Thus it applies to the given E.
2. Fix a Tor interval [a,b] and an R_n-module N in degree zero. The evaluation
isomorphism identifies the level with derived extension to R_n. Apply
siteDerivedTensorRestriction to get Res((M tensor R_n) tensor N) isomorphic to
M tensor Res(N). Exact scalar restriction changes neither the underlying sheaf
nor its homology, so the assumed vanishing gives [a,b] at every level.
3. The section/internal equivalence and the canonical K-flat tensor comparison
identify this vanishing with HasProEtaleTorAmplitude, whose definition tests every
K-flat representative. Independence of the representative gives all its quantifiers.
Take N=R_n and use the tensor unitor for the cohomological support assertion.
No flatness of the quotient map is used. The order assumption a<=b is retained;
zero complexes and empty schemes require no exception.
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
            ((spDerivedCoefficientEvaluation l E T D n).obj (red.obj M))) := by sorry

end AlgebraicGeometry.ProEtale
