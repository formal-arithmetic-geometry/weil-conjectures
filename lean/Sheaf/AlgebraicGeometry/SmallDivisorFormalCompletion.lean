/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.FormalCompletionGeometry
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import WeilConjectures.RingTheory.FiniteTypeGRing
import WeilConjectures.RingTheory.GRingCompletionRegular
import Sheaf.RingTheory.RegularMapReducedTarget
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.RegularLocalMaximal
import WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber
import WeilConjectures.RingTheory.FlatUnderRegular
import WeilConjectures.RingTheory.RegularBaseChange
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import WeilConjectures.RingTheory.LocalizationRegular
import WeilConjectures.RingTheory.RegularComposition
import Mathlib.RingTheory.Finiteness.Ideal

/-! # Completion along a small Cartier divisor

Source: Temkin, Non-embedded desingularization, proof of Theorem 3.4.1, printed p.26;
§§2.4.1,2.4.3,2.4.9,2.4.11,3.1.1--3.1.4
(blueprint: lem-per-small-divisor-formal-completion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- Completion along a small divisor gives a reduced quasi-excellent rig-regular locally
principal finite disjoint union of characteristic-zero formal varieties.
Source: Temkin, proof of Theorem 3.4.1, printed p.26
(blueprint: lem-per-small-divisor-formal-completion).

Proof plan:
1. Refine a finite Noetherian affine cover to Cartier trivializations. Completion is
   Noetherian by lem-weil-pbc-adic-completion-noetherian. Its extended ideal defines the
   topology and its quotient is the original closed fibre by
   lem-weil-pbc-adic-completion-mod-ideal. The inverse limit of the thickening sheaves
   restricts on each affine chart to its formal spectrum, and its space is the divisor.
2. The quotient B/I is quasi-excellent: the Noetherian, G-ring and J-2 conditions descend
   to finite-type quotients. Apply lem-per-qe-complete-pair-lifting to the completed pair.
   The same argument applies after localization and completion to formal open charts,
   using lem-weil-pbc-localization-noetherian and lem-weil-pbc-finite-type-over-g-ring.
3. The map B to its completion is regular by lem-weil-pbc-g-ring-completion-regular,
   so reducedness follows by lem-exc-regular-map-reduced-target. Flat tensor exactness
   (lem-weil-pbc-flat-tensor-exact) preserves the injectivity of multiplication by a
   Cartier generator, making the extended ideal regular principal on the chosen cover.
4. By lem-weil-pbc-regular-local-maximal the local maps are regular. Regularity ascends
   by lem-weil-pbc-flat-over-regular-with-regular-fibre and descends by
   lem-weil-pbc-flat-under-regular. Thus the nonregular locus pulls back exactly.
5. For the reduced singular ideal J, regular base change
   (lem-weil-pbc-regular-base-change) and reduced ascent show that its extension is
   radical. The nonregular locus calculation identifies it with the completed singular
   ideal. By lem-weil-pbc-completion-finite-module-tensor, the completed quotient is
   the inverse limit of B/(J+I^n), giving the completed singular subscheme.
6. The ideals glue: the maps to completed distinguished opens are regular by
   lem-weil-pbc-localization-regular, lem-weil-pbc-g-ring-completion-regular and
   lem-weil-pbc-regular-composition. The same local calculation identifies their
   singular ideals and quotient completions on overlaps.
7. Containment of the singular locus in the divisor gives I contained in the radical
   of J. By lem-weil-pbc-fg-ideal-radical-power a positive power of I is contained in J;
   extend this containment to completed charts. This is the openness of the singular
   ideal, hence rig-regularity.
8. The finite clopen decomposition of D lifts to the completion. Each reduced closed
   fibre is the reduction of a finite-type scheme over its given characteristic-zero
   field, hence is finite type. For the empty divisor all quotient rings are zero, so
   the ringed space is empty. This includes the empty ambient scheme. -/
theorem SmallSingularLocusPair.formalCompletion_geometry (P : SmallSingularLocusPair.{u}) :
    AdicFormalCompletion.IsNoetherianFormalSpace P.completion.space ∧
    P.completion.IsReducedQuasiExcellent ∧
    (∀ U : P.scheme.affineOpens,
      Nonempty (P.completion.chartSpace U ≅
        AdicFormalCompletion.formalSpectrum (.of (P.completion.chartRing U))
          (P.completion.chartIdeal U))) ∧
    Nonempty (P.completion.space ≃ₜ P.completion.closedFibre) ∧
    P.completion.HasInvertibleIdealOfDefinition ∧
    P.completion.IsFiniteDisjointUnionOfFormalVarieties ∧
    P.completion.HasCompletedSingularLocus ∧
    P.completion.IsRigRegular ∧
    (P.divisor = ⊤ → IsEmpty P.completion.space) := by
  sorry

end AlgebraicGeometry
