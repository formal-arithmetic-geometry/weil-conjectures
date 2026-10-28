/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q8
-/
module

public import Sheaf.SixFunctors.IntegralDualizingMappingTower

/-! # A quotient-system realization of one normalized DVR tower -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- A finite semilinear derived tower has a strict quotient-system representative,
whose completed restriction is isomorphic to the given strict tower.

Source: blueprint prop-coef-integral-dualizing, second paragraph, first mapping
comparison; Stacks 079P and 070I.
(blueprint: lem-coef-normalized-dvr-quotient-system-realization).

Proof: choose a complex P_0 representing T.M 0. After choosing P_n, transport
T.tau(n+1,n) to a map into the restriction of P_n. The right-fraction presentation
of a derived morphism replaces its source by a quasi-isomorphic complex P_(n+1)
and supplies a strict semilinear chain map to P_n. Inductively choose these roofs.
Compose successor chain maps, with the canonical restriction-composition maps.
The identity and associativity of restriction give a complex of strict quotient
systems. The sequence-site equivalence makes it a complex Q of modules over the
quotient sequence ring. The roof isomorphisms supply a_n. For successors the
square is the defining equation of the roof; induction using T.tau_comp proves
it for all n ≤ m, and T.tau_refl handles equal indices.
The completion projections commute with the quotient maps. Hence the a_n,
after exact restriction, compose with T.evaluationIso to give compatible
isomorphisms from the evaluated T.tower to the evaluated restriction of Q.
Sequential tower fullness lifts this fixed compatible family. Its isomorphism
criterion makes the lift invertible. No lift depending on a varying Hom input
is chosen. Zero complexes and the empty scheme give the same construction;
no normalization, constructibility, boundedness or flatness is used in these
steps beyond the supplied tower data. -/
theorem normalizedDVR_quotient_system_realization
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : NormalizedDVRTower l E X D hl) :
    ∃ (Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
      (a : ∀ n : ℕ, T.M n ≅
        (coefficientSequenceDerivedEvaluation l E X n).obj (coefTraceInput l E X Q)),
      (∀ {m n : ℕ} (h : n ≤ m),
        T.tau h ≫ (normalizedDVRRes l E X h).map (a n).hom =
          (a m).hom ≫ (coefficientSequenceDerivedTransition l E X h).app
            (coefTraceInput l E X Q)) ∧
      Nonempty (T.tower ≅ (coefficientSequenceDerivedRestriction l E X).obj
        (coefTraceInput l E X Q)) := by sorry

end WeilConjectures
