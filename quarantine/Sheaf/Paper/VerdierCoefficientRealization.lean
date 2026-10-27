/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.SixFunctors.BoundaryDualityInput
public import Sheaf.Paper.FiniteStageVerdierBiduality
public import Sheaf.SixFunctors.IntegralVerdier
public import Sheaf.SixFunctors.RationalVerdier
public import Sheaf.SixFunctors.CoefQbarVerdier
public import Sheaf.Paper.VerdierExchange
public import Sheaf.SixFunctors.RationalOperations
public import Sheaf.SixFunctors.CoefIntegralFiniteExtension
import Sheaf.SixFunctors.BoundaryDualityDischarge
import Sheaf.Paper.IntegralResidueTor
import Sheaf.Paper.IntegralDualizingExceptionalUnit
import Sheaf.Paper.ConstantCoefficientObjectsConstructible

/-! # Evaluation-defined Verdier duality through coefficients

Source: main-20261015, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, clause (7)
(blueprint: lem-sf-package-verdier-coefficient-realization).

All predicates below refer to the published coefficient constructions. In particular,
`VerdierExchange.Assertion` requires `StageConclusion.components`: its natural isomorphism
has precisely `StageData.epsilon` as components, rather than unspecified invertible maps.
That arrow is the construction owned by `def-sf-verdier-exchange-data`: projection and
evaluation followed by the exceptional, tensor--Hom and ordinary adjunction transposes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.ConstructibleExceptionalCoefficients

namespace WeilConjectures

/-- The geometric duality assertions on one separated finite-type scheme. Positive finite
levels are indexed by `n + 1`. Integral presentations retain their coherent reduction
counits, and the integral conclusion uses the actual evaluation-defined comparison and
biduality. Rational and common-stage assertions retain the corresponding actual maps.
`BoundaryDualityInput` uses the same zero-based index: its index `n` means `A_(n+1)`.
The common-stage assertion asks only for duality, its internal Hom realization and its
exceptional value at the unit; no formula for other exceptional functors is added.

Source: main-20261015, prop-functor-package.proof.md, clause (7)
(blueprint: lem-sf-package-verdier-coefficient-realization). -/
def VerdierCoefficientRealizationOn
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))] : Prop :=
  (∀ n : ℕ,
    FiniteProEtaleVerdierBiduality C.l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      T (T ↘ Spec (.of D.k))) ∧
  (∀ n : ℕ, ProEtale.BoundaryDualityInput D C.l C.different E n
    T (T ↘ Spec (.of D.k))) ∧
  (∃ (w : IntegralFiniteExtension.DualizingDatum C.l T D C.different E)
    (S : RationalOperations.structureSystem C.l T D C.different C.Qbar)
    (U : ConstructibleExceptionalCoefficients.C C.l C.Qbar
      (Spec (.of D.k)) (.integral { carrier := E })),
    Nonempty ((RingStage.inclusion C.l C.Qbar (Spec (.of D.k))
      (.integral { carrier := E })).obj U ≅
        VerdierExchange.ringUnit C.l (Spec (.of D.k)) (.integral { carrier := E })) ∧
    Nonempty ((RingStage.inclusion C.l C.Qbar T (.integral { carrier := E })).obj
      ((S.ring.operation (integralDualizingCompactification D T)
        (.integral { carrier := E })).G.obj U) ≅ w.omega.obj) ∧
    IntegralVerdier.Conclusion C.l E T D C.different w.omega w.reduction ∧
    ∃ r : RationalVerdier.Datum D C.l C.different T E w,
      Nonempty (RationalOperations.HomIdentification C.l E T D C.different w r) ∧
      RationalOperations.DualizingIdentification C.l T D C.different C.Qbar S
        { carrier := E } w) ∧
  RationalVerdier.Conclusion D C.l C.different T ∧
  ∃ B : CoefQbarVerdier.Duality D C.l C.different C.Qbar T,
    Nonempty (CoefQbarVerdier.InternalHom D C.l C.different C.Qbar T B) ∧
    CoefQbarVerdier.Dualizing D C.l C.different C.Qbar T B

/-- Evaluation-defined constructible Verdier duality at all four coefficient stages.
The scheme assertion includes geometric finite biduality, boundary exchange as a
conclusion, integral preservation and uniform dimension bounds, and actual coefficient
passage of evaluation and biduality. The exchange assertion includes naturality, shifts
and the specified coefficient comparison squares, and pins epsilon to the evaluation
transpose of `def-sf-verdier-exchange-data`. No ambient exceptional-adjoint admissibility
or boundary duality input is a hypothesis.

Source: main-20261015, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, clause (7)
(blueprint: lem-sf-package-verdier-coefficient-realization).

Proof, following the accepted seven-step split:
1. Apply thm-fix-general-biduality to every positive finite level on T. Its pro-etale
   conclusion gives the exact finite-Tor anti-equivalence and invertibility of delta.
   By lem-weil-duality-pairing this delta is the tensor-Hom transpose of evaluation,
   with the signed tensor symmetry; no boundary hypothesis enters this step.
2. Apply cor-weil-boundary-duality-discharge. It covers every locally closed piece
   and closed immersion, with beta the transpose of the specified evaluation pairing.
   It therefore gives the entire boundary input as a conclusion of geometric duality.
3. Use prop-coef-integral-dualizing for its coherent completed dualizing presentation,
   identified with the constructible exceptional value at the unit. Apply
   thm-coef-integral-verdier to obtain equality of the constructible and uniform
   finite-Tor domains, preservation, exact anti-equivalence and the output interval
   [-b-2d,-a]. Its canonical reduction maps preserve evaluation, its transposes and
   actual delta; reconstruction and invertibility of delta complete the integral clause.
4. Apply thm-coef-rational-verdier. Rationalizing the same integral maps gives the
   E-linear exact anti-equivalence, evaluation and delta. Its extension comparisons
   obey unit and associator equations. Lem-coef-rational-operations identifies this
   dual with internal Hom into the constructible exceptional value at E.
5. Apply thm-coef-qbar-verdier and retain its duality, InternalHom and Dualizing
   conclusions. Its finite-origin equations identify evaluation and biduality at a
   common coefficient field, including their restrictions to every retract.
6. The finite-Tor domain is exactly the chosen finite domain. At R it is the whole
   constructible domain by step 3. At both field stages this is the definition in
   def-weil-finite-tor-amplitude; thus all allowed M are exchange inputs.
7. Apply sk-thm-sf-verdier-exchange to f and these inputs. Its package supplies c and
   the natural exchange with components StageData.epsilon, the successive exceptional,
   tensor-Hom and ordinary adjunction transposes of projection and evaluation. The
   ring realizations and coefficient squares identify finite, completed, rationalized
   and common-stage comparisons, including shifts. Only the constructible exceptional
   functor is used. Combine this exchange with steps 1--5 for every T.
-/
theorem verdier_coefficient_realization
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (∀ (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
      [IsSeparated (T ↘ Spec (.of D.k))]
      [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))],
      VerdierCoefficientRealizationOn D C E T) ∧
    VerdierExchange.Assertion C.l C.Qbar D C.different f := by
  constructor
  · intro T _ _ _ _
    refine ⟨?_, ?_, ?_, coef_rational_verdier D C.l C.different T, ?_⟩
    · intro n
      exact (finite_stage_verdier_biduality D C.l C.different E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) T (T ↘ Spec (.of D.k))).2
    · intro n
      exact ProEtale.boundary_duality_input D C.l C.different E n T
        (T ↘ Spec (.of D.k))
    · obtain ⟨_, S, hS⟩ := coef_rational_operations D C.l C.different C.Qbar
        T T (𝟙 T) (Compactification.ofIsProper (𝟙 T))
      obtain ⟨I, _, _, _, _, hdual, _⟩ :=
        hS { carrier := E } { carrier := E } (AlgHom.id (Padic C.l) E)
      let P := Spec (.of D.k)
      let (x : P) : Invertible (C.l : P.residueField x) :=
        (show IsUnit (C.l : P.residueField x) by
          simpa using (finiteFieldDatumPrimeUnit D C.l C.different).map
            ((P ↘ Spec (.of D.k)).residueFieldAlgebraMap x)).invertible
      have hconstant :=
        (integralConstantCoefficient_constructible C.l E P D C.different).2.1
      have hunit : finiteTorConstructibleIntegral C.l E P
          (integralConstantCoefficientObject C.l E P) :=
        (integral_residue_tor D C.l C.different E P).2 ▸ hconstant
      let U : ConstructibleExceptionalCoefficients.C C.l C.Qbar P
          (.integral { carrier := E }) :=
        ⟨integralConstantCoefficientObject C.l E P, hunit⟩
      refine ⟨I.wX, S, U, ⟨Iso.refl _⟩, ?_, ?_, I.DX, ⟨I.homX⟩, hdual⟩
      · exact integral_dualizing_exceptional_unit D C.l C.different C.Qbar E T
          S I.wX U ⟨Iso.refl _⟩
      · exact integral_verdier_biduality D C.l C.different E T I.wX.omega I.wX.reduction
    · obtain ⟨B, hhom, hdual, _⟩ := coef_qbar_verdier D C.l C.different C.Qbar T
      exact ⟨B, hhom, hdual⟩
  · exact VerdierExchange.verdier_exchange C.l C.Qbar D C.different f

end WeilConjectures
