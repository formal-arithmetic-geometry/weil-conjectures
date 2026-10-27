/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Sheaf.Paper.ConstructibleAlgClTopologyComparison
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.Paper.RingedCoefficientProjectionCocycle
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.ProperBasic
import Sheaf.Paper.FiniteCoefficientDescentTwoColimit
import Sheaf.Paper.ProperBaseChangeRational
import Sheaf.Paper.QlbarDirectImageComparison
import Sheaf.Paper.ContinuousAlgClConstructibleTor
import Sheaf.Paper.ProperLocalizingContinuousAlgCl

/-!
# Constructible domains for the two-stage proper algebraic-closure comparison

Source: blueprint, direct-image stability proof paragraph (3), proper coefficient-change input
(blueprint: lem-sfb-proper-algcl-comparison-domains).

The chosen algebraic closure is PadicAlgCl with its extended ell-adic norm. Its
finite-subextension-valued condensed ring C and its all-continuous condensed ring B
are distinct. All functors below act on ordinary unbounded derived internal modules.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The five constructible endpoints and finite-Tor input of the proper two-stage
coefficient comparison, together with invertibility of the intermediate counit mate.
Source: blueprint direct-image stability proof paragraph (3), proper coefficient-change input
(blueprint: lem-sfb-proper-algcl-comparison-domains).

Here S is derivedExtendScalarsToPadicAlgCl and J is algClTopologyScalarExtension.
The displayed derivedPushHom is the canonical coefficient mate: its geometric adjunct
is the inverse derivedPullIso followed by S of the A_E-counit. Its balanced-tensor
normalization is the one in lem-pur-ringed-coefficient-projection-cocycle. The finite
coefficient flatness instances used internally by this existing map are inferred facts,
not hypotheses of the theorem; no flatness of C to B is asserted or assumed.

Proof, following the six steps of the DAG:
1. A field is Noetherian since its ideals are zero or the unit ideal. Its affine
spectrum is quasi-compact (lem-weil-pbc-affine-scheme-qcqs, pqf-def-locnoeth).
Finite type over it makes Z and T Noetherian
(lem-weil-pbc-finite-type-over-noetherian). Properness makes f qcqs
(pqf-lem-proper-basic).
2. The rational-category identification in sk-thm-sfb-qlbar-two-colimit (4)
identifies the constant-model constructible categories with the ordinary finite-field
and finite-subextension-valued algebraic-closure categories. The functor of
 def-sfb-derived-extend-to-qlbar is exactly S. Apply
lem-sfb-extend-to-qlbar-constructible to obtain constructibility of L = S_Z K.
3. Apply det-thm-sfb-proper-base-change-rational (2) at coefficient C, and the same
rational-category identification on T, to obtain constructibility of P = Rf_{*,C} L.
4. Bounded K is bounded below. The qcqs comparison
lem-sfb-qlbar-direct-image-comparison gives invertibility of the A_E-to-C mate.
Its defining adjunct is exactly the specified chi, so uniqueness of adjuncts
identifies the maps. This uses no ambient unbounded coproduct-continuity assumption.
5. Apply lem-sfb-constructible-algcl-topology-comparison to L on Z and P on T.
The actual K-flat functors J_Z and J_T give constructibility of J_Z L and J_T P.
On Noetherian Z, det-sf-comp-continuous-algcl-constructible-tor gives finite Tor
amplitude of J_Z L. The coefficient here uses all continuous norm-valued maps.
6. Apply the preservation clause of det-sf-comp-proper-continuous-algcl to the
bounded constant-model constructible finite-Tor input J_Z L. It gives bounded
constructibility of Q = Rf_{*,B} J_Z L in the ordinary ambient derived category. -/
theorem properAlgClComparisonDomains
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (_hp : 0 < p) (_hpℓ : p ≠ ℓ) (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {Z T : Scheme.{u}} [Z.Over (Spec (.of k))] [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    (f : Z ⟶ T) [f.IsOver (Spec (.of k))] [IsProper f]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (padicSubfieldRingObj.{u} Z ℓ E)))
    (_hK : constantModelBoundedConstructible.{u} (Profinite.continuousMapRingObj.{u} E) Z K) :
    constantModelBoundedConstructible.{u} (Profinite.padicAlgClRingObj.{u} ℓ) Z
      ((derivedExtendScalarsToPadicAlgCl.{u} Z ℓ E).obj K) ∧
    constantModelBoundedConstructible.{u} (Profinite.padicAlgClRingObj.{u} ℓ) T
      ((moduleObjectDerivedPushforward.{u} (Profinite.padicAlgClRingObj.{u} ℓ) f).obj
        ((derivedExtendScalarsToPadicAlgCl.{u} Z ℓ E).obj K)) ∧
    IsIso ((derivedPushHom.{u} (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ℓ E) f).app K) ∧
    constantModelBoundedConstructible.{u} (Profinite.continuousMapRingObj.{u} (PadicAlgCl ℓ)) Z
      ((algClTopologyScalarExtension.{u} ℓ Z).obj
        ((derivedExtendScalarsToPadicAlgCl.{u} Z ℓ E).obj K)) ∧
    DerivedCategory.finiteTorAmplitude _
      ((algClTopologyScalarExtension.{u} ℓ Z).obj
        ((derivedExtendScalarsToPadicAlgCl.{u} Z ℓ E).obj K)) ∧
    constantModelBoundedConstructible.{u} (Profinite.continuousMapRingObj.{u} (PadicAlgCl ℓ)) T
      ((algClTopologyScalarExtension.{u} ℓ T).obj
        ((moduleObjectDerivedPushforward.{u} (Profinite.padicAlgClRingObj.{u} ℓ) f).obj
          ((derivedExtendScalarsToPadicAlgCl.{u} Z ℓ E).obj K))) ∧
    constantModelBoundedConstructible.{u} (Profinite.continuousMapRingObj.{u} (PadicAlgCl ℓ)) T
      ((moduleObjectDerivedPushforward
        (Profinite.continuousMapRingObj.{u} (PadicAlgCl ℓ)) f).obj
          ((algClTopologyScalarExtension.{u} ℓ Z).obj
            ((derivedExtendScalarsToPadicAlgCl.{u} Z ℓ E).obj K))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
