/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import WeilConjectures.TraceFormula.Statement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
import Sheaf.AlgebraicGeometry.SchemeFrobeniusFiniteRadicial
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import Sheaf.Paper.BoundedConstructiblePushforwardRestriction

/-!
# The model compact-support comparison and the proper unit

Source: `WeilConjectures/TraceFormula/Statement.lean`,
`compactCohomologyFrobeniusComparison`, `weilCompactCohomology`, and
`WeilBoundedConstructibleOfEnd.globalOperator`; blueprint `sec-zeta-weil`,
`sk-thm-rationality` (blueprint: lem-zl-model-compact-comparison-unit).

All functors below are the actual bounded constructible internal-module functors over
`Profinite.padicAlgClRingObj ℓ`. The proper comparison and composition isomorphisms are
those of the chosen-compactification construction, including its independence comparisons.
The helpers only name the arrows occurring in the statement; their data are explicit.
This file records the stage-2 statement interface for the model compact-support comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The proper-unit natural transformation on compact supports, with factors in the order
unit, inverse proper comparison, inverse composition comparison, and `h ≫ a_X = a_X`.
Source: `TraceFormula/Statement.lean`, the four final factors of
`compactCohomologyFrobeniusComparison`
(blueprint: lem-zl-model-compact-comparison-unit). -/
noncomputable def compactSupportProperUnit (h : X ⟶ X) [IsProper h.left] :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight
      (boundedConstructibleUpperStarLowerStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ h).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (Functor.whiskerRight
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ h).inv _ ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ h (toPoint X)).inv ≫
        (eqToIso (congrArg
          (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ)
          (comp_toPoint h))).hom)

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] [algClosure : IsAlgClosure k₀ k]
  {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)}
  [LocallyOfFiniteType f₀] [qcModel : QuasiCompact f₀] [sepModel : IsSeparated f₀]
  {π : X.left ⟶ X₀} {Φ : X ⟶ X}

/-- The proper unit for the actual `r`-th model-Frobenius iterate. Finiteness is supplied
by the published model-Frobenius theorem, rather than imposed as an extra hypothesis.
Source: `TraceFormula/Statement.lean`, `IsModelFrobenius.isFinite` and the proper-unit
recipe (blueprint: lem-zl-model-compact-comparison-unit). -/
noncomputable def modelCompactProperUnit (hΦ : IsModelFrobenius Φ f₀ π) (r : ℕ) :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (frobeniusIterate Φ r) ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) :=
  letI := hΦ.isFinite r
  compactSupportProperUnit ℓ (frobeniusIterate Φ r)

/-- The specified model comparison with the canonical identity pullback on `Spec k`
removed by precomposition with its inverse, including the right unitor.
Source: `TraceFormula/Statement.lean`, `compactCohomologyFrobeniusComparison`
(blueprint: lem-zl-model-compact-comparison-unit). -/
noncomputable def modelCompactComparisonWithoutIdentity
    (hΦ : IsModelFrobenius Φ f₀ π) (r : ℕ) :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (frobeniusIterate Φ r) ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) :=
  letI := hΦ.isFinite r
  letI := hΦ.isUniversalHomeomorphism r
  (Functor.isoWhiskerLeft _
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)) ≪≫
    Functor.rightUnitor _).inv ≫
      (compactCohomologyFrobeniusComparison ℓ (frobeniusIterate Φ r)).hom

/-- The actual `globalOperator` of an arbitrary Weil object for the `r`-th model iterate,
viewed as its first iterate. Only finiteness and universal homeomorphism instances are
installed; the operator is the published implementation, with its carrier casts.
Source: `TraceFormula/Statement.lean`, `WeilBoundedConstructibleOfEnd.globalOperator`
(blueprint: lem-zl-model-compact-comparison-unit). -/
noncomputable def modelCompactGlobalOperator (hΦ : IsModelFrobenius Φ f₀ π) (r : ℕ)
    (K : WeilBoundedConstructibleOfEnd ℓ (frobeniusIterate Φ r)) :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier ⟶
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier :=
  letI : IsFinite (frobeniusIterate (frobeniusIterate Φ r) 1).left :=
    (frobeniusIterate_one (frobeniusIterate Φ r)) ▸ hΦ.isFinite r
  letI : IsUniversalHomeomorphism (frobeniusIterate (frobeniusIterate Φ r) 1).left :=
    (frobeniusIterate_one (frobeniusIterate Φ r)) ▸ hΦ.isUniversalHomeomorphism r
  K.globalOperator 1

include algClosure qcModel sepModel in
/-- The specified comparison is the proper-unit map, naturally in the coefficient complex,
and the actual global operator is this unit followed by compact pushforward of the Weil map.
Source: `TraceFormula/Statement.lean`, `compactCohomologyFrobeniusComparison`,
`weilCompactCohomology`, and `WeilBoundedConstructibleOfEnd.globalOperator`
(blueprint: lem-zl-model-compact-comparison-unit).

Proof:
1. Use the actual module-object categories and the restricted pullback/direct-image
adjunction of `sk-def-sfb-dc-restricted-functors`. The functor P is the chosen-compactification
lower shriek of `sk-def-sfb-dc-lower-shriek`. `compactSupportProperUnit` names precisely
P applied to the unit, the inverse proper comparison, inverse composition, and equality map.
2. Model Frobenius is finite by `lem-trf-scheme-frobenius-finite-radicial`; induct on the
positive iterate using `lem-weil-pbc-finite-composition`, then use
`lem-weil-pbc-finite-proper`. All iterates are over the base, giving `comp_toPoint`.
3. Expand the specified implementation named by `nt-assume-trace-formula`. Its first
factor is the canonical identity pullback, with unitors. Cancel it against its inverse
in `modelCompactComparisonWithoutIdentity`. The remaining four factors are precisely
`modelCompactProperUnit`, in the same order and with the same compactifications.
4. Compose the naturality squares of the unit, proper comparison, composition, and
equality comparison to obtain the displayed naturality identity. Finally unfold
`weilCompactCohomology` as `IsoAlgebra.mapOfNatIso`: its structure arrow is the comparison
followed by P of the Weil structure. Remove the same identity pullback in `frobenius`
and cancel the carrier casts in `globalOperator`. For an arbitrary Weil object for h,
its first iterated structure is the original structure by pullback identity coherence.
This yields the last equality. No trace, duality, Galois action, or adic comparison is used.
-/
theorem modelCompactComparison_eq_properUnit
    (hΦ : IsModelFrobenius Φ f₀ π) (r : ℕ) (hr : 1 ≤ r) :
    modelCompactComparisonWithoutIdentity ℓ hΦ r = modelCompactProperUnit ℓ hΦ r ∧
      (∀ (M N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (v : M ⟶ N),
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map v ≫
            (modelCompactProperUnit ℓ hΦ r).app N =
          (modelCompactProperUnit ℓ hΦ r).app M ≫
            (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
                (frobeniusIterate Φ r)).map v)) ∧
      (∀ K : WeilBoundedConstructibleOfEnd ℓ (frobeniusIterate Φ r),
        modelCompactGlobalOperator ℓ hΦ r K =
          (modelCompactProperUnit ℓ hΦ r).app K.carrier ≫
            (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
              K.str.hom) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
