/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.UnboundedLocalizingPullback
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.SixFunctors.ProperImageLocalizingProper

/-!
# Extending proper base change to the localizing closure

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-proper-base-change-unbounded/sk-prop-proper-base-change-unbounded-extension.md
(blueprint: det-proper-base-change-unbounded-extension).

The exchange is the existing canonical ambient mate, transported to the exact termwise
inverse images. The ambient category is ordinary and unbounded; the generators are bounded
constructible objects of finite Tor amplitude. All six coefficient cases are retained,
including the finite-subextension-valued algebraic-closure coefficient.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {X' X Y' Y : Scheme.{u}}
  {g' : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}

/-- The canonical ambient exchange expressed using exact termwise inverse images.
The comparison `Lu^* ≅ D(u^*)` is the canonical exact-functor comparison, and both
adjunctions are transported along it. Consequently the transported mate inserts the unit
for `p'`, applies the termwise square comparison built from `upperStarComp` and `sq.w`,
and contracts the counit for `p`, exactly as in the displayed formula of the source.
This is a change of presentation of `condensedAmbientExchange`, with no new choice of map.
Source: blueprint main-20261015, unbounded base-change extension, displayed beta
(blueprint: det-proper-base-change-unbounded-extension). -/
def termwiseCondensedAmbientExchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (sq : ChosenCartesianSquare g' p' p g) :
    (lowerStar Λ p).rightDerivedFunctor ⋙ (upperStar Λ g).mapDerivedCategory ⟶
      (upperStar Λ g').mapDerivedCategory ⋙ (lowerStar Λ p').rightDerivedFunctor :=
  (Functor.isoWhiskerLeft (lowerStar Λ p).rightDerivedFunctor
    (leftDerivedUpperStarIsoMapDerivedCategory Λ g).symm).hom ≫
    condensedAmbientExchange Λ sq ≫
    (Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ g')
      (lowerStar Λ p').rightDerivedFunctor).hom

/-- The extension implication for one coefficient ring: the specified base-change map
being invertible on every bounded constructible finite-Tor object implies its invertibility
on every object of their localizing closure. Both quantifiers range over the same ordinary
unbounded derived category of internal modules over the pulled-back condensed ring.
Source: blueprint main-20261015, unbounded base-change extension, final sentence
(blueprint: det-proper-base-change-unbounded-extension). -/
def UnboundedBaseChangeExtension
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (sq : ChosenCartesianSquare g' p' p g) : Prop :=
  (∀ K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    (constantModelBoundedConstructible Λ X K ∧ DerivedCategory.finiteTorAmplitude _ K) →
      IsIso ((termwiseCondensedAmbientExchange Λ sq).app K)) →
  ∀ K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    localizingClosureProEtale Λ X K →
      IsIso ((termwiseCondensedAmbientExchange Λ sq).app K)

/-- Proper base change extends from Dctf to its localizing closure, for every admissible
coefficient in the source's list. The last coefficient is specifically the ring of
continuous functions valued in some finite subextension, rather than all continuous
functions into the algebraic closure. Finite rings are represented in `Type 0`, which
includes a representative of every finite coefficient ring.
Source: blueprint main-20261015, unbounded base-change extension
(blueprint: det-proper-base-change-unbounded-extension).

Proof plan, following the five steps of the DAG node:
1. Properness of `p'` follows from properness under base change
   (lem-weil-pbc-proper-base-change). By det-proper-image-localizing-proper both proper
   pushforwards carry localizing closures to localizing closures and preserve ambient
   small sums. By det-proper-base-change-unbounded-pullback the two inverse images do so
   too. Hence both composites restrict to sum-preserving functors. Fullness identifies
   coproducts in these subcategories with the ambient coproducts (sk-def-localizing-closure).
2. Cartesian coefficients make inverse images exact (sk-prop-sfb-cartesian-coefficients).
   The exact-functor comparison of sk-def-sfb-derived-categories transports the adjunctions
   of sk-def-sfb-module-derived-pushpull to the termwise inverse images. Equip their right
   adjoints with the unique compatible coherent shifts
   (lem-weil-pbc-adjunction-shift-compatibility-unique); they are exact by
   lem-sf-triangulated-right-adjoint. Restrict and compose these exact functors using
   lem-weil-pbc-triangulated-functor-restriction and -composite. These auxiliary structures
   change neither the underlying functors nor the exchange map.
3. The comparison from def-sfb-module-upper-star-comp commutes with integer shifts
   degreewise: its degree-r component on a shifted complex is its component in degree
   r+n on the original complex. Additivity respects the shifted differential. Localization
   preserves this equality (def-weil-abstract-derived-category).
4. The unit and counit commute with the shifts of step 2. Whiskering and composition
   preserve compatibility (lem-weil-pbc-commshift-nattrans-comp-whisker), so the specified
   exchange restricts to a shift-compatible natural transformation of the two exact
   sum-preserving functors on the full localizing subcategories.
5. Apply sk-lem-sf-determination. Its generator hypothesis is exactly the antecedent of
   UnboundedBaseChangeExtension, and its conclusion is the desired assertion on the closure.
-/
theorem unboundedBaseChangeExtension
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
    [IsSeparated (X' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    [p.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [p'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]
    [IsProper p] (sq : ChosenCartesianSquare g' p' p g) :
    (∀ (A : Type) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A],
      (∃ n : ℕ, (ℓ ^ n : A) = 0) →
        UnboundedBaseChangeExtension (Profinite.continuousMapRingObj A) sq) ∧
    UnboundedBaseChangeExtension (Profinite.continuousMapRingObj ℤ_[ℓ]) sq ∧
    UnboundedBaseChangeExtension (Profinite.continuousMapRingObj ℚ_[ℓ]) sq ∧
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      UnboundedBaseChangeExtension (Profinite.padicIntegersRingObj ℓ E) sq ∧
      UnboundedBaseChangeExtension (Profinite.continuousMapRingObj E) sq) ∧
    UnboundedBaseChangeExtension (Profinite.padicAlgClRingObj ℓ) sq := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
