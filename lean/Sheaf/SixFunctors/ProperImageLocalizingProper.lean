/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q91
-/
module

public import Sheaf.Paper.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.Paper.AmbientIndDerivedSums
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Paper.FiniteProperLocalizing
import Sheaf.Paper.IntegralProperBaseChange
import Sheaf.Paper.IntegralProperDirectSums
import Sheaf.Paper.LocalizingAdmissibleCoefficients
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.Paper.ProperBaseChangeRational
import Sheaf.Paper.ProperUnboundedCoproducts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Proper direct image on localizing categories

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-proper-image-localizing/sk-prop-proper-image-localizing-proper.md and its proof
(blueprint: det-proper-image-localizing-proper).

The coefficient list uses bundled ring objects, so membership identifies both the
underlying condensed abelian sheaf and its multiplication. The two auxiliary predicates
spell out the hypotheses and conclusion of this node, using the recorded ambient
module-object derived category and localizing closure. Coproduct indices have universe
`u + 2`, exactly the indexing universe in the recorded closure of this ambient category.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The two hypotheses in the proper localizing-image statement: preservation of
bounded constructible finite-Tor objects and of ambient sums of localizing objects.
Source: blueprint det-proper-image-localizing-proper, first paragraph
(blueprint: det-proper-image-localizing-proper). -/
def ProperLocalizingHypotheses
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y) : Prop :=
  (∀ K : ConstantModelConstructibleFiniteTor Λ X,
    (constantModelBoundedConstructible Λ Y ⊓ fun L ↦
      DerivedCategory.finiteTorAmplitude _ L)
        ((lowerStar Λ p).rightDerivedFunctor.obj K.obj)) ∧
  ∀ (I : Type (u + 2)) (F : Discrete I ⥤ (localizingClosureProEtale Λ X).FullSubcategory),
    PreservesColimit (F ⋙ (localizingClosureProEtale Λ X).ι)
      (lowerStar Λ p).rightDerivedFunctor

/-- The canonical restriction of the total derived pushforward is triangulated
and preserves every small coproduct. The subcategory structures are the induced
ones from the ambient derived categories, and the functor is the standard lift of
inclusion followed by the total derived pushforward, with its induced shift structure.
Source: blueprint det-proper-image-localizing-proper, first paragraph
(blueprint: det-proper-image-localizing-proper). -/
def ProperLocalizingRestriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y) : Prop :=
  ObjectProperty.IsTriangulated (localizingClosureProEtale Λ X) ∧
  ObjectProperty.IsTriangulated (localizingClosureProEtale Λ Y) ∧
  ∀ [ObjectProperty.IsTriangulated (localizingClosureProEtale Λ X)]
    [ObjectProperty.IsTriangulated (localizingClosureProEtale Λ Y)],
  ∃ h : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
      localizingClosureProEtale Λ Y ((lowerStar Λ p).rightDerivedFunctor.obj K.obj),
    (ObjectProperty.lift (localizingClosureProEtale Λ Y)
      ((localizingClosureProEtale Λ X).ι ⋙ (lowerStar Λ p).rightDerivedFunctor)
      h).IsTriangulated ∧
    ∀ I : Type (u + 2), PreservesColimitsOfShape (Discrete I)
      (ObjectProperty.lift (localizingClosureProEtale Λ Y)
        ((localizingClosureProEtale Λ X).ι ⋙ (lowerStar Λ p).rightDerivedFunctor) h)

/-- Proper direct image restricts to an exact, sum-preserving functor on the
localizing categories, provided it preserves the generators and ambient sums of
localizing objects. The coefficient list is exactly the admissible list, with the
finite ring discrete, finite subfield E, and finite-subextension condensed Qbar.

Source: blueprint det-proper-image-localizing-proper, first paragraph and first
proof paragraph (blueprint: det-proper-image-localizing-proper).

Proof: lowerStar is additive, so its total right derived functor is triangulated
(lem-pc-right-derived-functor-triangulated). Inside the source localizing closure,
take the objects whose image belongs to the target localizing closure. Exactness
makes this subcategory replete and triangulated. The first hypothesis puts all
Dctf generators in it. For a family in it, the second hypothesis identifies the
image of its ambient sum with the sum of its images, so this subcategory is
closed under sums. Minimality of sk-def-localizing-closure makes it the entire
source closure. ObjectProperty.isTriangulated_lift gives exactness of the lift
(lem-weil-pbc-triangulated-functor-restriction). Fullness and closure under sums
identify subcategory coproducts with ambient coproducts, giving preservation of
sums by that same lift. Only sums of localizing objects were used. -/
theorem proper_image_localizing_proper
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (_hA : ∃ n : ℕ, (ℓ ^ n : A) = 0)
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) [IsCommMonObj Λ.X]
    (_hΛ : Λ ∈ [Mon.mk (Profinite.continuousMapRingObj A),
      Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ]),
      Mon.mk (Profinite.padicIntegersRingObj ℓ E.val),
      Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ]),
      Mon.mk (Profinite.continuousMapRingObj E), Mon.mk (Profinite.padicAlgClRingObj ℓ)])
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p] :
    ProperLocalizingHypotheses Λ.X p → ProperLocalizingRestriction Λ.X p := by
  sorry

/-- In the standing separated finite-type positive-characteristic field setting,
both hypotheses of proper_image_localizing_proper hold for every admissible coefficient.
The list includes Q_ell and Z_ell explicitly, as the E = Q_ell specializations.

Source: blueprint det-proper-image-localizing-proper, coefficient assertions and
second proof paragraph (blueprint: det-proper-image-localizing-proper).

Proof: for E and Qbar, the schemes are qcqs by lem-weil-pbc-qcqs-over-affine.
By det-def-localizing-closure-ctf-equals-bc, Dctf equals Dbc, and the rational
proper base-change theorem det-thm-sfb-proper-base-change-rational preserves Dbc.
By det-ambient-ind-derived-sums their localizing closure lies in Dic;
sk-lem-proper-unbounded-window-ii therefore supplies exactly the required sums.
For finite A, det-ctf-finite-proper-localizing gives preservation of Dctf and
an exact sum-preserving restriction; its sums are ambient by fullness and sum
closure. No identification Dctf = Dbc for arbitrary finite A is used.
For O_E, qcqs again gives Dctf = Dbc; det-thm-sfb-proper-base-change-integral
preserves Dbc. Properness and quasi-compactness of the target give a uniform
fibre-dimension bound by lem-fin-finite-type-fibre-dimension-bound, and
det-prop-int-compactness-direct-sums gives preservation of sums on that closure.
Taking E = Q_ell yields the Q_ell and Z_ell cases. -/
theorem proper_image_localizing_proper_coefficients
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (A : Type) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (_hA : ∃ n : ℕ, (ℓ ^ n : A) = 0)
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) [IsCommMonObj Λ.X]
    (_hΛ : Λ ∈ [Mon.mk (Profinite.continuousMapRingObj A),
      Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ]),
      Mon.mk (Profinite.padicIntegersRingObj ℓ E.val),
      Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ]),
      Mon.mk (Profinite.continuousMapRingObj E), Mon.mk (Profinite.padicAlgClRingObj ℓ)])
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] :
    ProperLocalizingHypotheses Λ.X p := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
