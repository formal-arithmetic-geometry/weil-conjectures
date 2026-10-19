/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q101
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Sheaf.Paper.FiniteCoefficientDescentTwoColimit

/-!
# Rational open direct images with finite constant local models

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-open-coefficients,
integral and rational paragraphs
(blueprint: lem-sfb-rational-open-direct-image-constructible).

The two conjuncts are the finite-subextension and algebraic-closure coefficient cases.
Both use the finite-constant-model predicate, rather than general local finite presentation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Rational derived direct image along a quasi-compact open immersion preserves bounded
constructibility with finite constant scalar models, for both rational coefficient rings.
Source: blueprint sk-prop-open-coefficients, rational paragraph
(blueprint: lem-sfb-rational-open-direct-image-constructible).

Proof:
1. Clause (4) of [sk-thm-sfb-qlbar-two-colimit], applied to U and X, identifies
   finite-constant-model bounded constructibility with ring-object bounded constructibility
   for both E and the algebraic closure. Its positive-characteristic hypothesis follows from
   primality of ringChar k, and the distinct-prime hypothesis is part of the standing setting.
2. Regard j as a morphism over Spec k. For E, convert the input by the equality on U, apply
   [lem-sfb-dc-lower-star-preserves] with the continuous E coefficient ring, and convert the
   output by the equality on X. The underlying morphism and derived direct image remain j
   and its ordinary right derived module direct image.
3. Apply the same argument to the algebraic-closure coefficient ring and pair the results.
   Both rings have the finiteness-coefficient instances required by the direct-image theorem.
   The geometric instances on the bundled over-objects are exactly the given instances.
-/
theorem constantModelBoundedConstructible_rational_open_direct_image
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j] :
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) U)),
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) U K →
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X
        (((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) j).rightDerivedFunctor).obj
          K)) ∧
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U)),
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) U K →
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X
        (((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) j).rightDerivedFunctor).obj
          K)) := by
  let f := j.asOver (Spec (.of k))
  let : LocallyOfFiniteType (U.asOver (Spec (.of k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (U ↘ Spec (.of k)))
  let : QuasiCompact (U.asOver (Spec (.of k))).hom :=
    inferInstanceAs (QuasiCompact (U ↘ Spec (.of k)))
  let : IsSeparated (U.asOver (Spec (.of k))).hom :=
    inferInstanceAs (IsSeparated (U ↘ Spec (.of k)))
  let : LocallyOfFiniteType (X.asOver (Spec (.of k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of k)))
  let : QuasiCompact (X.asOver (Spec (.of k))).hom :=
    inferInstanceAs (QuasiCompact (X ↘ Spec (.of k)))
  let : IsSeparated (X.asOver (Spec (.of k))).hom :=
    inferInstanceAs (IsSeparated (X ↘ Spec (.of k)))
  have hU := (finiteCoefficientDescentTwoColimit k (ringChar k) ℓ
    (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ) U).2.2.2
  have hX := (finiteCoefficientDescentTwoColimit k (ringChar k) ℓ
    (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ) X).2.2.2
  let : CondensedRing.IsFinitenessCoefficient ℓ (Profinite.continuousMapRingObj E) :=
    .continuous E
  let : CondensedRing.IsFinitenessCoefficient ℓ (Profinite.padicAlgClRingObj ℓ) :=
    .algebraicClosure
  constructor
  · intro K hK
    rw [(hU.1 E).1] at hK
    rw [(hX.1 E).1]
    exact CondensedRing.boundedConstructible_rightDerivedLowerStar_obj
      (Profinite.continuousMapRingObj E) ℓ (k := k) f K hK
  · intro K hK
    rw [hU.2.1.1] at hK
    rw [hX.2.1.1]
    exact CondensedRing.boundedConstructible_rightDerivedLowerStar_obj
      (Profinite.padicAlgClRingObj ℓ) ℓ (k := k) f K hK

end AlgebraicGeometry.ProEtale
