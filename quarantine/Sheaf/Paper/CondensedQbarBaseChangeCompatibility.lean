/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.OverSquare

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.Paper.CondensedQbarComparisons

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Sheaf.Paper.CondensedQbarExchangeEquality
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-!
# Condensed finite-to-algebraic-closure coefficient change and exchange

Source: upstream `ModuleObject/Colimit/TwoColimit.lean`, final transport paragraph;
`ModuleObject/ChangeOfCoefficients.lean`, Derived section
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility).

The coefficient ring is the finite-subextension-valued continuous-function ring
`Profinite.padicAlgClRingObj`, not the full continuous-function ring. All categories below
are the published bounded constructible full subcategories, without a completeness condition.
The pull and push comparisons are restrictions of the specified ambient comparisons.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- Keep the ambient mate folded while restricting its component to the full subcategory.
attribute [local irreducible] derivedPushHom

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))

section Square

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- Restriction of the bounded-below comparison to a bounded constructible input. -/
private theorem constructibleToQbarPushHom_isIso_of_isProper [IsProper f]
    (K : PadicSubfieldConstructible X ℓ E) :
    IsIso (constructibleToQbarPushHom ℓ k E f K) := by
  obtain ⟨N, hN⟩ := K.property.1.1
  have : K.obj.IsGE N := hN
  exact (ObjectProperty.isIso_hom_iff
    (P := boundedConstructible (padicAlgClRingObj Y ℓ))
    (constructibleToQbarPushHom ℓ k E f K)).mp
    (isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE.{u}
      ℓ f E K.obj N)

/-- Proper finite-to-Qbar coefficient change preserves the specified exchange arrow.
Source: TwoColimit.lean, final transport paragraph; ChangeOfCoefficients.lean, Derived section
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility).

Proof: the chosen pullback makes f' proper. Extract a cohomological lower bound from
each bounded constructible input and apply
`isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE`. That theorem combines
the scalar-basis decomposition with copower continuity in these same internal condensed
module categories (`lem-weil-pbc-condensed-subfield-bounded-copowers`). Transfer each
component through `ObjectProperty.isIso_hom_iff` to the constructible full subcategory.
The source and target comparisons are composites of these push isomorphisms with the
published pull isomorphisms, so both are invertible. Finally apply the separately stated
`constructibleToQbar_exchange_equality` to the specified square and input; it identifies
exactly the displayed arrows without assuming either exchange transformation invertible. -/
theorem constructibleToQbar_baseChange_compatibility [IsProper f]
    (sq : ChosenCartesianSquare g' f' f g) :
    (∀ K : PadicSubfieldConstructible X ℓ E,
      IsIso (constructibleToQbarPushHom ℓ k E f K)) ∧
    (∀ K : PadicSubfieldConstructible X' ℓ E,
      IsIso (constructibleToQbarPushHom ℓ k E f' K)) ∧
    (∀ K : PadicSubfieldConstructible X ℓ E,
      IsIso (constructibleToQbarSourceHom ℓ k E f g K) ∧
      IsIso (constructibleToQbarTargetHom ℓ k E f' g' K) ∧
      constructibleToQbarSourceHom ℓ k E f g K ≫
          (boundedConstructibleBaseChange (Profinite.padicAlgClRingObj ℓ) ℓ (sq.toCommSq.asOver (Spec (.of k)))).app ((constructibleToPadicAlgCl X ℓ E).obj K) =
        (constructibleToPadicAlgCl Y' ℓ E).map
            ((boundedConstructibleBaseChange (Profinite.continuousMapRingObj E) ℓ (sq.toCommSq.asOver (Spec (.of k)))).app K) ≫
          constructibleToQbarTargetHom ℓ k E f' g' K) := by
  have : IsProper f' := by
    rw [← sq.hom_snd]
    infer_instance
  have hpush : ∀ K : PadicSubfieldConstructible X ℓ E,
      IsIso (constructibleToQbarPushHom ℓ k E f K) :=
    constructibleToQbarPushHom_isIso_of_isProper ℓ k E f
  have hpush' : ∀ K : PadicSubfieldConstructible X' ℓ E,
      IsIso (constructibleToQbarPushHom ℓ k E f' K) :=
    constructibleToQbarPushHom_isIso_of_isProper ℓ k E f'
  refine ⟨hpush, hpush', ?_⟩
  intro K
  have := hpush K
  have : IsIso (constructibleToQbarPushHom ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of k)))).obj K)) :=
    hpush' _
  constructor
  · dsimp [constructibleToQbarSourceHom]
    infer_instance
  constructor
  · dsimp [constructibleToQbarTargetHom]
    infer_instance
  · exact constructibleToQbar_exchange_equality ℓ k E f g f' g' sq.toCommSq K

end Square

end AlgebraicGeometry.ProEtale.CondensedRing
