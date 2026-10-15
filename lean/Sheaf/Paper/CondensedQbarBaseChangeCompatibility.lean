/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.Paper.CondensedQbarComparisons

import Sheaf.Paper.CondensedQbarExchangeEquality
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction

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

/-- Proper finite-to-Qbar coefficient change preserves the specified exchange arrow.
Source: TwoColimit.lean, final transport paragraph; ChangeOfCoefficients.lean, Derived section
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility).

Proof plan (the DAG's seven steps):
1. Choose an algebraic E-basis of Ω. Finite-dimensional coordinate homeomorphisms
(`lem-weil-pbc-finite-dimensional-linear-homeomorphism`) identify finite-field-valued sections
with finite sums of continuous E-valued coordinates. Finite covers preserve finite support,
so underline Ω is the sheaf direct sum of copies of underline E. The monoidal left adjoint
p_T^* preserves this identification (`lem-weil-pbc-profinite-point-pullback`).
2. Tensoring is thus a direct sum after restriction of scalars. Sheaf sums are exact, so
extension is exact, computed termwise, and preserves local finite presentations, strata and
bounded cohomology. Exact restriction preserves injectives and K-injectives by adjunction
(`lem-weil-pbc-module-sheaves-colimits-forgetful`, `lem-weil-pbc-sheafification-exact`).
3. Pullback comparisons identify the same simple tensors. Restriction commutes with derived
pushforward on K-injective resolutions. The specified push mate on a basis summand is R h_*
of the basis inclusion, by the adjunction bijection and the counit formula.
4. Properness of f and its base change f' gives qcqs. Bounded-below coproduct continuity
(`lem-weil-pbc-proetale-bounded-below-coproducts`) makes the push comparisons invertible;
faithful exact restriction detects this. Only uniformly bounded below copies are used.
5. Finite-E realization (`lem-weil-pbc-condensed-e-realization`) and exact scalar extension
preserve constructibility. Object descent (`prop-weil-pbc-qbar-condensed-two-colimit`) on
noetherian finite-type schemes gives the Ω restrictions. Therefore all factors of S and U
are isomorphisms.
6. Restriction identifies units and counits by their adjunction characterizations and the
square comparison by coherent inverse-image composition. Substitution in the three-factor
exchange formula identifies the specified Ω exchange with the E exchange after restriction.
7. On every basis summand, naturality of B_E at the basis inclusion gives the asserted
commutative diagram. The coproduct universal property and faithful restriction imply equality
of the two specified arrows. Neither exchange transformation is assumed invertible. -/
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
          (boundedConstructibleBaseChange (Profinite.padicAlgClRingObj ℓ) ℓ k
            sq.toCommSq).app ((constructibleToPadicAlgCl X ℓ E).obj K) =
        (constructibleToPadicAlgCl Y' ℓ E).map
            ((boundedConstructibleBaseChange (Profinite.continuousMapRingObj E) ℓ k
              sq.toCommSq).app K) ≫
          constructibleToQbarTargetHom ℓ k E f' g' K) := by
  let : IsIso (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f) :=
    inferInstance
  have : IsProper f' := by
    rw [← sq.hom_snd]
    infer_instance
  let : IsIso (derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f') :=
    inferInstance
  have hpush : ∀ K : PadicSubfieldConstructible X ℓ E,
      IsIso (constructibleToQbarPushHom ℓ k E f K) := by
    intro K
    apply (ObjectProperty.isIso_hom_iff _).mp
    dsimp [constructibleToQbarPushHom]
    exact inferInstance
  have hpush' : ∀ K : PadicSubfieldConstructible X' ℓ E,
      IsIso (constructibleToQbarPushHom ℓ k E f' K) := by
    intro K
    apply (ObjectProperty.isIso_hom_iff _).mp
    dsimp [constructibleToQbarPushHom]
    exact inferInstance
  refine ⟨hpush, hpush', ?_⟩
  intro K
  have := hpush K
  have : IsIso (constructibleToQbarPushHom ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g').obj K)) :=
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
