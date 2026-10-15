/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse
import Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts
import Sheaf.Paper.ProfinitePointPullback

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

section Edge

variable {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
  [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
  [IsSeparated (T ↘ Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]

/-- The canonical pullback comparison restricted to bounded constructible objects, in the
orientation `T_T l_{h,E} ≅ l_{h,Ω} T_U`. Source: ChangeOfCoefficients.lean, `derivedPullIso`;
TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarPullIso (K : PadicSubfieldConstructible U ℓ E) :
    (constructibleToPadicAlgCl T ℓ E).obj
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k h).obj K) ≅
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k h).obj
        ((constructibleToPadicAlgCl U ℓ E).obj K) :=
  ObjectProperty.isoMk _
    ((derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) h).app K.obj)

/-- The specified pushforward comparison restricted to bounded constructible objects.
Source: ChangeOfCoefficients.lean, `derivedPushHom`, the mate of restriction/pushforward;
TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarPushHom (K : PadicSubfieldConstructible T ℓ E) :
    (constructibleToPadicAlgCl U ℓ E).obj
        ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ k h).obj K) ⟶
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k h).obj
        ((constructibleToPadicAlgCl T ℓ E).obj K) :=
  ObjectProperty.homMk
    ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) h).app K.obj)

end Edge

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

/-- The specified source comparison `S_K`: first the pull comparison for `g`, then the
pullback of the push comparison for `f`. Source: TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarSourceHom (K : PadicSubfieldConstructible X ℓ E) :
    (constructibleToPadicAlgCl Y' ℓ E).obj
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g).obj
          ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ k f).obj K)) ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g).obj
        ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k f).obj
          ((constructibleToPadicAlgCl X ℓ E).obj K)) :=
  (constructibleToQbarPullIso ℓ k E g
      ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ k f).obj K)).hom ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g).map
      (constructibleToQbarPushHom ℓ k E f K)

/-- The specified target comparison `U_K`: first the push comparison for `f'`, then the
pushforward of the pull comparison for `g'`. Source: TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarTargetHom (K : PadicSubfieldConstructible X ℓ E) :
    (constructibleToPadicAlgCl Y' ℓ E).obj
        ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ k f').obj
          ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g').obj K)) ⟶
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k f').obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g').obj
          ((constructibleToPadicAlgCl X ℓ E).obj K)) :=
  constructibleToQbarPushHom ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g').obj K) ≫
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k f').map
      (constructibleToQbarPullIso ℓ k E g' K).hom

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
  sorry

end Square

end AlgebraicGeometry.ProEtale.CondensedRing
