/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Sheaf.Paper.ModuleObjectProjectionMap
public import Sheaf.Paper.CondensedAmbientExchange
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Sheaf.Paper.IntegralLocalizingProperBaseChange
import Sheaf.Paper.IntegralProperProjectionFormula
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage

/-!
# Integral open direct image and proper formulas

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-pf-adic/_section.md
(blueprint: sk-thm-sf-pf-adic).

The three statements use internal modules over the pulled-back condensed ring of integers.
The base change and projection conclusions include membership of both endpoints in the
localizing closure. Since this is a full subcategory, ambient invertibility then says exactly
that these maps are isomorphisms in that subcategory. No completed tensor is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false

-- Keep the coefficient inverse image opaque while elaborating derived endpoints.
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section OpenImage

variable {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [IsSeparated (U ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]

/-- Quasi-compact open direct image preserves bounded constructible finite-Tor objects.
Source: blueprint main-20261015, sk-thm-sf-pf-adic, first assertion
(blueprint: sk-thm-sf-pf-adic).

Proof: the standing finite-type separated hypotheses give qcqs by
lem-weil-pbc-qcqs-over-affine. Apply clause (2) of
 det-def-localizing-closure-ctf-equals-bc to identify Dctf with Dbc for O_E.
The coefficient sheaves are precisely the pulled-back condensed O_E sheaves required by
 det-thm-sf-pf-adic-open. Its final conclusion places Rj_*K in Dbc(X,O_E); the same
identification gives Dctf(X,O_E). That detail theorem proves derived completeness by
Stacks 099L, identifies residue reduction with the direct image of the reduction because
reduction is a cone, applies torsion open finiteness, then uses the residue criterion 09C1.
-/
theorem integralOpenDirectImage (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of k))]
    (K : ConstantModelConstructibleFiniteTor (Profinite.padicIntegersRingObj ℓ E.val) U) :
    constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X
        ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val) j).obj K.obj) ∧
      DerivedCategory.finiteTorAmplitude _
        ((moduleObjectDerivedPushforward
          (Profinite.padicIntegersRingObj ℓ E.val) j).obj K.obj) := by
  sorry

end OpenImage

section ProperFormulas

variable {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]

/-- Proper base change is an isomorphism inside the localizing closure of Dctf.
Source: blueprint main-20261015, sk-thm-sf-pf-adic, base change assertion
(blueprint: sk-thm-sf-pf-adic).

Proof: use lem-weil-pbc-qcqs-over-affine and clause (2) of
 det-def-localizing-closure-ctf-equals-bc to identify Dctf=Dbc and their localizing
closures. Apply det-thm-sf-pf-adic-base-change to the cartesian square and K. Its
functor codomain supplies membership of both endpoints in Loc(Dbc(Y',O_E)), and its
invertibility assertion concerns the same canonical unit/square/counit exchange arrow.
Transport those two memberships back to Loc(Dctf). Fullness identifies the ambient inverse
with an inverse in this subcategory. The identity square is included and gives preservation
of the localizing closure by proper direct image, as used in the projection proof below.
-/
theorem integralProperBaseChange {X' Y' : Scheme.{u}}
    [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
    [IsSeparated (X' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    [g.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare g' f' f g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)))
    (hK : localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E.val) X K) :
    localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E.val) Y'
        ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val) g).obj
          ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val) f).obj K)) ∧
      localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E.val) Y'
        ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val) f').obj
          ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val) g').obj K)) ∧
      IsIso ((condensedAmbientExchange
        (Profinite.padicIntegersRingObj ℓ E.val) sq).app K) := by
  sorry

/-- The proper projection formula is an isomorphism inside the localizing closure of Dctf.
Source: blueprint main-20261015, sk-thm-sf-pf-adic, projection assertion
(blueprint: sk-thm-sf-pf-adic).

Proof: identify Dctf=Dbc and their localizing closures as above. Clause (2) of
 det-thm-sf-pf-adic-projection gives tensor closure and ambient invertibility of precisely
the counit-defined projection map. The identity-square specialization of
 det-thm-sf-pf-adic-base-change puts Rf_*K in Loc(Dbc(Y,O_E)). Tensor closure then puts
its tensor with L in the same closure. Repleteness puts the target there, since the
projection map is invertible. Fullness supplies its inverse in that subcategory.
The detail projection theorem first proves the bounded case: both objects are derived
complete, reduction gives the torsion projection formula (0F0G), and the complete cone with
zero reduction vanishes by derived Nakayama (099I). Tensor closure and proper coproduct
continuity extend it in both variables to the localizing closure. All tensors are the
ordinary relative K-flat tensors in the ambient module-object derived categories.
-/
theorem integralProperProjection
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)))
    (L : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y)))
    (hK : localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E.val) X K)
    (hL : localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E.val) Y L) :
    localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E.val) Y
        (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) Y).obj
          ((moduleObjectDerivedPushforward
            (Profinite.padicIntegersRingObj ℓ E.val) f).obj K)).obj L) ∧
      localizingClosureProEtale (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val) f).obj
          (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) X).obj K).obj
            ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val) f).obj L))) ∧
      IsIso (moduleObjectProjectionMap (Profinite.padicIntegersRingObj ℓ E.val) f K L) := by
  sorry

end ProperFormulas

end AlgebraicGeometry.ProEtale.CondensedRing
