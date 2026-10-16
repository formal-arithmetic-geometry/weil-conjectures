/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2 -/
module

public import Sheaf.Paper.FiniteDiscreteCoefficientEncoding
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.LowerShriek.Defs

/-! # Finite presentations under the common coefficient encoding -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

/-- A constructible internal module has a constructible ordinary module sheaf
under the sectionwise finite-coefficient encoding.
Source: Bhatt--Scholze, Proposition 5.3.2 and Lemma 5.4.1
(blueprint: lem-weil-pbc-finite-discrete-constructible-encoding).

Proof in words. Take the finite stratification in the internal constructibility
hypothesis. The coefficient identification and sectionwise encoding commute with
restriction to each stratum and to every member of a pro-etale cover. On a member
where there is a finite presentation, use exactness of the encoding to turn it
into a cokernel of a map between finite sums of constant finite B-module sheaves.
The rank-one constant internal module becomes a constant module whose underlying
additive group is B, by hG. Each matrix entry is therefore locally constant with
values in a finite set of homomorphisms. Refine the covering simultaneously for
these finitely many entries. On every refined member the map is constant. Its
cokernel is the constant sheaf of the corresponding cokernel of finite B-modules.
This module is finite, being a quotient of a finite sum of finite modules. Refining
covers and composing them gives
a pro-etale cover on which the restriction to this stratum is constant with finite
stalks. Retain the original finite stratification. Empty strata and covers give
the empty case, and a zero cokernel gives the constant zero module, so neither
requires a nonzero-ring or positive-rank assumption. -/
theorem finiteDiscreteCoefficient_constructible [DiscreteTopology B] [Finite B]
    (T : Scheme.{u}) (M : FiniteDiscreteInternalModules B T)
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T) M) :
    ProEtale.IsConstructible (ULift.{u + 1} B)
      ((finiteDiscreteCoefficientEquivalence B eR G hG T).inverse.obj M) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
