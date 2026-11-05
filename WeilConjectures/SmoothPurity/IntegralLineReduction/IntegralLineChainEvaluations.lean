/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionDefinitions
import all WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence

/-! # Chain cancellation for signed integral lines

Source: latest blueprint, Tate-twist local freeness, proof (3), final two sentences.
(blueprint: lem-pur-integral-line-chain-evaluations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u uC vC r
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralLineReduction
open IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

open MonoidalCategory
open Functor
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
attribute [local irreducible] completedIntegralCommRingSheafUnrestricted

section OrdinarySite

variable {D : Type uC} [Category.{vC} D] {J : GrothendieckTopology D}
  [EssentiallySmall.{max uC vC r} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
  [HasWeakSheafify J AddCommGrpCat.{max uC vC r}]
  (R : Sheaf J CommRingCat.{max uC vC r})

open SheafOfModules.LineEvaluation
set_option quotPrecheck false in
set_option hygiene false in
local notation "Mdl" => SheafOfModules.LineEvaluation.Modules.{uC, vC, r} R
set_option quotPrecheck false in
set_option hygiene false in
local notation "𝒪" => SheafOfModules.unit
  ((sheafCompose J
    (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R)

attribute [local irreducible] tensorSiteIso
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  SheafOfModules.LineEvaluation.cancellation Localization.Monoidal.tensorBifunctor

attribute [local irreducible] siteCancellation sitePairing

end OrdinarySite

attribute [local instance 3000] chainSiteSmall

attribute [local instance 3000] chainWeakSheafify

attribute [local instance 3000] chainLocallyBijective

attribute [local irreducible] tensorSiteIso sitePairing siteCancellation
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  SheafOfModules.LineEvaluation.cancellation Localization.Monoidal.tensorBifunctor

attribute [local irreducible] moduleCancellation

section OrdinarySiteTriangles

attribute [-instance] chainSiteSmall chainWeakSheafify chainLocallyBijective

variable {D : Type uC} [Category.{vC} D] {J : GrothendieckTopology D}
  [EssentiallySmall.{max uC vC r} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
  [HasWeakSheafify J AddCommGrpCat.{max uC vC r}]
  (R : Sheaf J CommRingCat.{max uC vC r})

open SheafOfModules.LineEvaluation
set_option quotPrecheck false in
set_option hygiene false in
local notation "Mdl" => SheafOfModules.LineEvaluation.Modules.{uC, vC, r} R
set_option quotPrecheck false in
set_option hygiene false in
local notation "𝒪" => SheafOfModules.unit
  ((sheafCompose J
    (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R)

end OrdinarySiteTriangles

attribute [local instance 3000] chainSiteSmall chainWeakSheafify chainLocallyBijective

attribute [local irreducible] sheafUnitUnitor

end WeilConjectures.IntegralLineReduction
