/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.NatIso
public import WeilConjectures.CategoryTheory.CommonStage.CoherentPairFunctorDescent
public import WeilConjectures.CategoryTheory.StageSystem.Basic
import WeilConjectures.CategoryTheory.StageSystem.Functor

/-! # Coherent functor descent on the existing StageSystem quotient

Source: sketch32 common-stage calculus, lines 1291--1338 and 1419--1426;
sketch42 pseudocone and pair universal properties
(blueprint: lem-sbc-coherent-pair-functor-descent).

## Main definitions

* `StageSystem.pairFunctorCoherent`: the specified tower equation.
* `StageSystem.coefficientPairFunctor`: descent on the actual upstream quotient.

The imported original interface retains additive structures, compatible natural
transformations and outer Karoubi extension. This interface transports its functor
construction to the independently existing `StageSystem.PairCategory` carrier.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w u v u' v'

namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)]
  (S : StageSystem C) (T : StageSystem D)
  (φ : ∀ i, C i ⥤ D i)
  (b : ∀ {i j} (h : i ≤ j), φ i ⋙ T.T h ≅ S.T h ⋙ φ j)

/-- Coherent-pair descent, with uniquely determined object and arrow formulas.
Source: sketch32, lines 1291--1338 and 1419--1426
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
@[irreducible] def coefficientPairFunctor (hb : pairFunctorCoherent S T φ b) :=
  ((coefficientPairFunctor_exists S T φ b hb).exists.choose).copyObj
    (coefficientPairFunctorObject S T φ)
    (fun P ↦ eqToIso ((coefficientPairFunctor_exists S T φ b hb).exists.choose_spec.1 P))

end CategoryTheory.StageSystem
