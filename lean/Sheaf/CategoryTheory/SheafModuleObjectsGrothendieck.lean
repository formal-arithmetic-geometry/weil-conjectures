/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Sheaf.CategoryTheory.AbelianSheafTensorInstances
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian

/-! # Grothendieck categories of internal modules over arbitrary sheaf rings

Source: Weil conjectures blueprint, `sec-proetale-coefficients`,
`sk-prop-sf-open-closed-triangle/lem-sfb-modobj-grothendieck` and its proof
(blueprint: lem-sfb-sheaf-modobj-grothendieck-any-ring).

The canonical sheaf tensor and its instance interfaces are the existing ones from
`sk-def-sfb-sheaf-tensor` and `def-sfb-abelian-sheaf-tensor-instances`.
The coefficient ring object is not assumed commutative.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Mod

/-- Abelian sheaves and internal left modules over any ring object are Grothendieck
abelian, and the forgetful functor is faithful and preserves finite limits, finite
colimits and small filtered colimits.

Source: blueprint `sec-proetale-coefficients`,
`sk-prop-sf-open-closed-triangle/lem-sfb-modobj-grothendieck` and its proof
(blueprint: lem-sfb-sheaf-modobj-grothendieck-any-ring).

Proof, following the node:
1. Replace the essentially small site by its small model in the coefficient universe.
Abelian-group sheaves are Grothendieck abelian by
`lem-sfb-sheaves-grothendieck-with-sheafification`. The specified sheaf tensor is closed
by `sk-def-sfb-sheaf-tensor`, so each fixed-factor tensor preserves small colimits.
Preserving zero and binary coproducts preserves the diagonal--biproduct--codiagonal
formula for addition, so tensor is additive in both variables.
2. Apply `lem-sfb-modobj-abelian`: left tensor with R preserves finite colimits,
so its internal left modules are abelian, without commutativity.
3. The forgetful functor is faithful by `lem-sfb-modobj-forget-faithful`.
By `lem-sfb-modobj-forget-creates`, underlying limits acquire unique module actions,
and underlying colimits do too because left tensor preserves colimits. Consequently
forgetting preserves finite limits, finite colimits and small filtered colimits.
4. An inverse to an invertible underlying module map is linear: compose the action
identity with the inverse and its left tensor by R. Thus forgetting reflects
isomorphisms and preserves zero maps. Apply `lem-weil-pbc-jointly-reflect-short-exact`
to this singleton functor: short exactness is detected underneath. Filtered colimits
of short exact sequences are therefore exact, since they are exact in abelian sheaves.
5. If G is a generator of abelian sheaves, `lem-sfb-free-internal-module-adjunction`
gives Hom_R(R tensor G,M) = Hom(G,U M), naturally in M. Faithfulness of U and the
generator property of G distinguish any two module morphisms after precomposition
from the free module R tensor G. This is a generator. Abelianness, small colimits,
exact filtered colimits and this generator give Grothendieckness by
`def-sp-grothendieck-abelian`.
-/
theorem sheafModuleObjects_grothendieck_any_ring
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    (R : Sheaf J AddCommGrpCat.{w}) [MonObj R] :
    IsGrothendieckAbelian.{w} (Sheaf J AddCommGrpCat.{w}) ∧
      IsGrothendieckAbelian.{w} (Mod (Sheaf J AddCommGrpCat.{w}) R) ∧
      (forget (D := Sheaf J AddCommGrpCat.{w}) R).Faithful ∧
      PreservesFiniteLimits (forget (D := Sheaf J AddCommGrpCat.{w}) R) ∧
      PreservesFiniteColimits (forget (D := Sheaf J AddCommGrpCat.{w}) R) ∧
      PreservesFilteredColimitsOfSize.{w, w}
        (forget (D := Sheaf J AddCommGrpCat.{w}) R) := by
  have : IsGrothendieckAbelian.{w} (Sheaf J AddCommGrpCat.{w}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall J AddCommGrpCat.{w}
  have hTensor : ∀ F : Sheaf J AddCommGrpCat.{w},
      PreservesColimitsOfSize.{w, w} (MonoidalCategory.tensorLeft F) := fun F ↦
    ((sfbSheafTensor_properties.{uC, vC, w + 1, w, w, w}
      (A := AddCommGrpCat.{w}) J).2.2 F).1
  have : PreservesColimitsOfSize.{w, w} (MonoidalCategory.tensorLeft R) := hTensor R
  have : HasColimitsOfSize.{w, w} (Sheaf J AddCommGrpCat.{w}) :=
    IsGrothendieckAbelian.hasColimits _
  have : PreservesColimitsOfSize.{w, w}
      (forget (D := Sheaf J AddCommGrpCat.{w}) R) :=
    preservesColimits_of_createsColimits_and_hasColimits _
  exact ⟨inferInstance, isGrothendieckAbelian R, inferInstance,
    inferInstance, inferInstance, inferInstance⟩

end CategoryTheory.Mod
