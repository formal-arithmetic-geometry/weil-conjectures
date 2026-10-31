/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystemCommonStageCones

/-! # Supplied exact and shift data for a directed pair category

Source: blueprint filtered two-colimit pair model, with the unnormalized stage system of
`WeilConjectures.CategoryTheory.StageSystem.Basic` and the supplied structures of
`WeilConjectures.CategoryTheory.StageSystemVerdier`
(blueprint: def-sf-directed-common-stage-data).

The pair construction, inclusions, canonical identifications, triangle images and common-stage
predicate are reused, respectively, as `StageSystem.PairCategory`, `StageSystem.ι`,
`StageSystem.transIso`, `StageSystem.isoToStage`, `Functor.mapTriangle` and
`StageSystem.CommonStageDistinguished`. Only their supplied exact/shift data are packaged here.
-/

@[expose] public section
set_option autoImplicit false

universe w v u

open CategoryTheory.Limits

namespace CategoryTheory.StageSystem

/-- An exact-stage pair datum over a nonempty directed preorder. The field `system` uses the
unnormalized pair construction: its associators satisfy the cocycle, but it has no unitors.
The stage pretriangulations and the pair category's additive, zero and shift structures are
supplied data. The inclusion and transition comparisons include shift-zero and shift-add
coherence via `Functor.CommShift`; `identificationCommShift` is exactly compatibility of the
canonical `transIso` with these comparisons. No pretriangulation of the pair category is stored.
For these data the image of a stage triangle is `(system.ι i).mapTriangle.obj U`, and the
common-stage predicate is `system.CommonStageDistinguished`, which asserts that a triangle is
isomorphic to such an image of a distinguished stage triangle.
Source: blueprint filtered two-colimit pair model; `StageSystem.Basic` (pair construction),
`StageSystemVerdier` (supplied exact/shift hypotheses), and `StageSystemCommonStageCones`
(common-stage predicate) (blueprint: def-sf-directed-common-stage-data). -/
structure ExactStagePairData {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (C : I → Type u) [∀ i : I, Category.{v} (C i)] where
  /-- The transition functors and their coherent associators, without specified unitors. -/
  system : StageSystem C
  /-- The preadditive structures at the stages. -/
  [stagePreadditive : ∀ i : I, Preadditive (C i)]
  /-- The stage zero objects. -/
  [stageZero : ∀ i : I, HasZeroObject (C i)]
  /-- The stage integer shifts. -/
  [stageShift : ∀ i : I, HasShift (C i) ℤ]
  /-- Additivity of every stage shift. -/
  [stageShiftAdditive : ∀ (i : I) (n : ℤ), (shiftFunctor (C i) n).Additive]
  /-- The stage pretriangulations (TR1--TR3 only). -/
  [stagePretriangulated : ∀ i : I, Pretriangulated (C i)]
  /-- The fixed preadditive structure on the pair category. -/
  [pairPreadditive : Preadditive system.PairCategory]
  /-- The fixed zero object on the pair category. -/
  [pairZero : HasZeroObject system.PairCategory]
  /-- The fixed integer shifts on the pair category. -/
  [pairShift : HasShift system.PairCategory ℤ]
  /-- Additivity of every pair-category shift. -/
  [pairShiftAdditive : ∀ n : ℤ, (shiftFunctor system.PairCategory n).Additive]
  /-- Additivity of each stage inclusion. -/
  [inclusionAdditive : ∀ i : I, (system.ι i).Additive]
  /-- The coherent comparisons beta between inclusion and all integer shifts. -/
  [inclusionCommShift : ∀ i : I, (system.ι i).CommShift ℤ]
  /-- The coherent comparisons sigma between transition and all integer shifts. -/
  [transitionCommShift : ∀ (i j : I) (h : i ≤ j), (system.T h).CommShift ℤ]
  /-- Exactness of the transition functors with their supplied comparisons. -/
  [transitionExact : ∀ (i j : I) (h : i ≤ j), (system.T h).IsTriangulated]
  /-- The canonical identifications theta commute with the supplied shift comparisons. -/
  [identificationCommShift : ∀ (i j : I) (h : i ≤ j),
    NatTrans.CommShift (system.transIso h).hom ℤ]

end CategoryTheory.StageSystem
