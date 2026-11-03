/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralTensorPullback.IntegralTensorPullbackData

import WeilConjectures.AlgebraicGeometry.IntegralTensorPullback.IntegralRestrictedQuotientTower
import WeilConjectures.CategoryTheory.Augmented.AugmentedTowerRoosTransport

/-! # Constant scalar restriction of the strict pulled reduction tower

Source: blueprint det-lem-int-tensor-pullback, comparison paragraph; Stacks 099I.
(blueprint: lem-sfb-internal-pullback-constant-roos-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralTensorPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.IntegralTensorPullback

namespace AlgebraicGeometry.ProEtale.IntegralTensorPullback

/-- Restriction carries the pulled quotient Roos complex and its augmentation to
the constant scalar quotient Roos complex with the normalized source comparison.
This is a chain-level statement for every complex, independent of completeness.

Source: blueprint det-lem-int-tensor-pullback, comparison with the Stacks Project;
strict normalization step 9; Stacks 099I and 099N(5).
(blueprint: lem-sfb-internal-pullback-constant-roos-unit).

Proof: the constant-to-continuous integral map induces an isomorphism on every
positive finite quotient, since continuous functions to a finite discrete quotient
are locally constant. Thus extending the constant quotient to continuous scalars
recovers the actual finite quotient, with its quotient map and all transitions.
Associativity of balanced tensor products gives Res(M tensor_R A_n) isomorphic to
Res(M) tensor_C A_n for arbitrary M. Combine this with restrictionPullback and
its generator normalization to compare the two pulled towers, including their
quotient augmentations. Restriction is exact and preserves products. Its canonical
product comparison and the level isomorphisms intertwine 1 minus shift, so they
induce an isomorphism on mapping cocones. On the two cone coordinates its composite
with the restricted augmentation is (the common quotient augmentation,0).
The normalized source map is restrictionPullbackComplex. Equality on both cone
coordinates proves the equation; no K-flat or boundedness hypothesis is needed.
The empty scheme, zero complex, and identity map require no separate choices. -/
theorem constant_roos_unit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    ∃ e : (((restriction l E X).mapHomologicalComplex (.up ℤ)).obj
          (WeilConjectures.integralOperationsRoos (pulledTower l E g P))) ≅
        WeilConjectures.integralOperationsRoos
          (constantPulledTower l E g
            (((restriction l E Y).mapHomologicalComplex (.up ℤ)).obj P)),
      ((restriction l E X).mapHomologicalComplex (.up ℤ)).map (comparison l E g P) ≫
          e.hom =
        (restrictionPullbackComplex l E g P).hom ≫
          constantComparison l E g
            (((restriction l E Y).mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨e, he⟩ := restricted_pulled_tower_unit l E g P
  let F := (CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapHomologicalComplex
    (.up ℤ)
  let G := (CondensedRing.upperStar (constantRing l E) g).mapHomologicalComplex (.up ℤ)
  let Q := ((restriction l E Y).mapHomologicalComplex (.up ℤ)).obj P
  let γ : (Functor.const ℕᵒᵖ).obj (F.obj P) ⟶ pulledTower l E g P :=
    (Functor.constComp ℕᵒᵖ P F).inv ≫ Functor.whiskerRight (towerUnit l E Y P) F
  let δ : (Functor.const ℕᵒᵖ).obj (G.obj Q) ⟶ constantPulledTower l E g Q :=
    (Functor.constComp ℕᵒᵖ Q G).inv ≫ Functor.whiskerRight (constantTowerUnit l E Y Q) G
  exact augmentedTowerRoosTransport (restriction l E X) (F.obj P) (G.obj Q)
    (pulledTower l E g P) (constantPulledTower l E g Q) γ δ
    (restrictionPullbackComplex l E g P) e he

end AlgebraicGeometry.ProEtale.IntegralTensorPullback
