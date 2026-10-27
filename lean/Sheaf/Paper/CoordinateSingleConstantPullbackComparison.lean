/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E8
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction

/-! # The recorded constant pullback agrees with the canonical derived comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors
  leftDerivedUpperStarIsoMapDerivedCategory

private theorem isoWhiskerLeft_app_eq
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) {G H : D ⥤ E} (e : G ≅ H) (X : C) :
    (Functor.isoWhiskerLeft F e).app X = e.app (F.obj X) := by
  rfl

/-- The cached ordinary constant pullback is the canonical derived comparison.
Source: sk-thm-dnc, Local construction, canonical constant-coefficient identifications
(blueprint: lem-trf-coordinate-single-constant-pullback-comparison).

Proof: Use the published factorization of ordinaryFiniteUnitPullback through the
single-degree comparison and the pullback of the constant sheaf. The published
ordinaryFiniteSingleExactPullbackIso_eq and ordinaryFiniteSingleFunctor_eq replace
the cached comparisons by the canonical ones. Evaluation of a composite natural
isomorphism and of left whiskering gives the three factors defining
leftDerivedUpperStarSingleConstantSheafIso. Associativity of isomorphism composition
identifies their products. The large derived-functor comparison is kept abstract.
-/
theorem coordinateUnitPullback_eq_singleConstant
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S T : Scheme.{u}} (v : T ⟶ S) :
    ordinaryFiniteUnitPullback A v =
      leftDerivedUpperStarSingleConstantSheafIso
        (ModuleCat.{u + 1} A) v (𝟙_ (ModuleCat.{u + 1} A)) := by
  rw [ordinaryFiniteUnitPullback_eq, leftDerivedUpperStarSingleConstantSheafIso]
  unfold ordinaryFiniteSinglePullbackIso
  rw [ordinaryFiniteSingleExactPullbackIso_eq]
  simp only [NatIso.trans_app, isoWhiskerLeft_app_eq, Iso.trans_assoc,
    ordinaryFiniteSingleFunctor_eq]
  rfl

end AlgebraicGeometry.Etale
