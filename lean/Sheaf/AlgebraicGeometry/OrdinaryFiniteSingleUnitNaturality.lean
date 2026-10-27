/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import all Sheaf.AlgebraicGeometry.OrdinaryFiniteDerivedRightUnitPullback
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # Naturality of the inverse right unit for ordinary finite coefficients

Source: the tensor-unit normalization in thm-amb-p1-decomposition.proof.md
(blueprint: lem-asd-ordinary-finite-single-unit-naturality).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u uB

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
attribute [local irreducible]
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors

private theorem constant_unit_naturality
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) {K K' : DerivedCategory (Sheaf X.smallEtaleTopology B)} (f : K ⟶ K') :
    f ≫ (constant_unit_iso B X K').inv =
      (constant_unit_iso B X K).inv ≫
        ((derivedTensor B X).map f).app (constantSingle B X (𝟙_ B)) := by
  dsimp only [constant_unit_iso, Iso.trans_inv, Functor.mapIso_inv]
  exact (derivedTensorRightUnitorInvComp B X (singleFunctorObjUnitIso B X).inv).naturality f

/-- The inverse right-unit comparison with constant coefficients is natural in its object.
Source: the tensor-unit normalization in the projective-line evaluation argument,
the current blueprint, thm-amb-p1-decomposition.proof.md
(blueprint: lem-asd-ordinary-finite-single-unit-naturality).

Proof: write the comparison as the inverse derived right unitor followed by tensoring
with the inverse of singleFunctorObjUnitIso. Naturality of the right unitor, followed
by tensor interchange, is exactly the naturality of derivedTensorRightUnitorInvComp.
This argument works for every coefficient ring and every scheme, including zero
coefficients and empty schemes. -/
theorem ordinaryFiniteSingleUnit_naturality (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) {K K' : DerivedCategoryModule A X} (f : K ⟶ K') :
    f ≫ (derivedTensorSingleUnitIso K').inv = (derivedTensorSingleUnitIso K).inv ≫
      ((ordinaryFiniteTensor A X).map f).app (ordinaryFiniteUnit A X) := by
  exact constant_unit_naturality (ModuleCat.{u + 1} A) X f

end AlgebraicGeometry.Etale
