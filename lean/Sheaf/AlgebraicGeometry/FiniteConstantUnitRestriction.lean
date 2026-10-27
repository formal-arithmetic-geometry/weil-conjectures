/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R9
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Evaluation of the finite constant-coefficient open unit

Source: Stacks, Tags 0D6H, 08BJ, 03FD and 03F3.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- An invertible actual derived open unit for the regular constant module induces
an invertible restriction on abelian derived sections of its underlying constant group.
Source: Stacks, Tags 0D6H, 08BJ, 03FD and 03F3; proof steps 1--2 of
`lem-sfb-torsion-open-test-devissage`.
(blueprint: lem-sfb-finite-constant-unit-restriction).

Proof: resolve the pullback of the constant regular module on the open by a
nonnegative complex of injective module sheaves. The direct image of this complex
is K-injective, since inverse image is exact and left adjoint to direct image.
Consequently derived evaluation of the actual unit at V is computed by the
ordinary unit followed by the direct image of the resolution map. On sections
this is exactly restriction from V to its inverse-image principal open, followed
by the resolution map. Thus deriving restriction identifies this specific arrow
with evaluation of the given unit, using the derived-composition comparison.
It is invertible because the given unit is invertible.

The underlying additive sheaf of the constant regular module is the constant
abelian sheaf with value A: forgetting finite scalars commutes with constant
sheafification. The module-to-abelian derived evaluation comparison is invertible
on bounded below complexes; underlying abelian sheaves of injective module
sheaves are evaluation-acyclic. The comparison commutes with section restriction
and with constant inverse image. Apply it to the preceding arrow to obtain the
displayed, already specified abelian restriction, rather than choosing an
arbitrary isomorphism of its endpoints. No weak contractibility or nonemptiness
is needed for this comparison. -/
theorem finiteConstantUnit_isIso_derivedRestriction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) (f : Γ(X, ⊤))
    (hunit : IsIso ((derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} A) (X.basicOpen f).ι).unit.app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A A)))))
    (V : X.ProEt) :
    IsIso ((Functor.rightDerivedFunctorNatTrans
      (F := sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
        (evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj (op V))
      (G := sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
        (evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op (Scheme.ProEt.mk
            ((V.left.basicOpen (V.hom.appTop.hom f)).ι ≫ V.hom))))
      ((sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).map
        (MorphismProperty.Over.homMk
          (V.left.basicOpen (V.hom.appTop.hom f)).ι rfl :
            Scheme.ProEt.mk ((V.left.basicOpen (V.hom.appTop.hom f)).ι ≫ V.hom) ⟶ V).op)).app
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of A)))) := by sorry

end AlgebraicGeometry.ProEtale
