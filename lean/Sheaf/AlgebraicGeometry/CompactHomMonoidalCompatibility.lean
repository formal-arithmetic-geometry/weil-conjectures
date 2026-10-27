/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom

/-! Mate calculus for compact internal adjunction. -/

@[expose] public section

universe u uA

open CategoryTheory Limits Opposite MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme _root_.AlgebraicGeometry.Etale.DerivedCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

open TwoSquare

attribute [local irreducible] projectionMap _root_.DerivedCategory.monoidalClosed

variable (A : Type uA) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A] [UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
  {g : S' ⟶ S} {g' : X' ⟶ X}
  [HasCompactification f] [HasCompactification f']
  [(rightDerivedLowerShriek A f).IsLeftAdjoint]
  [(rightDerivedLowerShriek A f').IsLeftAdjoint]
  [IsIso (projectionMap A f)] [IsIso (projectionMap A f')]
  (sq : CommSq g' f' f g)
  (B : rightDerivedLowerShriek A f ⋙ L(upperStar A g) ⟶
    L(upperStar A g') ⋙ rightDerivedLowerShriek A f') [IsIso B]
  (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))

omit [HasSmallSiteSheafify A] in
private theorem compact_hom_compatibility
    (TX : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A))
    (TY : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A))
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M' : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A))
    (σ : TwoSquare TY (L(upperStar A f)) (L(upperStar A f')) TX)
    (μ : TwoSquare TX ((derivedTensor A X).obj M) ((derivedTensor A X').obj M') TX)
    (ρ : TwoSquare TX (rightDerivedLowerShriek A f) (rightDerivedLowerShriek A f') TY)
    (ν : TwoSquare TY ((derivedTensor A S).obj ((rightDerivedLowerShriek A f).obj M))
      ((derivedTensor A S').obj ((rightDerivedLowerShriek A f').obj M')) TY)
    (h : ν.whiskerLeft ((projectionMap A f).app M) =
      (σ ≫ᵥ μ ≫ᵥ ρ).whiskerRight ((projectionMap A f').app M'))
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    TY.map (((derivedHomRightDerivedLowerShriekIso A f).app (op M)).hom.app Q) ≫
      (mateEquiv (derivedTensorHomAdjunction A ((rightDerivedLowerShriek A f).obj M))
        (derivedTensorHomAdjunction A ((rightDerivedLowerShriek A f').obj M')) ν).app Q =
      (mateEquiv (derivedUpperStarLowerStarAdjunction A f)
        (derivedUpperStarLowerStarAdjunction A f') σ).app _ ≫
      (R(lowerStar A f')).map ((mateEquiv (derivedTensorHomAdjunction A M)
        (derivedTensorHomAdjunction A M') μ).app _) ≫
      (R(lowerStar A f')).map (((derivedHom A X').obj (op M')).map
        ((mateEquiv (rightDerivedUpperShriekAdjunction A f)
          (rightDerivedUpperShriekAdjunction A f') ρ).app Q)) ≫
      ((derivedHomRightDerivedLowerShriekIso A f').app (op M')).hom.app (TY.obj Q) := by
  have key :
      (mateEquiv (derivedTensorHomAdjunction A ((rightDerivedLowerShriek A f).obj M))
        (derivedTensorHomAdjunction A ((rightDerivedLowerShriek A f').obj M')) ν).whiskerTop
          ((derivedHomRightDerivedLowerShriekIso A f).app (op M)).hom =
      ((mateEquiv (rightDerivedUpperShriekAdjunction A f)
          (rightDerivedUpperShriekAdjunction A f') ρ ≫ₕ
        mateEquiv (derivedTensorHomAdjunction A M) (derivedTensorHomAdjunction A M') μ) ≫ₕ
        mateEquiv (derivedUpperStarLowerStarAdjunction A f)
          (derivedUpperStarLowerStarAdjunction A f') σ).whiskerBottom
            ((derivedHomRightDerivedLowerShriekIso A f').app (op M')).hom := by
    rw [← mateEquiv_hcomp, ← mateEquiv_hcomp]
    exact mateEquiv_whiskerTop_conjugateEquiv
      ((derivedUpperStarLowerStarAdjunction A f).comp
        ((derivedTensorHomAdjunction A M).comp (rightDerivedUpperShriekAdjunction A f)))
      (derivedTensorHomAdjunction A ((rightDerivedLowerShriek A f).obj M))
      ((derivedUpperStarLowerStarAdjunction A f').comp
        ((derivedTensorHomAdjunction A M').comp (rightDerivedUpperShriekAdjunction A f')))
      (derivedTensorHomAdjunction A ((rightDerivedLowerShriek A f').obj M'))
      ((projectionMap A f).app M) ((projectionMap A f').app M') _ ν h
  have result := congr_app key Q
  simpa only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app, TwoSquare.hComp_app,
    Functor.comp_obj, Category.assoc, Functor.map_comp] using result

omit [HasSmallSiteSheafify A] [UpperStarPreservesFlat A] in
private theorem derived_mate_pre_app
    (TY : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A)) [TY.LaxMonoidal]
    (U : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A))
    (V : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A))
    (b : V ⟶ TY.obj U) (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    (mateEquiv (derivedTensorHomAdjunction A U) (derivedTensorHomAdjunction A V)
      ((Functor.LaxMonoidal.μTwoSquare TY U).whiskerRight
        ((derivedTensor A S').map b))).app Q =
      (Functor.LaxMonoidal.ihomComparison TY U).app Q ≫
        ((derivedHom A S').map b.op).app (TY.obj Q) := by
  rw [mateEquiv_conjugateEquiv_vcomp]
  rfl

omit [HasSmallSiteSheafify A] [UpperStarPreservesFlat A] in
private theorem derived_hom_comparison_as_mate
    (TY : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A)) [TY.LaxMonoidal]
    (U Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    (mateEquiv (derivedTensorHomAdjunction A U)
      (derivedTensorHomAdjunction A (TY.obj U))
      (Functor.LaxMonoidal.μTwoSquare TY U)).app Q =
      (Functor.LaxMonoidal.ihomComparison TY U).app Q := rfl

omit [HasSmallSiteSheafify A] in
/-- Compatible compact projection squares induce compatible internal adjunctions.
Source: the final paragraph of the blueprint proof of smooth generic direct image;
`mateEquiv_whiskerTop_conjugateEquiv` and composition of mates.
(blueprint: lem-asd-compact-hom-mate-compatibility).

Proof: Conjugate the two projection maps through the ordinary, tensor--Hom and
exceptional adjunctions. The equality of projection squares gives equality after
whiskering these conjugates, by the mate/conjugation identity. Horizontal composition
of mates separates the three right-adjoint comparisons. Evaluate at Q, identify the
mates of the tensorators with the internal-Hom comparisons, and identify the mate of
tensoring with b with precomposition by b. This uses only adjunction identities, so
also covers zero objects and empty schemes. -/
theorem compactHomMonoidalCompatibility
    (TX : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)) [TX.LaxMonoidal]
    (TY : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A)) [TY.LaxMonoidal]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (σ : TwoSquare TY (L(upperStar A f)) (L(upperStar A f')) TX)
    (ρ : TwoSquare TX (rightDerivedLowerShriek A f) (rightDerivedLowerShriek A f') TY)
    (b : (rightDerivedLowerShriek A f').obj (TX.obj M) ⟶
      TY.obj ((rightDerivedLowerShriek A f).obj M))
    (h : ((Functor.LaxMonoidal.μTwoSquare TY ((rightDerivedLowerShriek A f).obj M)).whiskerRight
      ((derivedTensor A S').map b)).whiskerLeft ((projectionMap A f).app M) =
        (σ ≫ᵥ Functor.LaxMonoidal.μTwoSquare TX M ≫ᵥ ρ).whiskerRight
          ((projectionMap A f').app (TX.obj M)))
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    TY.map ((((derivedHomRightDerivedLowerShriekIso A f).app (op M)).app Q).hom) ≫
      (Functor.LaxMonoidal.ihomComparison TY ((rightDerivedLowerShriek A f).obj M)).app Q ≫
      ((derivedHom A S').map b.op).app (TY.obj Q) =
      (mateEquiv (derivedUpperStarLowerStarAdjunction A f)
        (derivedUpperStarLowerStarAdjunction A f') σ).app
          (((derivedHom A X).obj (op M)).obj ((rightDerivedUpperShriek A f).obj Q)) ≫
      (R(lowerStar A f')).map
        ((Functor.LaxMonoidal.ihomComparison TX M).app ((rightDerivedUpperShriek A f).obj Q)) ≫
      (R(lowerStar A f')).map (((derivedHom A X').obj (op (TX.obj M))).map
        ((mateEquiv (rightDerivedUpperShriekAdjunction A f)
          (rightDerivedUpperShriekAdjunction A f') ρ).app Q)) ≫
      (((derivedHomRightDerivedLowerShriekIso A f').app (op (TX.obj M))).app (TY.obj Q)).hom := by
  have result := compact_hom_compatibility A TX TY M (TX.obj M) σ
    (Functor.LaxMonoidal.μTwoSquare TX M) ρ
    ((Functor.LaxMonoidal.μTwoSquare TY ((rightDerivedLowerShriek A f).obj M)).whiskerRight
      ((derivedTensor A S').map b)) h Q
  rw [derived_mate_pre_app, derived_hom_comparison_as_mate] at result
  simpa only [Iso.app_hom] using result

end AlgebraicGeometry.Etale
