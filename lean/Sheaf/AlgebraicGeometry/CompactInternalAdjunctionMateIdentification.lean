/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom
import Sheaf.AlgebraicGeometry.CompactHomMonoidalCompatibility

/-! Identification of the canonical maps in compact adjunction exchange. -/

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
/-- Identify the mate calculation with the canonical Cartesian comparison maps.
Source: the final paragraph of the blueprint proof of smooth generic direct image.
(blueprint: lem-asd-compact-hom-mate-identification).

Proof: Apply compactHomMonoidalCompatibility to the two pullback functors, the
pullback-composition square, and inverse compact exchange. The mates of these squares
are respectively ordinary base change, internal-Hom pullback comparison, and exceptional
exchange. The internal-Hom map induced by inverse compact exchange is precomposition
with its component. Expanding these canonical definitions gives the displayed equality.
No extra boundedness, finiteness or dualizability condition on N or Q is used. -/
theorem compactInternalAdjunctionExchangeOfMateCompatibility
    (h : letI := leftDerivedUpperStarMonoidal A g
      let := leftDerivedUpperStarMonoidal A g'
      let σ := TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A sq).hom
      let μ := Functor.LaxMonoidal.μTwoSquare (L(upperStar A g')) N
      let ρ := TwoSquare.mk _ _ _ _ (inv B)
      let ν := (Functor.LaxMonoidal.μTwoSquare (L(upperStar A g))
        ((rightDerivedLowerShriek A f).obj N)).whiskerRight
          ((curriedTensor _).map (inv (B.app N)))
      ν.whiskerLeft ((projectionMap A f).app N) =
        (σ ≫ᵥ μ ≫ᵥ ρ).whiskerRight
          ((projectionMap A f').app ((L(upperStar A g')).obj N)))
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    (L(upperStar A g)).map
          ((((derivedHomRightDerivedLowerShriekIso A f).app (op N)).app Q).hom) ≫
        derivedHomUpperStarComparison A g ((rightDerivedLowerShriek A f).obj N) Q ≫
        (((derivedHom A S').map (inv (B.app N)).op).app
          ((L(upperStar A g)).obj Q)) =
      (derivedBaseChangeMap A sq).app _ ≫
        (R(lowerStar A f')).map
          (derivedHomUpperStarComparison A g' N ((rightDerivedUpperShriek A f).obj Q)) ≫
        (R(lowerStar A f')).map
          (((derivedHom A X').obj (op ((L(upperStar A g')).obj N))).map
            ((mateEquiv (rightDerivedUpperShriekAdjunction A f)
              (rightDerivedUpperShriekAdjunction A f') (inv B)).app Q)) ≫
        ((((derivedHomRightDerivedLowerShriekIso A f').app
          (op ((L(upperStar A g')).obj N))).app ((L(upperStar A g)).obj Q)).hom) := by
  let := leftDerivedUpperStarMonoidal A g
  let := leftDerivedUpperStarMonoidal A g'
  have result := compactHomMonoidalCompatibility A
    (L(upperStar A g')) (L(upperStar A g)) N
    (TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A sq).hom)
    (TwoSquare.mk _ _ _ _ (inv B)) (inv (B.app N)) h Q
  exact result

end AlgebraicGeometry.Etale
