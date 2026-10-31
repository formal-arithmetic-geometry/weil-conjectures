/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactInternalAdjunctionMateIdentificationGeneral
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom
public import WeilConjectures.AlgebraicGeometry.CompactInternalAdjunctionMateCanonicalMaps
import WeilConjectures.AlgebraicGeometry.CompactHomMonoidalCompatibility
public import WeilConjectures.AlgebraicGeometry.CompactInternalAdjunctionMateIdentification

/-! Identification of the canonical maps in compact adjunction exchange.

The mate calculus over a general coefficient category is in
`Sheaf.AlgebraicGeometry.CompactInternalAdjunctionMateIdentificationCanonicalMaps` and
`Sheaf.AlgebraicGeometry.CompactInternalAdjunctionMateIdentificationGeneral` (split for compile
time). -/

@[expose] public section

universe u uA

open CategoryTheory Limits Opposite MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme _root_.AlgebraicGeometry.Etale.DerivedCategory MateIdentification

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

open TwoSquare

attribute [local irreducible] projectionMap _root_.DerivedCategory.monoidalClosed

section General

namespace MateIdentification

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
  [IsIso (projectionMap A f)] [IsIso (projectionMap A f')]
  (sq : CommSq g' f' f g)
  (B : rightDerivedLowerShriek A f ⋙ L(upperStar A g) ⟶
    L(upperStar A g') ⋙ rightDerivedLowerShriek A f') [IsIso B]
  (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))

omit [HasSmallSiteSheafify A] [IsIso (projectionMap A f')] in
omit [HasSmallSiteSheafify A] in
end MateIdentification

end General

-- The general identity `MateIdentification.compactInternalAdjunctionExchange_aux` (also used by
-- `CompactInternalAdjunctionExchange`) is specialised to `ModuleCat Λ` below; elaborate the
-- statement with the same (generic) instances so that the specialisation matches it
-- syntactically, instead of the kernel comparing the instances found through `ModuleCat`.
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
  {g : S' ⟶ S} {g' : X' ⟶ X}
  [HasCompactification f] [HasCompactification f']
  [IsIso (projectionMap (ModuleCat.{u + 1} Λ) f)] [IsIso (projectionMap (ModuleCat.{u + 1} Λ) f')]
  (sq : CommSq g' f' f g)
  (B : rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ⋙ L(upperStar (ModuleCat.{u + 1} Λ) g) ⟶
    L(upperStar (ModuleCat.{u + 1} Λ) g') ⋙ rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f') [IsIso B]
  (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

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
    (h : letI := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) g
      let := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) g'
      let σ := TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom
      let μ := Functor.LaxMonoidal.μTwoSquare (L(upperStar (ModuleCat.{u + 1} Λ) g')) N
      let ρ := TwoSquare.mk _ _ _ _ (inv B)
      let ν := (Functor.LaxMonoidal.μTwoSquare (L(upperStar (ModuleCat.{u + 1} Λ) g))
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj N)).whiskerRight
          ((curriedTensor _).map (inv (B.app N)))
      ν.whiskerLeft ((projectionMap (ModuleCat.{u + 1} Λ) f).app N) =
        (σ ≫ᵥ μ ≫ᵥ ρ).whiskerRight
          ((projectionMap (ModuleCat.{u + 1} Λ) f').app ((L(upperStar (ModuleCat.{u + 1} Λ) g')).obj N)))
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L(upperStar (ModuleCat.{u + 1} Λ) g)).map
          ((((derivedHomRightDerivedLowerShriekIso Λ f).app (op N)).app Q).hom) ≫
        derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) g ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj N) Q ≫
        (((derivedHom (ModuleCat.{u + 1} Λ) S').map (inv (B.app N)).op).app
          ((L(upperStar (ModuleCat.{u + 1} Λ) g)).obj Q)) =
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app _ ≫
        (R(lowerStar (ModuleCat.{u + 1} Λ) f')).map
          (derivedHomUpperStarComparison (ModuleCat.{u + 1} Λ) g' N ((rightDerivedUpperShriek Λ f).obj Q)) ≫
        (R(lowerStar (ModuleCat.{u + 1} Λ) f')).map
          (((derivedHom (ModuleCat.{u + 1} Λ) X').obj (op ((L(upperStar (ModuleCat.{u + 1} Λ) g')).obj N))).map
            ((mateEquiv (rightDerivedUpperShriekAdjunction Λ f)
              (rightDerivedUpperShriekAdjunction Λ f') (inv B)).app Q)) ≫
        ((((derivedHomRightDerivedLowerShriekIso Λ f').app
          (op ((L(upperStar (ModuleCat.{u + 1} Λ) g')).obj N))).app ((L(upperStar (ModuleCat.{u + 1} Λ) g)).obj Q)).hom) := by
  unfold derivedHomRightDerivedLowerShriekIso
  exact compactInternalAdjunctionExchange_aux (ModuleCat.{u + 1} Λ) sq B N
    (rightDerivedUpperShriekAdjunction Λ f) (rightDerivedUpperShriekAdjunction Λ f') h Q

end AlgebraicGeometry.Etale
