/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Sheaf.Paper.BoundaryExceptionalComparisonData
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap

/-!
# The normalized pro-etale transpose of the etale projection

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-direct-image.proof.md`, Step 1; Stacks Tags 0E48 and 07A4
(blueprint: lem-sp-direct-image-etale-mate-isomorphism).

All categories are ordinary uncompleted constant-ring module categories, in their
fixed-ring sheaf presentation. The coefficient on X is written as the canonical
pullback of B_Y, and its pro-etale realization as the pullback of nu_Y^* B_Y.
Thus every constant-coefficient identification in the statement is built into the
endpoints, without an arbitrary choice of comparison or any flatness assumption.

## Main definitions and statement

* `spDirectImageComparisonIso`: the recorded normalized comparison, included from D+.
* `spEtaleMate`: the transported etale projection, including both tensor comparisons.
* `spEtaleMate_transpose`: its normalized counit transpose and conditional invertibility.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- B_Y in degree zero, with its A-action given by the specified ring homomorphism.
Source: blueprint direct-image proof, Step 1; Stacks 0E48
(blueprint: lem-sp-direct-image-etale-mate-isomorphism). -/
def spEtaleCoefficient {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) (Y : Scheme.{u}) :
    DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      ((ModuleCat.restrictScalars a).obj (ModuleCat.of B B)))

/-- H = K tensor B_X, writing B_X as the canonical pullback of B_Y.
Source: blueprint direct-image proof, Step 1; Stacks 07A4
(blueprint: lem-sp-direct-image-etale-mate-isomorphism). -/
def spEtaleTensorObject {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj
    ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
      (spEtaleCoefficient a Y))

/-- The specified etale projection pi_K, with coefficient B_Y.
Source: blueprint direct-image proof, Step 1; Stacks 0E48
(blueprint: lem-sp-direct-image-etale-mate-isomorphism). -/
abbrev spEtaleProjection {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app K).app
    (spEtaleCoefficient a Y)

/-- Include the recorded normalized D+ comparison into the unbounded categories.
The four endpoint isomorphisms are the standard exact-functor and right-derived
compatibilities with the fully faithful D+ inclusion. In particular the middle
arrow is exactly fixedComparisonDirectImageMatePlus, not a chosen endpoint isomorphism.
Source: blueprint direct-image proof, Step 1; Stacks 099R and 0B65
(blueprint: lem-sp-direct-image-etale-mate-isomorphism). -/
def spDirectImageComparisonIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : ∃ n : ℤ, K.IsGE n) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K) ≅
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K) := by
  let J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨K, hK⟩
  letI := isIso_fixedComparisonDirectImageMatePlus A f
  exact
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.mapIso
        ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.app
          J).symm ≪≫
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlusCompatibility.app
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) f).obj J)).symm ≪≫
      DerivedCategory.Plus.ι.mapIso
        ((asIso (fixedComparisonDirectImageMatePlus A f)).app J) ≪≫
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj J) ≪≫
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.mapIso
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlusCompatibility.app J)

/-- The target identification C_X H = N tensor p^* C_Y B_Y, using the canonical
tensor comparison and the inverse of the canonical pullback square.
Source: blueprint direct-image proof, Step 1; Stacks 07A4 and 0E48
(blueprint: lem-sp-direct-image-etale-mate-isomorphism). -/
def spEtaleMateTargetIso {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) K).app
      ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
        (spEtaleCoefficient a Y)) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)).mapIso
        ((BoundaryComparison.pullbackSquare (ModuleCat.{u + 1} A) f).symm.app
          (spEtaleCoefficient a Y))

/-- The source RN tensor B_Y, with B_Y presented as C_Y of the etale coefficient.
Source: blueprint direct-image proof, Step 1; Stacks 0E48
(blueprint: lem-sp-direct-image-etale-mate-isomorphism). -/
abbrev spEtaleMateSource {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
    ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K))).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
          (spEtaleCoefficient a Y))

/-- The tensor target N tensor B_X, in the same constant-section identifications.
Source: blueprint direct-image proof, Step 1; Stacks 0E48
(blueprint: lem-sp-direct-image-etale-mate-isomorphism). -/
abbrev spEtaleMateTarget {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)).obj
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
          (spEtaleCoefficient a Y)))

/-- The map t: tensor beta_K inverse, undo the source tensor comparison, apply
C_Y(pi_K), then beta_H and the target tensor/pullback identification.
Only K and H are required to lie in D+; the source tensor on Y is unrestricted.
Source: blueprint direct-image proof, Step 1; Stacks 0E48
(blueprint: lem-sp-direct-image-etale-mate-isomorphism). -/
def spEtaleMate {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : ∃ n : ℤ, K.IsGE n)
    (hH : ∃ n : ℤ, (spEtaleTensorObject a f K).IsGE n) :
    spEtaleMateSource a f K ⟶
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
        (spEtaleMateTarget a f K) :=
  ((derivedTensor (ModuleCat.{u + 1} A) Y).map
      (spDirectImageComparisonIso A f K hK).inv).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
          (spEtaleCoefficient a Y)) ≫
    ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A)
      ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K)).app
        (spEtaleCoefficient a Y)).inv ≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
      (spEtaleProjection a f K) ≫
    (spDirectImageComparisonIso A f (spEtaleTensorObject a f K) hH).hom ≫
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map
      (spEtaleMateTargetIso a f K).hom

/-- The normalized transpose of the transported etale projection is the pro-etale
counit tensored with the coefficient identity. Invertibility of pi_K implies that of t.
Source: blueprint main-20261015, direct-image proof, Step 1; Stacks 0E48 and 07A4
(blueprint: lem-sp-direct-image-etale-mate-isomorphism).

Proof (the four steps of the node):
1. Form the ringed square with horizontal site comparisons and vertical p on the
etale and pro-etale sites. The structure-ring maps preserve constant sections
(prop-weil-pbc-proetale-constant-ring-map). Its exchange maps at K,H are exactly
the recorded normalized direct-image mates: their transposes are the inverse
pullback comparison followed by comparison of the etale counit
(lem-weil-pbc-comparison-direct-image-canonical-mate). Include these maps from D+
using the exact-functor and right-derived compatibility isomorphisms.
2. Apply lem-weil-pbc-ringed-exchange-tensor-coherence with E=K, Q=B_Y[0]. Its
projection is spEtaleProjection by def-kun-projection-formula-map. Its tensor
identifications are the canonical ones of
lem-weil-pbc-ringed-topoi-derived-tensor-pullback. The resulting square says that
beta_H after C(pi_K), including the target comparison, is the pro-etale projection
after beta_K tensor identity. No cartesianness or flatness is needed.
3. Precompose with beta_K inverse tensor identity. Bifunctoriality cancels beta_K.
The result is exactly spEtaleMate. Transpose under the pro-etale adjunction; by
the definition of the projection mate this is the tensor-pullback comparison
followed by counit tensor identity. Precompose with the inverse comparison.
4. If pi_K is invertible, reverse the displayed definition of spEtaleMate using
pi_K inverse, beta_H inverse, beta_K, and the inverse tensor identifications.
Functoriality and the inverse identities give a two-sided inverse. No assertion
that pi_K is always invertible is used. -/
theorem spEtaleMate_transpose (ℓ p : ℕ) (_hℓ : ℓ.Prime)
    (k : Type u) [Field k] [CharP k p] (_hp : 0 < p) (_hne : p ≠ ℓ)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, (ℓ : A) ^ n = 0) (_hB : ∃ n : ℕ, (ℓ : B) ^ n = 0)
    (a : A →+* B) {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : ∃ n : ℤ, K.IsGE n)
    (hH : ∃ n : ℤ, (spEtaleTensorObject a f K).IsGE n) :
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f
      ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K))
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
        (spEtaleCoefficient a Y))).inv ≫
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv
        (spEtaleMateSource a f K) (spEtaleMateTarget a f K)).symm
          (spEtaleMate a f K hK hH) =
      ((derivedTensor (ModuleCat.{u + 1} A) X).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K))).app
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
            (spEtaleCoefficient a Y))) ∧
    (IsIso (spEtaleProjection a f K) → IsIso (spEtaleMate a f K hK hH)) := by
  sorry

end AlgebraicGeometry.ProEtale
