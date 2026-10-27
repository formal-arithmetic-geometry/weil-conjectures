/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.SfExactPullbackCounitNormalization
public import Sheaf.Paper.CompletedPullback
public import Sheaf.Paper.StrictQuotientPullbackComputation
import Sheaf.CategoryTheory.ExactSquareDerivedCounit
import Sheaf.CategoryTheory.DerivedTowerCounitProjections
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-! # The completed augmentation as the normalized derived adjunct

Source: blueprint localization returned Step 6, immersion-comparison Step 5;
Stacks Derived Categories, Tags 0FND and 09T5
(blueprint: lem-sf-completed-augmentation-adjunct).

The module functor is the published scalar-transport presentation of tensor pullback.
The tensor-generator isomorphism and its universal-counit normalization are those of
`ExactPullbackNormalization.counit_normalization`. Indices `n : ℕ` mean exponent `n+1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ExactPullbackNormalization

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  {X Y : Scheme.{u}} (g : Y ⟶ X) [IsIso (completedCoefficientMap g d)]
  [(moduleFunctor d g).Additive]
  [PreservesFiniteLimits (moduleFunctor d g)] [PreservesFiniteColimits (moduleFunctor d g)]

/-- The pulled quotient augmentation `a_K`, using the exact constant-tower comparison.
Here `constantIso.hom` is the inverse of the paper's `j`.
Source: localization Step 6; Stacks 0FND
(blueprint: lem-sf-completed-augmentation-adjunct). -/
def pulledAugmentation (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    (completedDerivedConstant d Y).obj ((moduleFunctor d g).mapDerivedCategory.obj K) ⟶
      (towerFunctor d g).mapDerivedCategory.obj ((completedReductionTower X d).obj K) :=
  (constantIso d g).hom.app K ≫
    (towerFunctor d g).mapDerivedCategory.map ((completedReductionTowerUnit d X).app K)

/-- The exact pulled strict quotient complex, before localization or K-injective resolution.
Source: localization Step 6, representative paragraph; Stacks 0FND
(blueprint: lem-sf-completed-augmentation-adjunct). -/
abbrev pulledReductionComplex
    (P : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :=
  ((towerFunctor d g).mapHomologicalComplex (.up ℤ)).obj
    ((completedReductionComplexTowerFunctor X d).obj P)

/-- The strict chain augmentation with components `F(P → P tensor P_n)`.
This uses the ordinary constant-tower identity and the existing quotient section map.
Source: localization Step 6, representative paragraph; Stacks 0FND
(blueprint: lem-sf-completed-augmentation-adjunct). -/
def pulledChainAugmentation
    (P : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
    ((completedTowerConstant d Y).mapHomologicalComplex (.up ℤ)).obj
        (((moduleFunctor d g).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      pulledReductionComplex d g P :=
  letI := completedReductionModuleTowerFunctor_additive X d
  (NatTrans.mapHomologicalComplex
    ((Functor.compConstIso ℕᵒᵖ (moduleFunctor d g)).hom ≫
      Functor.whiskerRight (completedReductionModuleUnit d X) (towerFunctor d g))
    (.up ℤ)).app P

/-- The actual compatible-family chain map into the limit of a tower resolution.
It is the ordinary constant/limit transpose, not a choice of a derived cone map.
Source: localization Step 6, representative paragraph; Stacks 0FND
(blueprint: lem-sf-completed-augmentation-adjunct). -/
def resolvedChainAugmentation
    (P : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
    (J : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ)
    (r : pulledReductionComplex d g P ⟶ J) :
    ((moduleFunctor d g).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((lim : pbcTowers Y (pbcAdicCompletion Y d) ⥤
        pbcModules Y (pbcAdicCompletion Y d)).mapHomologicalComplex (.up ℤ)).obj J :=
  ((constLimAdj : completedTowerConstant d Y ⊣ lim).mapHomologicalComplex (.up ℤ)).homEquiv
    _ J (pulledChainAugmentation d g P ≫ r)

/-- The canonical map from the derived pulled quotient tower to a resolved presentation.
On K-flat P and a quasi-isomorphism r this is a canonical isomorphism; writing its forward
map avoids arbitrary inverse choices.
Source: localization Step 6, canonical localization and resolution comparisons; Stacks 0FND
(blueprint: lem-sf-completed-augmentation-adjunct). -/
def pulledResolutionComparison
    (P : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
    (J : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ)
    (r : pulledReductionComplex d g P ⟶ J) :
    (towerFunctor d g).mapDerivedCategory.obj
        ((completedReductionTower X d).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj J :=
  (towerFunctor d g).mapDerivedCategory.map (completedReductionTowerComplexCounit X d P) ≫
    (towerFunctor d g).mapDerivedCategoryFactors.hom.app
      ((completedReductionComplexTowerFunctor X d).obj P) ≫ DerivedCategory.Q.map r

/-- The actual normalized completed augmentation is the derived adjunct of the pulled
strict quotient augmentation, naturally for every unbounded derived morphism, and is
represented by the compatible component maps on every K-injective tower resolution.

Source: blueprint localization returned Step 6, immersion-comparison Step 5;
Stacks Derived Categories, Tags 0FND and 09T5
(blueprint: lem-sf-completed-augmentation-adjunct).

The published `exactAugmentation` is precisely the actual ambient comparison transported
by the original universal counits, as asserted by
lem-sf-exact-pullback-counit-normalization. That lemma's tensor-generator isomorphism
identifies the scalar-transport module functor used here with the statement's tensor
pullback, carrying all quotient augmentations and resolution maps with it.

Proof:
1. Apply lem-sf-exact-pullback-counit-normalization to ordinary and tower pullback.
On a flat-term K-flat representative P, exact termwise pullback sends the actual strict
quotient augmentation to pulledChainAugmentation, whose localization is a_K.
The actual construction is L_Y(a_K) after the projection-defined constant-tower map z.
2. Apply lem-weil-pbc-exact-square-derived-counit to the identity square with
Delta left adjoint to lim. The unbounded tower resolutions are supplied by
lem-weil-pbc-ringed-strict-tower-homotopy-limit. The canonical adjunction is that of
lem-coef-derived-tower-counit-projections. For q : Delta C -> I the derived transpose
formula is L(Qq) v = delta_I Q(z^q), where z^q has components q_n. Cancelling the
invertible L(Qq) identifies the published z with this canonical unit v.
3. Substitute z=v. For any K-injective resolution r of the pulled quotient complex,
apply the same transpose formula to r composed with pulledChainAugmentation. The
ordinary adjunction gives resolvedChainAugmentation with components r_n F(P -> P_n).
Its localization followed by the universal derived-limit comparison gives the actual
augmentation after pulledResolutionComparison. Both comparison maps are invertible,
so this determines the same derived morphism for every representative and resolution.
4. The strict quotient unit is natural on complexes by (f tensor 1)(x tensor 1) =
f(x) tensor 1, and descends to all derived maps. Naturality of the exact constant
comparison and the adjunction unit gives the displayed naturality equation. No
completeness, preservation of products, or preservation of K-injectives by F is used. -/
theorem completed_augmentation_adjunct :
    (∀ K : DerivedCategory (pbcModules X (pbcAdicCompletion X d)),
      exactAugmentation d g K =
        (d.constantRlimAdjunction Y).unit.app ((moduleFunctor d g).mapDerivedCategory.obj K) ≫
          (completedTowerRlim d Y).map (pulledAugmentation d g K)) ∧
    (∀ (K K' : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) (f : K ⟶ K'),
      (moduleFunctor d g).mapDerivedCategory.map f ≫ exactAugmentation d g K' =
        exactAugmentation d g K ≫ (completedTowerRlim d Y).map
          ((towerFunctor d g).mapDerivedCategory.map ((completedReductionTower X d).map f))) ∧
    (∀ (P : CbcStrictKFlatRepresentative d X)
        (J : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ)
        (r : pulledReductionComplex d g P.complex ⟶ J) [QuasiIso r] [J.IsKInjective],
      IsIso (pulledResolutionComparison d g P.complex J r) ∧
      (∀ (q : ℤ) (n : ℕ),
        (resolvedChainAugmentation d g P.complex J r).f q ≫ limit.π (J.X q) (op n) =
          (moduleFunctor d g).map
              (((cbcStrictAugmentation d X P.complex).f q).app (op n)) ≫
            (r.f q).app (op n)) ∧
      exactAugmentation d g (DerivedCategory.Q.obj P.complex) ≫
          (completedTowerRlim d Y).map (pulledResolutionComparison d g P.complex J r) =
        (moduleFunctor d g).mapDerivedCategoryFactors.hom.app P.complex ≫
          DerivedCategory.Q.map (resolvedChainAugmentation d g P.complex J r) ≫
          (completedRlimUnit Y (pbcAdicCompletion Y d)).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) := by
  sorry

end AlgebraicGeometry.Scheme.ExactPullbackNormalization
