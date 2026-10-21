/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.StrictRoosModel
import Sheaf.CategoryTheory.StrictRoosHomotopyFunctor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Strict scalar pullback cone naturality

Source: Bhatt--Scholze, Definition 3.4.10, Proposition 3.5.1 and Lemma 6.5.9(4);
Stacks Tags 03EK, 014E, 06YT and 04VG. The strict construction is agent formulated.
(blueprint: lem-weil-scalar-pullback-strict-cone-naturality).

Levels n denote positive exponents n+1. All tensors, inverse images, tower transitions
and Roos cones below are the recorded constructions, before localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The source tower D_E(P) with termwise ordinary scalar extension.
Source: Stacks 03EK (blueprint: lem-weil-scalar-pullback-strict-cone-naturality). -/
def scalarPullbackSourceTower {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y) :=
  integralOperationsPullbackTowerFunctor l E g ⋙
    (Functor.whiskeringRight _ _ _).obj (completedOrdinaryScalarComplex l E L ι X)

/-- The target tower D_L(P tensor S), with its recorded quotient transitions.
Source: Stacks 03EK (blueprint: lem-weil-scalar-pullback-strict-cone-naturality). -/
def scalarPullbackTargetTower {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y) :=
  completedOrdinaryScalarComplex l E L ι Y ⋙ integralOperationsPullbackTowerFunctor l L g

/-- The local inverse-image tensor generator, including its finite scalar b.
Source: Stacks 03D2, 03EK
(blueprint: lem-weil-scalar-pullback-strict-cone-naturality). -/
def scalarPullbackGenerator {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y)
    (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ)
    (V : Y.ProEt) (p : (P.X i).val.obj (op V))
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj (op V))
    (b : (integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange g).obj V))) :
    ((((integralOperationsPullbackLevel l E g n).obj P).X i).val.obj
      (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange g).obj V))) :=
  b • (@id
    (((integralOperationsLevelPullback l E g n).obj
      (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i)).val.obj
        (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange g).obj V)))
    (integralOperationsPullbackGenerator l E g n
      (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) V
        (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) a p)))

/-- The canonical tensor/product comparison, defined by the tensor of each projection.
No basis occurs in this definition.
Source: Stacks 03EK (blueprint: lem-weil-scalar-pullback-strict-cone-naturality). -/
def scalarPullbackProductMap (X : AlgebraicGeometry.Scheme.{t})
    (K : ℕ → CochainComplex (integralTowerModules l E X) ℤ) :
    (completedOrdinaryScalarComplex l E L ι X).obj (∏ᶜ K) ⟶
      ∏ᶜ fun n ↦ (completedOrdinaryScalarComplex l E L ι X).obj (K n) :=
  Pi.lift fun n ↦ (completedOrdinaryScalarComplex l E L ι X).map (Pi.π K n)

/-- The endomorphism 1-s of a strict tower, used to expose both Roos coordinates.
Source: Stacks 08TC (blueprint: lem-weil-scalar-pullback-strict-cone-naturality). -/
def scalarPullbackRoosEnd (X : AlgebraicGeometry.Scheme.{t})
    (T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E X) ℤ) :=
  towerTransitionEndomorphism (K := fun n ↦ T.obj (op n)) (integralOperationsTowerStep T)

/-- The exact local generator condition on a natural strict tower map. A tower morphism
already includes every quotient-transition and cochain-differential square.
Source: Stacks 03EK (blueprint: lem-weil-scalar-pullback-strict-cone-naturality). -/
def ScalarPullbackGeneratorFormula {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y)
    (d : scalarPullbackSourceTower l E L ι g ⟶ scalarPullbackTargetTower l E L ι g) : Prop :=
  ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ)
    (V : Y.ProEt) (p : (P.X i).val.obj (op V))
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj (op V))
    (b : (integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange g).obj V)))
    (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj
      (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange g).obj V))),
    (((d.app P).app (op n)).f i).val.app
        (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange g).obj V))
      (completedScalarTensorSection l E L ι X
        (((integralOperationsPullbackLevel l E g n).obj P).X i)
        (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange g).obj V)) s
        (scalarPullbackGenerator l E g n P i V p a b)) =
      scalarPullbackGenerator l L g n
        ((completedOrdinaryScalarComplex l E L ι Y).obj P) i V
        (completedScalarTensorSection l E L ι Y (P.X i) (op V) 1 p)
        ((integralScalarQuotientSheafMap l E L ι Y n).hom.app (op V) a)
        (((integralScalarQuotientSheafMap l E L ι X n).hom.app
          (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange g).obj V)) b) *
          (completedIntegralCommRingProjectionUnrestricted l L X n).hom.app
            (op ((AlgebraicGeometry.Scheme.proEtaleBaseChange g).obj V)) s)

/-- The two-coordinate normalization of tensor/Roos comparison. The first coordinate
has degree i and the shifted coordinate degree i-1 in the mapping-cocone convention.
Source: Stacks 014E, 08TC
(blueprint: lem-weil-scalar-pullback-strict-cone-naturality). -/
def ScalarPullbackConeFormula {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y)
    (κ : integralOperationsPullbackComplexFunctor l E g ⋙
        completedOrdinaryScalarComplex l E L ι X ≅
      scalarPullbackSourceTower l E L ι g ⋙ integralOperationsRoosFunctor) : Prop :=
  ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ),
    ((κ.hom.app P).f i ≫ (CochainComplex.mappingCocone.fst
      (scalarPullbackRoosEnd l L X
        ((scalarPullbackSourceTower l E L ι g).obj P))).f i =
      (completedOrdinaryScalarExtension l E L ι X).map
        ((CochainComplex.mappingCocone.fst (scalarPullbackRoosEnd l E X
          ((integralOperationsPullbackTowerFunctor l E g).obj P))).f i) ≫
        (scalarPullbackProductMap l E L ι X
          (fun n ↦ ((integralOperationsPullbackTowerFunctor l E g).obj P).obj (op n))).f i) ∧
    ((κ.hom.app P).f i ≫ (CochainComplex.mappingCocone.snd
      (scalarPullbackRoosEnd l L X
        ((scalarPullbackSourceTower l E L ι g).obj P))).v i (i - 1) (by omega) =
      (completedOrdinaryScalarExtension l E L ι X).map
        ((CochainComplex.mappingCocone.snd (scalarPullbackRoosEnd l E X
          ((integralOperationsPullbackTowerFunctor l E g).obj P))).v i (i - 1) (by omega)) ≫
        (scalarPullbackProductMap l E L ι X
          (fun n ↦ ((integralOperationsPullbackTowerFunctor l E g).obj P).obj (op n))).f
            (i - 1))

/-- The induced chain map, using the fixed tensor/Roos comparison and the strict
map on both cone coordinates.
Source: Stacks 014E, 08TC
(blueprint: lem-weil-scalar-pullback-strict-cone-naturality). -/
def scalarPullbackConeMap {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y)
    (d : scalarPullbackSourceTower l E L ι g ⟶ scalarPullbackTargetTower l E L ι g)
    (κ : integralOperationsPullbackComplexFunctor l E g ⋙
        completedOrdinaryScalarComplex l E L ι X ≅
      scalarPullbackSourceTower l E L ι g ⋙ integralOperationsRoosFunctor) :
    integralOperationsPullbackComplexFunctor l E g ⋙
        completedOrdinaryScalarComplex l E L ι X ⟶
      completedOrdinaryScalarComplex l E L ι Y ⋙
        integralOperationsPullbackComplexFunctor l L g :=
  κ.hom ≫ Functor.whiskerRight d integralOperationsRoosFunctor

/-- The normalized representative equation for the derived transformation. The
universal scalar counit on A_E(P) is used even though that cone need not be K-flat.
Source: Stacks 06YT, 04VG
(blueprint: lem-weil-scalar-pullback-strict-cone-naturality). -/
def ScalarPullbackDescentFormula {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y)
    (δ : integralOperationsPullbackComplexFunctor l E g ⋙
        completedOrdinaryScalarComplex l E L ι X ⟶
      completedOrdinaryScalarComplex l E L ι Y ⋙
        integralOperationsPullbackComplexFunctor l L g)
    (τ : integralDerivedPullback l E g ⋙ completedDerivedScalarExtension l E L ι X ⟶
      completedDerivedScalarExtension l E L ι Y ⋙ integralDerivedPullback l L g) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hQ : integralOperationsGoodComplex l L Y
      ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj)),
    τ.app (DerivedCategory.Q.obj P.obj) ≫
        (integralDerivedPullback l L g).map (completedScalarCounit l E L ι Y P.obj) ≫
        (integralDerivedPullbackComparison l L g).hom.app
          ⟨(completedOrdinaryScalarComplex l E L ι Y).obj P.obj, hQ⟩ =
      (completedDerivedScalarExtension l E L ι X).map
        ((integralDerivedPullbackComparison l E g).hom.app P) ≫
        completedScalarCounit l E L ι X
          ((integralOperationsPullbackComplexFunctor l E g).obj P.obj) ≫
        DerivedCategory.Q.map (δ.app P.obj)

/-- The strict and derived maps together with their full normalization conditions.
This bundles the witnesses of the single theorem; it assumes no comparison maps.
Source: Bhatt--Scholze 3.4.10, 3.5.1, 6.5.9(4); Stacks 03EK, 014E, 04VG
(blueprint: lem-weil-scalar-pullback-strict-cone-naturality). -/
structure ScalarPullbackStrictConeData {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y) where
  /-- A chain-natural map of strict towers. -/
  level : scalarPullbackSourceTower l E L ι g ⟶ scalarPullbackTargetTower l E L ι g
  /-- Its balanced local generator formula, including both coefficient scalars. -/
  generator : ScalarPullbackGeneratorFormula l E L ι g level
  /-- The basis-independent tensor/Roos comparison. -/
  cone : integralOperationsPullbackComplexFunctor l E g ⋙
      completedOrdinaryScalarComplex l E L ι X ≅
    scalarPullbackSourceTower l E L ι g ⋙ integralOperationsRoosFunctor
  /-- Both cone coordinates are the canonical tensor/product map. -/
  coordinates : ScalarPullbackConeFormula l E L ι g cone
  /-- The transformation on the entire derived category. -/
  derived : integralDerivedPullback l E g ⋙ completedDerivedScalarExtension l E L ι X ⟶
    completedDerivedScalarExtension l E L ι Y ⋙ integralDerivedPullback l L g
  /-- Its representative is exactly the diagonal strict cone map. -/
  descends : ScalarPullbackDescentFormula l E L ι g
    (scalarPullbackConeMap l E L ι g level cone) derived

/-- Normalization of ordinary tensor association by multiplication of its scalar factors.
This condition specifies the canonical associator, without choosing a basis or resolution.
Source: Stacks 03EK (blueprint: lem-weil-scalar-pullback-strict-cone-naturality). -/
def ScalarPullbackAssociationFormula
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{t})
    (α : completedOrdinaryScalarComplex l E L ι W ⋙
        completedOrdinaryScalarComplex l L F j W ≅
      completedOrdinaryScalarComplex l E F (j.comp ι) W) : Prop :=
  ∀ (P : CochainComplex (integralTowerModules l E W) ℤ) (i : ℤ) (U : W.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
    (z : (completedIntegralCommRingSheafUnrestricted l F W).obj.obj U)
    (p : (P.X i).val.obj U),
    ((α.hom.app P).f i).val.app U
      (completedScalarTensorSection l L F j W _ U z
        (completedScalarTensorSection l E L ι W (P.X i) U s p)) =
      completedScalarTensorSection l E F (j.comp ι) W (P.X i) U
        ((completedCoefficientMap l L F j W).hom.app U s * z) p

/-- Composition of the specified level and cone maps after the canonical tensor
associators. Existence with the scalar multiplication normalization is included;
there is no unspecified comparison map in this condition.
Source: Stacks 03EK, 014E
(blueprint: lem-weil-scalar-pullback-strict-cone-naturality). -/
def ScalarPullbackCompositionFormula {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y)
    (D : ScalarPullbackStrictConeData l E L ι g) : Prop :=
  ∀ (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (j : L →ₐ[ℚ_[l]] F)
    (D' : ScalarPullbackStrictConeData l L F j g)
    (D'' : ScalarPullbackStrictConeData l E F (j.comp ι) g),
    ∃ (αX : completedOrdinaryScalarComplex l E L ι X ⋙
          completedOrdinaryScalarComplex l L F j X ≅
        completedOrdinaryScalarComplex l E F (j.comp ι) X)
      (αY : completedOrdinaryScalarComplex l E L ι Y ⋙
          completedOrdinaryScalarComplex l L F j Y ≅
        completedOrdinaryScalarComplex l E F (j.comp ι) Y),
      ScalarPullbackAssociationFormula l E L ι F j X αX ∧
      ScalarPullbackAssociationFormula l E L ι F j Y αY ∧
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ),
        (completedOrdinaryScalarComplex l L F j X).map ((D.level.app P).app (op n)) ≫
          (D'.level.app ((completedOrdinaryScalarComplex l E L ι Y).obj P)).app (op n) ≫
          (integralOperationsPullbackLevel l F g n).map (αY.hom.app P) =
        αX.hom.app ((integralOperationsPullbackLevel l E g n).obj P) ≫
          (D''.level.app P).app (op n)) ∧
      (∀ P : CochainComplex (integralTowerModules l E Y) ℤ,
        (completedOrdinaryScalarComplex l L F j X).map
            ((scalarPullbackConeMap l E L ι g D.level D.cone).app P) ≫
          (scalarPullbackConeMap l L F j g D'.level D'.cone).app
            ((completedOrdinaryScalarComplex l E L ι Y).obj P) ≫
          (integralOperationsPullbackComplexFunctor l F g).map (αY.hom.app P) =
        αX.hom.app ((integralOperationsPullbackComplexFunctor l E g).obj P) ≫
          (scalarPullbackConeMap l E F (j.comp ι) g D''.level D''.cone).app P)

/-- The identity extension gives the identity on each level and on the entire cone,
under the published tensor multiplication unitors on source and target.
Source: Stacks 03EK, 014E
(blueprint: lem-weil-scalar-pullback-strict-cone-naturality). -/
def ScalarPullbackUnitFormula {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y)
    (D : ScalarPullbackStrictConeData l E E (AlgHom.id ℚ_[l] E) g) : Prop :=
  (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ),
    (D.level.app P).app (op n) ≫ (integralOperationsPullbackLevel l E g n).map
        ((completedScalarIdentityMultiplication l E Y).hom.app P) =
      (completedScalarIdentityMultiplication l E X).hom.app
        ((integralOperationsPullbackLevel l E g n).obj P)) ∧
  (∀ P : CochainComplex (integralTowerModules l E Y) ℤ,
    (scalarPullbackConeMap l E E (AlgHom.id ℚ_[l] E) g D.level D.cone).app P ≫
        (integralOperationsPullbackComplexFunctor l E g).map
          ((completedScalarIdentityMultiplication l E Y).hom.app P) =
      (completedScalarIdentityMultiplication l E X).hom.app
        ((integralOperationsPullbackComplexFunctor l E g).obj P))

/-- Strict scalar/pullback cone naturality, with unique normalized witnesses.
Source: Bhatt--Scholze 3.4.10, 3.5.1 and 6.5.9(4); Stacks 03EK, 014E, 06YS,
06YT, 0G7E and 04VG
(blueprint: lem-weil-scalar-pullback-strict-cone-naturality).
Proof:
1. The coefficient limit map has the prescribed residues. The inverse-image coefficient
square commutes because both adjoints send constants to the same constants.
2. Check the inner tensor balance, the inverse-image coefficient balance, and the
outer completed-scalar balance. Sheafification gives the unique generator map.
3. Applying a differential, a chain map, or a quotient transition gives the same
formula on each local generator. Thus these maps form a natural strict tower map.
4. A finite free basis of S over R gives the inverse to the canonical product map
by a finite sum of coordinate products. Its forward map uses only projections,
so the isomorphism is independent of the basis, natural, and valid unboundedly.
5. The product comparison commutes with 1-s. Tensor preserves the binary sums
and shifts of the cone, so it gives the specified cone isomorphism. The strict
map is diagonal on its two coordinates, commuting with (-dy-(1-s)x,dx).
6. Resolve a complex representing K by a flat-term K-flat P. Change of rings
makes Q flat-term K-flat, and the recorded integral comparisons compute pullback.
7. Finite freeness makes ordinary tensor exact on every complex, including A_E(P),
so its universal derived counit is invertible there without assuming that cone K-flat.
8. Strict Roos homotopy functoriality gives homotopy naturality; both functors invert
quasi-isomorphisms on the resolving class by the integral invariance theorem.
9. Localize flat-term K-flat representatives, then use fully faithful localization
precomposition to descend this natural transformation. The displayed counit equation
fixes its components uniquely, proves resolution independence, and gives naturality
also for inverse quasi-isomorphisms and therefore every derived morphism.
10. For a tower E,L,F, the quotient inclusions compose; the two successive generator
formulas multiply the scalar factors exactly as the tensor associator does. Products
respect that associator by their projections, hence so do both cone coordinates.
The identity inclusion gives multiplication, namely the tensor unit identification.
11. The canonical derived associators are localizations of these ordinary associators
on K-flat models. Faithfulness of the resolving localization extends coherence and
the unit identity to all derived objects. -/
theorem scalarPullbackStrictConeNaturality
    {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y)
    (_hX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hY : ∀ y : Y, IsUnit (l : Y.residueField y)) :
    (∀ K : ℕ → CochainComplex (integralTowerModules l E X) ℤ,
      IsIso (scalarPullbackProductMap l E L ι X K)) ∧
    (∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      integralOperationsGoodComplex l L Y
        ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj)) ∧
    (∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
      IsIso (completedScalarCounit l E L ι X
        ((integralOperationsPullbackComplexFunctor l E g).obj P.obj))) ∧
    Nonempty (ScalarPullbackStrictConeData l E L ι g) ∧
    Subsingleton (ScalarPullbackStrictConeData l E L ι g) ∧
    (∀ D : ScalarPullbackStrictConeData l E L ι g,
      ScalarPullbackCompositionFormula l E L ι g D) ∧
    (∀ D : ScalarPullbackStrictConeData l E E (AlgHom.id ℚ_[l] E) g,
      ScalarPullbackUnitFormula l E g D) := by
  sorry

end WeilConjectures
