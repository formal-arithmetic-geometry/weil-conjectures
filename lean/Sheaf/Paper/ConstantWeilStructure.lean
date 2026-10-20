/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.IsomorphismDerivedPullback
public import Sheaf.Paper.SfWeilSheafComplex
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.Paper.SfConstructibleHeart

/-! # Canonical Weil structure on constant coefficients

Source: Weil blueprint, ordinary compact cohomology, order 1510, coefficient paragraph;
Bhatt--Scholze, Sections 3.5 and 6.5
(blueprint: def-weil-constant-weil-structure).

Finite coefficients use the constant-section inverse-image map. The integral map is its
inverse limit. The derived normalization is fixed on the regular K-flat representative:
the inverse structure map is the compatible unit into the strict finite-pullback Roos
complex, with zero shifted-cone component. Thus no arbitrary derived isomorphism is chosen.
The natural number n denotes the positive coefficient exponent n+1 throughout.

## Main definitions

- `constantWeilFiniteComparison` and `constantWeilIntegralComparison`: canonical ring maps.
- `constantWeilIntegralLambda` and `constantWeilIntegralTheta`: normalized derived structure.
- `constantWeilRationalSheaf`: the rational constant Weil sheaf.
- `constantWeilAlgebraicallyClosedSheaf`: the literal least-stage constant Weil sheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme CategoryTheory.Endofunctor
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Finite coefficient comparison: exactly the adjoint of the constant-section map.
Source: blueprint order 1510, clause 1 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilFiniteComparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (n : ℕ) :=
  proEtaleIsoConstantRingComparison g
    (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))

/-- The actual quotient reduction on finite constant commutative-ring sheaves.
Source: blueprint order 1510, clause 1 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilCoefficientReduction (Y : Scheme.{u}) (n : ℕ) :=
  (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (n + 1)).comp
          (ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).toRingHom)))

/-- Reductions commute with the specified finite comparisons.
Source: blueprint order 1510, clause 1 (blueprint: def-weil-constant-weil-structure).
Proof: apply the coefficient naturality in lem-weil-proetale-isomorphism-inverse-image
to the actual quotient transition. Both adjoints send every coefficient to the same
constant section, so the two composites agree, including exponent one. -/
theorem constantWeilFiniteComparison_reduction {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    (constantWeilFiniteComparison l E g (n + 1)).hom ≫
        constantWeilCoefficientReduction l E X n =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
          (constantWeilCoefficientReduction l E Y n) ≫
        (constantWeilFiniteComparison l E g n).hom := by
  exact (proEtaleIso_constantComparison g CommRingCat.{u + 1}).2 _ _ _

/-- The completed integral comparison, uniquely fixed by all finite projections.
Its defining projection equations are exactly limit(c_n) after the inverse-limit comparison.
Source: blueprint order 1510, clause 2 (blueprint: def-weil-constant-weil-structure). -/
abbrev constantWeilIntegralComparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  isomorphismCompletedCoefficientComparison l E g

/-- The actual regular coefficient complex, before derived localization.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilIntegralComplex (Y : Scheme.{u}) :=
  (CochainComplex.singleFunctor (integralTowerModules l E Y) 0).obj
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))

/-- The regular coefficient complex is a permitted K-flat representative with flat terms.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure).
Proof: its only nonzero term is the regular module. Tensoring with it is naturally the
identity on complexes, so it preserves acyclicity. The regular module is flat, and all
other terms are zero and flat. This proves both clauses of integralOperationsGoodComplex. -/
theorem constantWeilIntegralComplex_good (Y : Scheme.{u}) :
    integralOperationsGoodComplex l E Y (constantWeilIntegralComplex l E Y) := by
  sorry

/-- The specified good representative; only its K-flatness proof is postponed.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilIntegralGood (Y : Scheme.{u}) :
    (integralOperationsGoodComplex l E Y).FullSubcategory :=
  ⟨constantWeilIntegralComplex l E Y, constantWeilIntegralComplex_good l E Y⟩

/-- The strict pullback tower of the actual regular representative.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilPullbackTower {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  (integralOperationsPullbackTowerFunctor l E g).obj (constantWeilIntegralComplex l E Y)

/-- The actual 1-shift endomorphism of the product in the pullback Roos complex.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilPullbackRoosEndomorphism {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  towerTransitionEndomorphism
    (K := fun n ↦ (constantWeilPullbackTower l E g).obj (op n))
    (integralOperationsTowerStep (constantWeilPullbackTower l E g))

/-- The section one in degree zero of the single regular complex.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilUnitSection (Y : Scheme.{u}) (V : Y.ProEt) :
    ((constantWeilIntegralComplex l E Y).X 0).val.obj (op V) :=
  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))).inv.val.app
      (op V)) (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))

/-- The image of 1 tensor 1 in degree zero of the actual finite reduction.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilReducedUnitSection (Y : Scheme.{u}) (n : ℕ) (V : Y.ProEt) :
    ((((unrestrictedIntegralFiniteComplex l E Y n).obj
      (constantWeilIntegralComplex l E Y)).X 0).val.obj (op V)) :=
  (((unrestrictedIntegralReductionFunctor l E Y n).map
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))).inv).val.app
        (op V))
    (unrestrictedIntegralTensorSection l E Y n
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) (op V) 1
      (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V)))

/-- The canonical comparison into the strict completed pullback is uniquely fixed by the
finite-level unit generators and by its zero shifted component. This is the inverse of
the desired derived structure map on the regular coefficient object.
Source: blueprint order 1510, clauses 1--3; Bhatt--Scholze, Definition 3.5.2
(blueprint: def-weil-constant-weil-structure).
Proof: at each finite level multiplication identifies reduction of the regular module
with the finite regular module, and its unit is 1 tensor 1. Apply the actual module
pullback adjunction unit. These generators are compatible with reductions by clause 1.
Their product is killed by 1-shift, so mappingCocone.lift with zero degree -1 component
gives the map. On an isomorphism, every site object is isomorphic to a base-change
object, where the prescribed generator generates the regular module. Thus the first
component is determined by the equations below. The zero second component and the two
cone projections determine the chain map uniquely. No cone filler is chosen. -/
theorem constantWeilChainUnit_existsUnique {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃! η : constantWeilIntegralComplex l E X ⟶
        (integralOperationsPullbackComplexFunctor l E g).obj
          (constantWeilIntegralComplex l E Y),
      (∀ (n : ℕ) (V : Y.ProEt),
        ((η.f 0 ≫
          (CochainComplex.mappingCocone.fst
            (constantWeilPullbackRoosEndomorphism l E g)).f 0 ≫
          (Pi.π (fun m ↦ (constantWeilPullbackTower l E g).obj (op m)) n).f 0).val.app
            (op ((proEtaleBaseChange g).obj V)))
          (constantWeilUnitSection l E X ((proEtaleBaseChange g).obj V)) =
        integralOperationsPullbackGenerator l E g n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj
            (constantWeilIntegralComplex l E Y)).X 0) V
          (constantWeilReducedUnitSection l E Y n V)) ∧
      (∀ i : ℤ, η.f i ≫
        (CochainComplex.mappingCocone.snd
          (constantWeilPullbackRoosEndomorphism l E g)).v i (i - 1) (by omega) = 0) := by
  sorry

/-- The uniquely normalized strict chain map, with real source and target complexes.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilChainUnit {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  (constantWeilChainUnit_existsUnique l E g).exists.choose

/-- The specified unit is a quasi-isomorphism.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure).
Proof: finite pullback takes the regular module to the regular module by the canonical
constant-ring comparison. The unit equations identify its tower with the finite
coefficient tower of X, with the actual quotient transitions. These are surjective
and their limit is the completed ring sheaf. Its Roos complex is therefore quasi-isomorphic
to that completed sheaf in degree zero. The normalized map above is precisely this
comparison. The empty scheme is allowed; the same calculation is vacuous there. -/
theorem constantWeilChainUnit_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    IsIso (DerivedCategory.Q.map (constantWeilChainUnit l E g)) := by
  sorry

/-- Canonical derived integral coefficient structure: invert the strict unit, then use
the specified good-representative comparison of the recorded completed derived pullback.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilIntegralRoosComparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (integralDerivedPullback l E g).obj (integralConstantCoefficientObject l E Y) ≅
      integralConstantCoefficientObject l E X :=
  (integralDerivedPullbackComparison l E g).app (constantWeilIntegralGood l E Y) ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map (constantWeilChainUnit l E g))
      (constantWeilChainUnit_isIso l E g)).symm

attribute [-instance] coefficientProEtaleModelBaseChange_isContinuous
  coefficientProEtaleModelUp_isContinuous in
/-- The regular module map induced by the completed coefficient comparison. On the small
model it is Mathlib's canonical pullback-of-unit map; transports are precomposition.
Source: blueprint order 1510, clauses 2--3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilTermwiseUnitMap {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (isomorphismTermwiseModuleInverseImage g
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (completedIntegralCommRingSheafUnrestricted l E X)
      (constantWeilIntegralComparison l E g)).obj
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) ⟶
      (SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (constantWeilIntegralComparison l E g).inv)).obj
        (SheafOfModules.unit
          ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
              (completedIntegralCommRingSheafUnrestricted l E Y)))) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (constantWeilIntegralComparison l E g).inv)).map
    ((proEtaleModuleFromModel
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (completedIntegralCommRingSheafUnrestricted l E Y)))).map
      (SheafOfModules.pullbackObjUnitToUnit
        (F := proEtaleModelBaseChange g)
        (J := proEtaleModelTopology Y) (K := proEtaleModelTopology X)
        (proEtaleModelRingUnit g (completedIntegralCommRingSheafUnrestricted l E Y))))

/-- The canonical unit map for restriction along the inverse coefficient isomorphism.
Source: blueprint order 1510, clauses 2--3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilRestrictionUnitMap {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X) ⟶
      (SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (constantWeilIntegralComparison l E g).inv)).obj
        (SheafOfModules.unit
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
              (completedIntegralCommRingSheafUnrestricted l E Y)))) :=
  let R' := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l E Y))
  (SheafOfModules.unitHomEquiv _).symm
    (PresheafOfModules.sectionsMk (fun U ↦ (1 : R'.obj.obj U))
      (fun {_ _} f ↦ map_one (R'.obj.map f).hom))

/-- The canonical module maps used for c_O_E are isomorphisms.
Source: blueprint order 1510, clauses 2--3 (blueprint: def-weil-constant-weil-structure).
Proof: on the small site models base change along an isomorphism is a final equivalence.
Mathlib's pullback-of-unit map is therefore invertible. Precomposition and restriction
preserve this. Restriction along the inverse coefficient isomorphism has inverse
restriction along the coefficient isomorphism; its unit map is sectionwise that ring
isomorphism. Both statements hold without any nonempty-site assumption. -/
theorem constantWeilTermwiseUnitMaps_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    IsIso (constantWeilTermwiseUnitMap l E g) ∧
      IsIso (constantWeilRestrictionUnitMap l E g) := by
  have : (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
      (inferInstance : WeaklyEtale g)).IsEquivalence :=
    (proEtaleIsoPostcompose_equivalence g).1
  have : (proEtaleBaseChange g).IsEquivalence :=
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
      (inferInstance : WeaklyEtale g) trivial).isEquivalence_right_of_isEquivalence_left
  have : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).isEquivalence_inverse
  have : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).isEquivalence_functor
  have : (proEtaleModelBaseChange g).IsEquivalence := by
    dsimp only [proEtaleModelBaseChange]
    infer_instance
  have : (proEtaleModelBaseChange g).Final := inferInstance
  constructor
  · unfold constantWeilTermwiseUnitMap
    infer_instance
  · let c := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (constantWeilIntegralComparison l E g)
    apply (isIso_iff_of_reflects_iso (constantWeilRestrictionUnitMap l E g)
      (SheafOfModules.toSheaf (completedIntegralCoefficientSheafUnrestricted l E X) ⋙
        sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1})).mp
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).2
    change Function.Bijective (fun x ↦ c.inv.hom.app U x * 1)
    simp only [mul_one]
    exact (ConcreteCategory.isIso_iff_bijective (c.inv.hom.app U)).1 inferInstance

/-- c_O_E on the completed regular module, with its transported coefficient action.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilTermwiseUnitIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  @asIso _ _ _ _ (constantWeilTermwiseUnitMap l E g)
      (constantWeilTermwiseUnitMaps_isIso l E g).1 ≪≫
    (@asIso _ _ _ _ (constantWeilRestrictionUnitMap l E g)
      (constantWeilTermwiseUnitMaps_isIso l E g).2).symm

/-- The coefficient comparison in the ambient derived category, via the exact single
functor comparison. Its underlying module map is the specified c_O_E.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilDerivedCoefficientComparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (isomorphismIntegralTermwiseInverseImage l E g).obj
        (integralConstantCoefficientObject l E Y) ≅ integralConstantCoefficientObject l E X :=
  ((isomorphismTermwiseModuleInverseImage g
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedIntegralCommRingSheafUnrestricted l E X)
    (constantWeilIntegralComparison l E g)).mapDerivedCategorySingleFunctor 0).app
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) ≪≫
    (DerivedCategory.singleFunctor (scalarReductionSource l E X) 0).mapIso
      (constantWeilTermwiseUnitIso l E g)

/-- The normalized derived-to-termwise comparison on the completed regular module.
The regular K-flat representative and strict Roos unit fix it, rather than bare existence
of a natural isomorphism. Multiplication by c_O_E identifies the same finite generators.
Source: blueprint order 1510, clause 3; lem-weil-isomorphism-derived-pullback
(blueprint: def-weil-constant-weil-structure). -/
def constantWeilIntegralLambda {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  constantWeilIntegralRoosComparison l E g ≪≫
    (constantWeilDerivedCoefficientComparison l E g).symm

/-- theta_O_E is c_O_E composed with the normalized derived-to-termwise comparison.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilIntegralTheta {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  constantWeilIntegralLambda l E g ≪≫ constantWeilDerivedCoefficientComparison l E g

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- The actual completed coefficient object in the intrinsic integral subcategory.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilIntegralObject (Y : Scheme.{u}) : sfIntegralConstructibleCategory l E Y :=
  ⟨integralConstantCoefficientObject l E Y,
    (integralConstantCoefficient_constructible l E Y D hl).2.1⟩

/-- E_Y is the image of the completed integral object under raw rationalization.
Source: blueprint order 1510, clause 4 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilRationalObject (Y : Scheme.{u}) : sfRationalConstructibleCategory l E Y :=
  (sfRationalConstructibleLocalization l E Y).obj (constantWeilIntegralObject l E D hl Y)

variable (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- Lift the actual integral theta to the full constructible subcategory.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilConstructibleIntegralTheta :
    (@constructibleIntegralPullback l _ E _ _ _ _ _ (D.geometricFrobenius Y₀).hom
      (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x)
      (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x)).obj
        (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left) ≅
      constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left :=
  ObjectProperty.isoMk _ (constantWeilIntegralTheta l E (D.geometricFrobenius Y₀).hom)

/-- Rational theta is exactly integral theta tensor one. The source identification is
part of the recorded rational pullback's unchanged-integral-object normalization.
Source: blueprint order 1510, clause 4 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilRationalTheta :
    (sfWeilFrobeniusPullback D l hl Y₀ E).obj
        (constantWeilRationalObject l E D hl (D.geometricFiber Y₀).left) ≅
      constantWeilRationalObject l E D hl (D.geometricFiber Y₀).left :=
  eqToIso ((@rationalDerivedPullback_existsUnique l _ E _ _ _ _ _
    (D.geometricFrobenius Y₀).hom
    (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x)
    (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x)).exists.choose_spec.2.1 _) ≪≫
      (sfRationalConstructibleLocalization l E (D.geometricFiber Y₀).left).mapIso
        (constantWeilConstructibleIntegralTheta l E D hl Y₀)

/-- The canonical E-Weil complex is the fixed pair (E_Y,theta_E).
Source: blueprint order 1510, clause 4 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilRationalComplex : sfWeilComplex D l hl Y₀ E :=
  IsoAlgebra.mk (constantWeilRationalObject l E D hl (D.geometricFiber Y₀).left)
    (constantWeilRationalTheta l E D hl Y₀)

/-- The coefficient object belongs to the constructible heart.
Source: blueprint order 1510, clause 4 (blueprint: def-weil-constant-weil-structure).
Proof: its integral representative is the completed regular module in degree zero,
constructible by lem-weil-constant-coefficient-objects-constructible. Its homology
vanishes in each nonzero degree. In both rational standard classes use that same
integral representative and the identity isomorphism. Thus it lies in their intersection. -/
theorem constantWeilRationalObject_mem_heart :
    sfRationalHeartProperty l E (D.geometricFiber Y₀).left
      (constantWeilRationalObject l E D hl (D.geometricFiber Y₀).left) := by
  constructor
  · refine ⟨constantWeilIntegralObject l E D hl _, ?_, ⟨Iso.refl _⟩⟩
    intro i hi
    change IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((DerivedCategory.singleFunctor _ 0).obj _))
    exact DerivedCategory.isZero_of_isLE _ 0 i hi
  · refine ⟨constantWeilIntegralObject l E D hl _, ?_, ⟨Iso.refl _⟩⟩
    intro i hi
    change IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((DerivedCategory.singleFunctor _ 0).obj _))
    exact DerivedCategory.isZero_of_isGE _ 0 i hi

/-- The canonical constructible E-Weil sheaf; forgetting it retains exactly E_Y.
Source: blueprint order 1510, clause 4 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilRationalSheaf : sfWeilSheaf D l hl Y₀ E :=
  ⟨constantWeilRationalComplex l E D hl Y₀, constantWeilRationalObject_mem_heart l E D hl Y₀⟩

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- At the least finite stage, the coefficient field is Q_l itself, transported by
Shrink.algEquiv. Its underlying object is the literal pair (Q_l,(Q_l)_Y).
Source: blueprint order 1510, clause 5 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilAlgebraicallyClosedComplex : sfCommonStageWeilComplex D l hl Y₀ Ω :=
  sfWeilStageObject D l hl Y₀ Ω (Padic.finiteCoefficientBase l Ω)
    (constantWeilRationalComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω (Padic.finiteCoefficientBase l Ω))
      D hl Y₀)

/-- The algebraically closed constant pair is in the common-stage constructible heart.
Source: blueprint order 1510, clause 5 (blueprint: def-weil-constant-weil-structure).
Proof: use the least finite stage and the rational constant object there as the
representative in both common-stage standard classes. The preceding heart-membership
statement supplies both classes; the pair's defining carrier is exactly its inclusion. -/
theorem constantWeilAlgebraicallyClosedObject_mem_heart :
    sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Ω
      (constantWeilAlgebraicallyClosedComplex l D hl Y₀ Ω).carrier := by
  have h := constantWeilRationalObject_mem_heart l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω (Padic.finiteCoefficientBase l Ω))
    D hl Y₀
  constructor
  · exact ⟨Padic.finiteCoefficientBase l Ω, _, h.1, ⟨Iso.refl _⟩⟩
  · exact ⟨Padic.finiteCoefficientBase l Ω, _, h.2, ⟨Iso.refl _⟩⟩

/-- The canonical algebraically closed constructible Weil sheaf at stage E=Q_l.
Forgetting the Weil structure gives exactly the coefficient pair (Q_l,(Q_l)_Y).
Source: blueprint order 1510, clause 5 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilAlgebraicallyClosedSheaf : sfCommonStageWeilSheaf D l hl Y₀ Ω :=
  ⟨constantWeilAlgebraicallyClosedComplex l D hl Y₀ Ω,
    constantWeilAlgebraicallyClosedObject_mem_heart l D hl Y₀ Ω⟩

/-- The rational forgetful functor discards exactly theta_E.
Source: blueprint order 1510, clause 4 (blueprint: def-weil-constant-weil-structure).
Proof: unfold the fixed-pair constructor and the fixed-pair forgetful functor. Its carrier
is definitionally the rationalization of the specified integral coefficient object. -/
theorem constantWeilRationalForget :
    (sfWeilForget D l hl Y₀ E).obj (constantWeilRationalComplex l E D hl Y₀) =
      constantWeilRationalObject l E D hl (D.geometricFiber Y₀).left := by
  rfl

/-- The algebraically closed forgetful functor retains precisely the literal base-stage pair.
Source: blueprint order 1510, clause 5 (blueprint: def-weil-constant-weil-structure).
Proof: the finite-stage inclusion retains its stage and its object. Unfold that inclusion,
the fixed-pair constructor and its forgetful functor. The stage is finiteCoefficientBase,
the image of Q_l in the fixed closure, with its prescribed small field model. -/
theorem constantWeilAlgebraicallyClosedForget :
    (sfCommonStageWeilForget D l hl Y₀ Ω).obj
        (constantWeilAlgebraicallyClosedComplex l D hl Y₀ Ω) =
      ⟨Padic.finiteCoefficientBase l Ω,
        constantWeilRationalObject l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
            (Padic.finiteCoefficientBase l Ω)) D hl (D.geometricFiber Y₀).left⟩ := by
  rfl

end WeilConjectures
