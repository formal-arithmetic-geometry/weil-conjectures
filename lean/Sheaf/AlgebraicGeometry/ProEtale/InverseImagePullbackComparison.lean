/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.Paper.IntegralDerivedOperations
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.CompletedIntegralCoefficientGerm

/-!
# Inverse image to finite and completed derived pullback

Source: Stacks Project, Tags 03D6 and 08TC; Bhatt--Scholze, Section 6.5
(blueprint: def-weil-inverse-image-pullback-comparison).

Inverse image is expressed in its canonical sectionwise model for an isomorphism.
All coefficient sheaves, finite reductions, pullbacks, transitions, and the Roos
complex are the recorded constructions. A map chosen below has a unique prescribed
value on every section; no arbitrary comparison or cone is supplied as data.
The index n denotes positive exponent n+1. The integral definition takes precisely
the good representative and resolution used to evaluate the recorded completed pullback.

## Main definitions

- `inverseImageCompletedCoefficientMap`: limit lift of the actual finite structure maps.
- `inverseImageFiniteDerived`, `inverseImageIntegralDerived`: exact module inverse images.
- `inverseImagePullbackComparisonFinite`: the sheafified finite tensor-unit map.
- `inverseImagePullbackComparisonFiniteIntrinsic`: its recorded intrinsic presentation.
- `inverseImageRoosComparisonComplex`: the compatible reductions with zero homotopy.
- `inverseImagePullbackComparison`: the integral map for the chosen resolution.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- The coefficient-sized pullback is the recorded intrinsic finite pullback,
with the canonical unit-preserving identification of left adjoints. This comparison
uses the same constant-section direct image on both sides.
Source: Stacks Tags 03D2 and 00YV
(blueprint: def-weil-inverse-image-pullback-comparison). -/
def inverseImageFiniteIntrinsicPullbackComparison {S T : Scheme.{t}} (f : S ⟶ T)
    (A : Type t) [CommRing A] [Finite A] :
    coefficientProEtaleModulePullback.{t, t} f (CommRingCat.of (ULift.{t + 1, t} A)) ≅
      sfIntrinsicPullback A f :=
  (coefficientProEtaleModuleAdjunction.{t, t} f
    (CommRingCat.of (ULift.{t + 1, t} A))).leftAdjointUniq
      (sfIntrinsicConstantModuleAdjunction f A)

/-- The standard localization at quasi-isomorphisms for finite coefficient sheaves.
Source: Stacks Tag 05RU (blueprint: def-weil-inverse-image-pullback-comparison). -/
instance inverseImageCoefficient_hasDerived (W : Scheme.{t})
    (R : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}) :
    HasDerivedCategory (SheafOfModules.{max u (t + 1)} R) :=
  HasDerivedCategory.standard _

/-- The finite constant coefficient structure map, in the sectionwise inverse-image model.
Source: Stacks Tag 03D6 (blueprint: def-weil-inverse-image-pullback-comparison). -/
abbrev inverseImageFiniteCoefficientMap (n : ℕ) :=
  isoSectionwiseConstantMap g
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))

/-- The prescribed components of the completed structure map are inverse images of
limit projections followed by the constant-section comparison.
Source: Stacks Tags 03CO and 03D6
(blueprint: def-weil-inverse-image-pullback-comparison). -/
def inverseImageCompletedCoefficientComponent (n : ℕ) :=
  (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
      (limit.π (integralCoefficientSheafSystem l E Y) (op n)) ≫
    inverseImageFiniteCoefficientMap l E g n

/-- The prescribed components commute with every coefficient reduction.
Source: Stacks Tags 03CO and 0H7J
(blueprint: def-weil-inverse-image-pullback-comparison).
Proof: limit projections commute with the quotient transitions. Constant-section
comparisons are natural in ring maps: both composites extend the same coefficient
map on constant presheaves. Apply inverse-image functoriality and these equations. -/
theorem inverseImageCompletedCoefficientComponent_naturality {a b : ℕᵒᵖ} (f : a ⟶ b) :
    inverseImageCompletedCoefficientComponent l E g a.unop ≫
        (integralCoefficientSheafSystem l E X).map f =
      inverseImageCompletedCoefficientComponent l E g b.unop := by
  sorry

/-- The completed structure map is the actual limit lift of its finite components.
Source: Stacks Tag 03CO; Bhatt--Scholze, Section 6.5
(blueprint: def-weil-inverse-image-pullback-comparison). -/
def inverseImageCompletedCoefficientMap :
    (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).obj
      (completedIntegralCoefficientSheafUnrestricted l E Y) ⟶
        completedIntegralCoefficientSheafUnrestricted l E X :=
  limit.lift (integralCoefficientSheafSystem l E X)
    { pt := (isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).obj
        (completedIntegralCoefficientSheafUnrestricted l E Y)
      π := { app n := inverseImageCompletedCoefficientComponent l E g n.unop
             naturality _ _ f := (Category.id_comp _).trans
               (inverseImageCompletedCoefficientComponent_naturality l E g f).symm } }

/-- The completed coefficient map is an isomorphism, without a completeness
hypothesis on any module.
Source: Stacks Tags 09A5, 00WX and 03CO
(blueprint: def-weil-inverse-image-pullback-comparison).
Proof: the site equivalence preserves the coefficient limit. Each finite structure
map is invertible by the constant-section normalization. The induced map on limits
is invertible and its projection equations identify it with the displayed limit lift. -/
@[instance] theorem inverseImageCompletedCoefficientMap_isIso :
    IsIso (inverseImageCompletedCoefficientMap l E g) := by
  sorry

/-- Finite inverse image, with action a acting through c_A inverse(a).
Source: Stacks Tag 03D6 (blueprint: def-weil-inverse-image-pullback-comparison). -/
abbrev inverseImageFiniteModules (n : ℕ) :
    integralOperationsFiniteModules l E Y n ⥤ integralOperationsFiniteModules l E X n :=
  isoSectionwiseModuleInverseImage g (inverseImageFiniteCoefficientMap l E g n)

/-- Completed-coefficient inverse image, with the action transported through the
inverse of the constructed limit coefficient map.
Source: Stacks Tag 03D6 (blueprint: def-weil-inverse-image-pullback-comparison). -/
abbrev inverseImageIntegralModules : integralTowerModules l E Y ⥤ integralTowerModules l E X :=
  isoSectionwiseModuleInverseImage g (inverseImageCompletedCoefficientMap l E g)

/-- Exact inverse image descends termwise to the unbounded finite derived category.
Source: Stacks Tag 05RU (blueprint: def-weil-inverse-image-pullback-comparison). -/
abbrev inverseImageFiniteDerived (n : ℕ) :=
  (inverseImageFiniteModules l E g n).mapDerivedCategory

/-- Exact inverse image descends termwise to the entire completed-coefficient derived
category; no derived-completeness or constructibility condition is imposed.
Source: Stacks Tag 05RU (blueprint: def-weil-inverse-image-pullback-comparison). -/
abbrev inverseImageIntegralDerived := (inverseImageIntegralModules l E g).mapDerivedCategory

/-- The finite pullback is exact in the canonical coefficient-sized presentation.
Source: Stacks Tags 03D6 and 04JC
(blueprint: def-weil-inverse-image-pullback-comparison).
Proof: module inverse image has exact underlying abelian inverse image. The coefficient
map is an isomorphism, so tensor extension transports its action without changing
kernels or cokernels. This also identifies the normalized adjunction pullback used
by integralOperationsLevelPullback with the sheafified tensor construction. -/
theorem inverseImageFinitePullback_exact (n : ℕ) :
    PreservesFiniteLimits (integralOperationsLevelPullback l E g n) ∧
      PreservesFiniteColimits (integralOperationsLevelPullback l E g n) := by
  sorry

/-- Left exactness of the recorded finite tensor pullback.
Source: Stacks Tag 04JC (blueprint: def-weil-inverse-image-pullback-comparison). -/
instance inverseImageFinitePullback_limits (n : ℕ) :
    PreservesFiniteLimits (integralOperationsLevelPullback l E g n) :=
  (inverseImageFinitePullback_exact l E g n).1

/-- Right exactness of the recorded finite tensor pullback.
Source: Stacks Tag 04JC (blueprint: def-weil-inverse-image-pullback-comparison). -/
instance inverseImageFinitePullback_colimits (n : ℕ) :
    PreservesFiniteColimits (integralOperationsLevelPullback l E g n) :=
  (inverseImageFinitePullback_exact l E g n).2

/-- The finite comparison is uniquely specified on every inverse-image section.
The adjunction unit is the sheafified generator x tensor 1; restriction along the
canonical comma arrow evaluates that generator at U.
Source: Stacks Tag 03D6 (blueprint: def-weil-inverse-image-pullback-comparison).
Proof: the unit followed by this restriction is the inverse-image coprojection
followed by the tensor unit. Restrictions commute with x tensor 1. The transported
action gives c_A inverse(a)x tensor 1 = x tensor a, proving linearity. The maps commute
with differentials and hence form a chain map. Values on every section determine
that chain map uniquely. This is the canonical sectionwise model of clause (a). -/
theorem inverseImageFiniteComparison_existsUnique (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ) :
    ∃! f : ((inverseImageFiniteModules l E g n).mapHomologicalComplex (.up ℤ)).obj K ⟶
        ((integralOperationsLevelPullback l E g n).mapHomologicalComplex (.up ℤ)).obj K,
      ∀ (i : ℤ) (U : X.ProEt)
        (x : (K.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (f.f i).val.app (op U) x =
          (((integralOperationsLevelPullback l E g n).obj (K.X i)).val.map
            (proEtaleIsoCommaArrow g U).op)
            (integralOperationsPullbackGenerator l E g n (K.X i)
              ((proEtaleIsoPostcompose g).obj U) x) := by
  sorry

/-- The actual finite comparison chain map, uniquely fixed on every section.
Source: Stacks Tag 03D6 (blueprint: def-weil-inverse-image-pullback-comparison). -/
def inverseImageFiniteComparisonComplex (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ) :=
  (inverseImageFiniteComparison_existsUnique l E g n K).exists.choose

/-- Finite comparison in the derived category: the class of the sheafified tensor-unit
chain map, with the canonical exact-functor localization comparisons on both sides.
Source: Stacks Tag 03D6 (blueprint: def-weil-inverse-image-pullback-comparison). -/
def inverseImagePullbackComparisonFinite
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ) :
    (inverseImageFiniteDerived l E g n).obj (DerivedCategory.Q.obj K) ⟶
      (integralOperationsLevelPullback l E g n).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K) :=
  (inverseImageFiniteModules l E g n).mapDerivedCategoryFactors.hom.app K ≫
    DerivedCategory.Q.map (inverseImageFiniteComparisonComplex l E g n K) ≫
      (integralOperationsLevelPullback l E g n).mapDerivedCategoryFactors.inv.app K

/-- In the recorded finite intrinsic presentation, the same comparison has exactly
finiteDerivedPullback as its target. The adjunction comparison preserves x tensor 1.
Source: Stacks Tags 03D6 and 00YV
(blueprint: def-weil-inverse-image-pullback-comparison). -/
def inverseImagePullbackComparisonFiniteIntrinsic
    (F : Type t) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l F Y n) ℤ) :
    (inverseImageFiniteDerived l F g n).obj (DerivedCategory.Q.obj K) ⟶
      (finiteDerivedPullback l F n g).obj (DerivedCategory.Q.obj K) :=
  letI : Finite (Padic.coefficientExtensionRing l F (n + 1)) :=
    Padic.finite_coefficientExtensionRing l F (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  let e : integralOperationsLevelPullback l F g n ≅
      sfIntrinsicPullback (Padic.coefficientExtensionRing l F (n + 1)) g :=
    inverseImageFiniteIntrinsicPullbackComparison g (Padic.coefficientExtensionRing l F (n + 1))
  inverseImagePullbackComparisonFinite l F g hX hY n K ≫
    (Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj K)

/-- The compatible integral-to-finite maps are uniquely specified on every section:
reduce x to 1 tensor x, apply the finite pullback unit, and restrict along the
canonical comma arrow. The target is exactly the recorded restricted finite pullback.
Source: Stacks Tags 03D6 and 08TC; Bhatt--Scholze, Section 6.5
(blueprint: def-weil-inverse-image-pullback-comparison).
Proof: reduction is the sheafified map x to 1 tensor x. Compose its inverse image
with the finite comparison of clause (a). The coefficient projection equation for
c_O makes this completed-linear. Restrictions and differentials commute with the
unit and reduction maps, so this is a chain map. The displayed values specify its
value on every section in the site-equivalence model, giving uniqueness. -/
theorem inverseImageReductionTheta_existsUnique (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ∃! f : ((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).obj P ⟶
        (integralOperationsPullbackLevel l E g n).obj P,
      ∀ (i : ℤ) (U : X.ProEt)
        (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (f.f i).val.app (op U) x =
          (((integralOperationsPullbackLevel l E g n).obj P).X i).val.map
            (proEtaleIsoCommaArrow g U).op
            (integralOperationsPullbackGenerator l E g n
              (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i)
              ((proEtaleIsoPostcompose g).obj U)
              (unrestrictedIntegralTensorSection l E Y n (P.X i)
                (op ((proEtaleIsoPostcompose g).obj U)) 1 x)) := by
  sorry

/-- The canonical theta_n, fixed by reduction and the finite pullback unit.
Source: Stacks Tags 03D6 and 08TC
(blueprint: def-weil-inverse-image-pullback-comparison). -/
def inverseImageReductionTheta (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :=
  (inverseImageReductionTheta_existsUnique l E g n P).exists.choose

/-- The theta maps commute strictly with every consecutive reduction.
Source: Stacks Tags 03D6 and 08TC
(blueprint: def-weil-inverse-image-pullback-comparison).
Proof: on sections, quotient reduction carries 1 tensor x to 1 tensor x. The recorded
pullback transition carries its unit generator to that same generator at the next
quotient. Restriction along the comma arrow commutes with this transition. The
normalization of theta on all sections gives the equality of chain maps. -/
theorem inverseImageReductionTheta_compatible (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    inverseImageReductionTheta l E g (n + 1) P ≫
        (integralOperationsPullbackTransition l E g n).app P =
      inverseImageReductionTheta l E g n P := by
  sorry

/-- The product of the actual theta maps.
Source: Stacks Tag 08TC (blueprint: def-weil-inverse-image-pullback-comparison). -/
def inverseImageReductionProduct (P : CochainComplex (integralTowerModules l E Y) ℤ) :=
  Pi.lift (fun n ↦ inverseImageReductionTheta l E g n P)

/-- Strict compatibility gives the zero-homotopy equation for the Roos lift.
Source: Stacks Tag 08TC (blueprint: def-weil-inverse-image-pullback-comparison).
Proof: after the nth product projection, theta followed by 1-s is theta_n minus
(theta_(n+1) followed by t_n), zero by strict compatibility. Product extensionality
makes this composite zero. The differential of the zero cochain is zero, yielding
exactly the mappingCocone.lift equation. -/
theorem inverseImageReductionProduct_lift_condition
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain
          (((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).obj P)
          (∏ᶜ fun n ↦ (integralOperationsPullbackLevel l E g n).obj P) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (inverseImageReductionProduct l E g P ≫
          towerTransitionEndomorphism
            (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l E g).obj P))) =
      0 := by
  sorry

/-- The concrete shifted-cone map z to (0, (theta_n(z))_n), using zero homotopy.
Its target is the existing strict Roos complex, with its actual differential.
Source: Stacks Tag 08TC (blueprint: def-weil-inverse-image-pullback-comparison). -/
def inverseImageRoosComparisonComplex
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).obj P ⟶
      (integralOperationsPullbackComplexFunctor l E g).obj P :=
  CochainComplex.mappingCocone.lift _ (inverseImageReductionProduct l E g P) 0
    (inverseImageReductionProduct_lift_condition l E g P)

/-- The inverse-image resolution is invertible after localization.
Source: Stacks Tag 05RU (blueprint: def-weil-inverse-image-pullback-comparison).
Proof: exact inverse image preserves the kernels, images and quotients defining
cohomology. It therefore preserves the quasi-isomorphism q. Localization sends
this inverse-image quasi-isomorphism to an isomorphism. -/
@[instance] theorem inverseImageResolution_isIso
    (K : CochainComplex (integralTowerModules l E Y) ℤ)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (q : P.obj ⟶ K) [QuasiIso q] :
    IsIso (DerivedCategory.Q.map
      (((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).map q)) := by
  sorry

/-- The completed comparison for the chosen K-flat flat-term resolution q:P to K.
Compose the inverse of inverse-image(q), the explicit zero-homotopy Roos lift,
and the recorded representative identification with completed derived pullback.
This defines the map on the entire ambient category. Naturality, independence of
resolution and invertibility on constructible complete objects are separate assertions.
Source: Stacks Tags 03D6 and 08TC; Bhatt--Scholze, Section 6.5
(blueprint: def-weil-inverse-image-pullback-comparison). -/
def inverseImagePullbackComparison
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : CochainComplex (integralTowerModules l E Y) ℤ)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (q : P.obj ⟶ K) [QuasiIso q] :
    (inverseImageIntegralDerived l E g).obj (DerivedCategory.Q.obj K) ⟶
      (integralDerivedPullback l E g).obj (DerivedCategory.Q.obj K) :=
  (inverseImageIntegralModules l E g).mapDerivedCategoryFactors.hom.app K ≫
    inv (DerivedCategory.Q.map
      (((inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)).map q)) ≫
    DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E g P.obj) ≫
    (integralDerivedPullbackComparison l E g).inv.app P ≫
    (integralDerivedPullback l E g).map (DerivedCategory.Q.map q)

end AlgebraicGeometry.ProEtale
