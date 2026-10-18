/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Sheaf.Paper.CompleteCoefficientDatum
public import Sheaf.Paper.CompletedRlimFunctor
import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.CategoryTheory.RingedToposMorphism
import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.CategoryTheory.DiagramSiteRealization
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.CategoryTheory.KInjectiveTotalDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-!
# Constant strict towers and normalized direct image

Source: Stacks, Tags 08BJ, 070K, 0940, 0941, 0A07, 06YS, 07A4 and 0B56;
agent-supplied constant-tower normalization supporting fix-lem-exchanges, Step 5
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).

The index n denotes positive exponent n+1. Quotients need not be finite sets.
All tower derived categories localize strict diagrams before evaluation.

## Main definitions

* `chi`: the canonical diagonal/direct-image natural isomorphism.
* `deltaLimit`: the inverse of the diagonal/derived-limit adjunction unit.
* `reduction` and `augmentation`: quotient-tower tensor and its canonical unit map.
* `projection`: the normalized whole-tower counit mate.

## Main statements

* `constantTowerDirectImageNormalization`: the four requested normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization

section GenericNormalization
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  {T : Type u₃} [Category.{v₃} T] [Abelian T] [HasDerivedCategory.{w₃} T]
  {U : Type u₄} [Category.{v₄} U] [Abelian U] [HasDerivedCategory.{w₄} U]

/-- The literal ordinary-square normalization on every K-injective representative.
The formula includes the exact-localization and derived-resolution comparisons.
Source: Stacks 070K (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def IsDirectImageNormalizedOnKInjectives
    (F : C ⥤ D) [F.Additive] (P : C ⥤ T) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (Q : D ⥤ U) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (H : T ⥤ U) [H.Additive]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions T]
    [P.PreservesKInjectiveComplexes]
    (e : F ⋙ Q ≅ P ⋙ H)
    (χ : F.rightDerivedFunctor ⋙ Q.mapDerivedCategory ≅
      P.mapDerivedCategory ⋙ H.rightDerivedFunctor) : Prop :=
  ∀ (J : CochainComplex C ℤ) [J.IsKInjective],
    χ.hom.app (DerivedCategory.Q.obj J) ≫
        H.rightDerivedFunctor.map (P.mapDerivedCategoryFactors.hom.app J) ≫
        (H.rightDerivedFunctorObjQIso ((P.mapHomologicalComplex (.up ℤ)).obj J)).hom =
      Q.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso J).hom ≫
        Q.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app J)

/-- The canonical pullback/reduction square at a homotopy representative. The two
counits and exact-localization factors specify the whole-tower tensor comparison.
Source: Stacks 06YY, 07A4
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def IsReductionPullAt
    (P : C ⥤ T) [P.Additive] (Q : D ⥤ U) [Q.Additive]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (H : T ⥤ U) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (RP : DerivedCategory C ⥤ DerivedCategory T)
    (RQ : DerivedCategory D ⥤ DerivedCategory U)
    (cP : DerivedCategory.Qh ⋙ RP ⟶ P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cQ : DerivedCategory.Qh ⋙ RQ ⟶ Q.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : P ⋙ H ≅ F ⋙ Q)
    (τ : RP ⋙ H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ RQ)
    (K : HomotopyCategory C (.up ℤ)) : Prop :=
  τ.hom.app (DerivedCategory.Qh.obj K) ≫
      RQ.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      cQ.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
    H.mapDerivedCategory.map (cP.app K) ≫
      H.mapDerivedCategoryFactorsh.hom.app ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app K ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ Q)) (.up ℤ)).inv.app K)

end GenericNormalization

variable (A : Type (u + 1)) [CommRing A]

/-- Exact diagonal, using the existing strict tower category.
Source: Stacks 0941 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
abbrev delta (X : Scheme.{u}) :=
  (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X).mapDerivedCategory

/-- Ordinary direct image in the same identified constant coefficients.
Source: Stacks 07A5 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
abbrev push {X Y : Scheme.{u}} (f : X ⟶ Y) := (moduleDirectImage A f).rightDerivedFunctor

/-- Ordinary exact inverse image.
Source: Stacks 03EK (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) := (modulePullback A f).mapDerivedCategory

/-- The existing unbounded derived inverse limit on the original small site.
Source: Stacks 0941 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
abbrev L (X : Scheme.{u}) := completedRlim X (coefficients A X)

/-- The canonical ordinary constant/inverse-image square, with identity components.
Source: Stacks 00YV (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def deltaPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    delta A Y ⋙ G A f ≅ pull A f ⋙ delta A X :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ (modulePullback A f)).symm ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Derived diagonal/limit adjunction, with its ordinary diagonal unit.
Source: Stacks 0941 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def deltaAdj (X : Scheme.{u}) : delta A X ⊣ L A X :=
  (constLimAdj : (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X) ⊣
    completedTowerLimit X (coefficients A X)).mapDerivedCategoryRightDerivedAdjunction

/-- The common-direct-image comparison is the conjugate of the identity-component square.
This retains the canonical comparison of Tag 0A07, including its unit normalization.
Source: Stacks 0A07 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def limitPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L A X ⋙ push A f ≅ R A f ⋙ L A Y :=
  conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f)).comp (deltaAdj A X))
    ((deltaAdj A Y).comp (adj A f)) (deltaPull A f)

/-- The exact diagonal preserves K-injectives because it is right adjoint to exact
terminal-index evaluation. Source: Stacks 08BJ
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: a map from a tower to a constant tower is uniquely determined at index zero;
all other components are its composites with the transitions to zero. This gives
an adjunction from exact evaluation to the diagonal. Transport a map from an acyclic
complex through that adjunction and use K-injectivity to null-homotope it. -/
@[instance] theorem delta_preservesKInjective (X : Scheme.{u}) :
    (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X).PreservesKInjectiveComplexes := by
  sorry

/-- The canonical derived direct-image/diagonal isomorphism. Both composition
comparisons retain their universal derived units; the middle comparison has identity
components on ordinary modules.
Source: Stacks 08BJ, 070K
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def chi {X Y : Scheme.{u}} (f : X ⟶ Y) :
    push A f ⋙ delta A Y ≅ delta A X ⋙ R A f :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso (moduleDirectImage A f)
    (Functor.const ℕᵒᵖ)).symm ≪≫
  Functor.rightDerivedFunctorNatIso (Functor.compConstIso ℕᵒᵖ (moduleDirectImage A f)) ≪≫
  Functor.rightDerivedFunctorCompIso (Functor.const ℕᵒᵖ) (towerDirectImage A f) ≪≫
  Functor.isoWhiskerRight
    (Functor.rightDerivedFunctorIsoMapDerivedCategory (Functor.const ℕᵒᵖ)) (R A f)

/-- Evaluation of a diagonal is canonically the identity.
Source: Stacks 0941 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def deltaEval (X : Scheme.{u}) (n : ℕ) : delta A X ⋙ ev A X n ≅ 𝟭 _ :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Functor.constCompEvaluationObj (D := Modules A X) (op n)) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The constant-tower unit is invertible for every unbounded complex.
Source: Stacks 0941 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: take a K-injective representative J. The diagonal of J is K-injective by
terminal-index evaluation. Its ordinary inverse limit is J, with identity cone.
The derived adjunction unit is the ordinary unit on this representative, hence is
invertible. Naturality and resolving quasi-isomorphisms give every derived object. -/
theorem deltaUnit_isIso (X : Scheme.{u}) : IsIso (deltaAdj A X).unit := by
  sorry

/-- The specified identification Rlim(delta M) = M, inverse to the canonical unit.
Source: Stacks 0941 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def deltaLimit (X : Scheme.{u}) : delta A X ⋙ L A X ≅ 𝟭 _ :=
  (@asIso _ _ _ _ (deltaAdj A X).unit (deltaUnit_isIso A X)).symm

variable {A} (I : Ideal A)

/-- The genuine quotient map of constant coefficient sheaves at positive exponent n+1.
Source: Stacks 099M (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def quotient (X : Scheme.{u}) (n : ℕ) :
    coefficients A X ⟶ coefficients (A ⧸ I ^ (n + 1)) X :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (Ideal.Quotient.mk _))

/-- The quotient transition of constant sheaves, including its coefficient action.
Source: Stacks 099M (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def quotientStep (X : Scheme.{u}) (n : ℕ) :
    coefficients (A ⧸ I ^ (n + 2)) X ⟶ coefficients (A ⧸ I ^ (n + 1)) X :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))))

/-- Ordinary tensor with a quotient, restricted back to the original coefficients.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def level (X : Scheme.{u}) (n : ℕ) : Modules A X ⥤ Modules A X :=
  reductionChange X (quotient I X n) ⋙ reductionRestrict X (quotient I X n)

/-- Quotient transitions are the unique maps on sheafified pure tensors.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: quotient maps commute with the scalar maps from A, so s tensor x maps to
q(s) tensor x by a balanced linear map. Sheafification extends it uniquely. The
formula proves compatibility with site restrictions and naturality in the module. -/
theorem step_existsUnique (X : Scheme.{u}) (n : ℕ) :
    ∃! τ : level I X (n + 1) ⟶ level I X n,
      ∀ (M : Modules A X) (U : X.ProEtᵒᵖ)
        (s : (coefficients (A ⧸ I ^ (n + 2)) X).obj.obj U) (x : M.val.obj U),
        (τ.app M).val.app U (reductionTensorSection X (quotient I X (n + 1)) M U s x) =
          reductionTensorSection X (quotient I X n) M U
            ((quotientStep I X n).hom.app U s) x := by
  sorry

/-- The strict reduction functor, including all coefficient transition maps.
Source: Stacks 099M (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def reductionModule (X : Scheme.{u}) : Modules A X ⥤ Towers A X :=
  (Functor.ofOpSequence (fun n ↦ (step_existsUnique I X n).exists.choose)).flip

/-- Reduction is additive before localization.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: every level is scalar extension followed by additive scalar restriction.
Evaluation jointly detects equality of maps of strict diagrams. -/
@[instance] theorem reductionModule_additive (X : Scheme.{u}) :
    (reductionModule I X).Additive := by
  sorry

/-- The homotopy functor to be left derived.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def reductionHomotopy (X : Scheme.{u}) :
    HomotopyCategory (Modules A X) (.up ℤ) ⥤ Derived A X :=
  (reductionModule I X).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh

set_option genSizeOf false in
set_option genInjectivity false in
/-- A derived reduction pair, retaining its determining universal property and K-flat
computation. Source: Stacks 06YS, 06YY
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
structure ReductionModel (X : Scheme.{u}) where
  functor : DerivedCategory (Modules A X) ⥤ Derived A X
  counit : DerivedCategory.Qh ⋙ functor ⟶ reductionHomotopy I X
  universal : functor.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso (Modules A X) (.up ℤ))
  computes : ∀ P : CochainComplex (Modules A X) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A X) P →
    IsIso (counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- Universal derived reduction, with its K-flat representative normalization.
Source: Stacks 06YS, 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: choose flat-term K-flat resolutions. Their diagonal is K-flat: tensoring an
acyclic tower evaluates to tensoring an acyclic complex with the K-flat model at
every level. Evaluations are exact and jointly detect acyclicity. The strict
quotient construction therefore inverts resolving quasi-isomorphisms. The resolving
class left-derived theorem gives the universal counit, invertible on these models.
This universal property determines the derived pair up to its unique comparison. -/
theorem reduction_exists (X : Scheme.{u}) : Nonempty (ReductionModel I X) := by
  sorry

/-- Select the derived pair by its universal property, retaining its comparison.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def reductionModel (X : Scheme.{u}) : ReductionModel I X :=
  Classical.choice (reduction_exists I X)

/-- Reduction is the functor of the universal derived pair.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def reduction (X : Scheme.{u}) : DerivedCategory (Modules A X) ⥤ Derived A X :=
  (reductionModel I X).functor

/-- The universal reduction counit, retained rather than forgotten.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def reductionCounit (X : Scheme.{u}) :
    DerivedCategory.Qh ⋙ reduction I X ⟶ reductionHomotopy I X :=
  (reductionModel I X).counit

/-- Ordinary quotient augmentation, uniquely fixed by the tensor unit at every level.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: insert 1 tensor x. Quotient transitions preserve 1 and their pure tensor
formula therefore makes these maps a strict tower map, natural in the module.
The formula on all sections determines every component uniquely. -/
theorem ordinaryAugmentation_existsUnique (X : Scheme.{u}) :
    ∃! η : (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X) ⟶ reductionModule I X,
      ∀ (M : Modules A X) (n : ℕ) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
        ((η.app M).app (op n)).val.app U x =
          reductionTensorSection X (quotient I X n) M U 1 x := by
  sorry

/-- The actual ordinary quotient augmentation.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def ordinaryAugmentation (X : Scheme.{u}) :
    (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X) ⟶ reductionModule I X :=
  (ordinaryAugmentation_existsUnique I X).exists.choose

/-- The ordinary augmentation after homotopy localization, with the diagonal
localization factor. Source: Stacks 06YY
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def augmentationHomotopy (X : Scheme.{u}) :
    DerivedCategory.Qh ⋙ delta A X ⟶ reductionHomotopy I X :=
  (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X).mapDerivedCategoryFactorsh.hom ≫
    Functor.whiskerRight (NatTrans.mapHomotopyCategory (ordinaryAugmentation I X) (.up ℤ))
      DerivedCategory.Qh

/-- The specified tensor-with-quotient map i_M, constructed by the determining
universal property of derived reduction. Its factorization is the ordinary
x maps to 1 tensor x formula after homotopy localization.
Source: Stacks 06YY (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def augmentation (X : Scheme.{u}) : delta A X ⟶ reduction I X :=
  haveI : (reduction I X).IsLeftDerivedFunctor (reductionCounit I X)
      (HomotopyCategory.quasiIso (Modules A X) (.up ℤ)) := (reductionModel I X).universal
  (reduction I X).leftDerivedLift (reductionCounit I X)
    (HomotopyCategory.quasiIso (Modules A X) (.up ℤ)) (delta A X)
    (augmentationHomotopy I X)

/-- Ordinary tensor/pullback comparison on the entire strict quotient tower.
Its formula is imposed on all inverse-image generators, not only constant sections.
Source: Stacks 07A4, 03EL
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: pullback of each constant quotient ring is its canonical constant sheaf.
The scalar square commutes on constants and therefore on the sheafifications.
Tensor balancing sends the inverse image of s tensor x to the inverse image of s
 tensored with the inverse image of x. The reverse reassociation is inverse.
The quotient transition formulas make these maps a strict diagram isomorphism.
Local generation of inverse-image sections and sheafification prove uniqueness. -/
theorem ordinaryReductionPull_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! σ : reductionModule I Y ⋙ towerPullback A f ≅
        modulePullback A f ⋙ reductionModule I X,
      ∀ (M : Modules A Y) (n : ℕ) (U : Y.ProEt)
        (s : (coefficients (A ⧸ I ^ (n + 1)) Y).obj.obj (op U))
        (x : M.val.obj (op U)),
        ((σ.hom.app M).app (op n)).val.app (op ((proEtaleBaseChange f).obj U))
            (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
              (constantRingIso A f)).unit.app ((level I Y n).obj M)).val.app (op U)
                (reductionTensorSection Y (quotient I Y n) M (op U) s x)) =
          reductionTensorSection X (quotient I X n) ((modulePullback A f).obj M)
            (op ((proEtaleBaseChange f).obj U))
            ((proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
              (CommRingCat.of (A ⧸ I ^ (n + 1)))).hom.app (op U) s)
            (((proEtaleRingModuleAdjunction f (coefficients A Y) (coefficients A X)
              (constantRingIso A f)).unit.app M).val.app (op U) x) := by
  sorry

/-- The normalized ordinary comparison, retaining its strict transition maps.
Source: Stacks 07A4 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def ordinaryReductionPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (ordinaryReductionPull_existsUnique I f).exists.choose

/-- Derived tensor/pullback comparison characterized on K-flat representatives.
Source: Stacks 06YS, 07A4
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).
Proof: a flat-term K-flat model P remains K-flat with flat terms after exact
constant-coefficient inverse image. The reduction counits are invertible there.
Conjugate the ordinary strict comparison by these counits and the localization
factors. This descends through chain maps, homotopies and resolving
quasi-isomorphisms. Every object has such a model, proving uniqueness. -/
theorem reductionPull_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! τ : reduction I Y ⋙ G A f ≅ pull A f ⋙ reduction I X,
      ∀ P : CochainComplex (Modules A Y) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := coefficients A Y) P →
        IsReductionPullAt (reductionModule I Y) (reductionModule I X)
          (modulePullback A f) (towerPullback A f) (reduction I Y) (reduction I X)
          (reductionCounit I Y) (reductionCounit I X) (ordinaryReductionPull I f) τ
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  sorry

/-- The canonical whole-tower tensor/pullback comparison.
Source: Stacks 07A4 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def reductionPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (reductionPull_existsUnique I f).exists.choose

/-- The projection map h, defined by its counit-tensor adjunction mate. The comparison
being transposed is the canonical tensor balancing map on the full quotient diagram.
Its source therefore includes precisely the diagonal identification chi.
Source: Stacks 0B56 (blueprint: lem-sf-cbc-constant-tower-direct-image-normalization). -/
def projection {X Y : Scheme.{u}} (f : X ⟶ Y) :
    push A f ⋙ reduction I Y ⟶ reduction I X ⋙ R A f :=
  mateEquiv
    (proEtaleRingDerivedAdjunction f (coefficients A Y) (coefficients A X)
      (constantRingIso A f)) (adj A f) (reductionPull I f).hom

/-- Constant strict towers have normalized derived direct image, evaluation, inverse
limit and quotient augmentation, for the given coefficient datum and every object.
Source: agent argument supporting fix-lem-exchanges Step 5, using Stacks 08BJ, 070K,
0940, 0941, 0A07, 06YS, 07A4 and 0B56
(blueprint: lem-sf-cbc-constant-tower-direct-image-normalization).

Proof plan:
1. Realize strict towers on the diagram site. Exact evaluation detects exactness.
Choose a K-injective model J of M. Terminal-index evaluation is left adjoint to
constant towers and is exact, so delta J is K-injective (08BJ). Exact constant-ring
inverse image makes f_* preserve K-injectives as well. The comparison chi is the
universal derived comparison of f_* delta J = delta f_* J (070K). This proves its
representative formula and the identity at every evaluation.
2. The inverse limit of the diagonal K-injective model is J. The two canonical
units identify its derived limit with M. The common-direct-image comparison is the
ordinary f_* lim = lim f_* comparison (0A07). On the diagonal this is the literal
identity, so the displayed conjugated composite is identity.
3. Independently choose a flat-term K-flat model P of M (06YS). The diagonal is
K-flat by levelwise tensoring and joint detection of acyclicity. The strict tensor
of this model with the entire quotient tower represents reduction and its quotient
augmentation. Exact inverse image carries the whole quotient diagram to the same
quotient diagram on X, compatibly with every quotient map (00YV, 07A4). The
normalized comparison reductionPull is thus the diagram-site tensor comparison.
Its adjoint projection is exactly the counit-tensor map of 0B56, with source
identified by chi; no arbitrary projection isomorphism is chosen.
4. Naturality in the coefficient argument applied to the strict quotient map and
the tensor-unit normalization of ringedProjectionMateExact give the last equation
before taking any inverse limit. This is equality of strict derived tower maps,
including all transitions, and uses no boundedness or finiteness of quotient sets. -/
theorem constantTowerDirectImageNormalization
    (d : CompleteCoefficientDatum A) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsDirectImageNormalizedOnKInjectives (moduleDirectImage A f)
      (Functor.const ℕᵒᵖ : Modules A X ⥤ Towers A X)
      (Functor.const ℕᵒᵖ : Modules A Y ⥤ Towers A Y) (towerDirectImage A f)
      (Functor.compConstIso ℕᵒᵖ (moduleDirectImage A f)) (chi A f) ∧
    (∀ (M : DerivedCategory (Modules A X)) (n : ℕ),
      (ev A Y n).map ((chi A f).hom.app M) ≫
          (evalR A f n).app ((delta A X).obj M) ≫
          (push A f).map ((deltaEval A X n).hom.app M) =
        (deltaEval A Y n).hom.app ((push A f).obj M)) ∧
    (∀ M : DerivedCategory (Modules A X),
      (push A f).map ((deltaLimit A X).inv.app M) ≫
          (limitPush A f).hom.app ((delta A X).obj M) ≫
          (L A Y).map ((chi A f).inv.app M) ≫
          (deltaLimit A Y).hom.app ((push A f).obj M) = 𝟙 _) ∧
    (∀ M : DerivedCategory (Modules A X),
      (augmentation d.ideal Y).app ((push A f).obj M) ≫
          (projection d.ideal f).app M =
        (chi A f).hom.app M ≫ (R A f).map ((augmentation d.ideal X).app M)) := by
  sorry

end AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization
