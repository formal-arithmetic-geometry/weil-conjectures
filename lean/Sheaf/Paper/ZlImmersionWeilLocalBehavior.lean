/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q157
-/
module

public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.ConstructiblePullbackTExact
public import Sheaf.Paper.CompactSupportCoefficientAction
import Sheaf.Paper.CompactSupportFiniteFieldIndependence
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.Paper.IntegralPullbackComposition
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.Paper.ConstructibleTruncations
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Sheaf.Paper.SfIntegralCompactSupportConstructible
import Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts
import Sheaf.Paper.CompletedOpenExchangeTransport
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.IntegralPullbackCompletedComparison
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
import Sheaf.SixFunctors.IntegralOpenReductionComparison
import Sheaf.SixFunctors.OpenTensorNormalization

/-! # Exact immersion operations and local Frobenius on Weil stalks

Source: main-20261015, sec-deligne-laumon-general/sk-l-dl-general-excision,
lem-zl-morphism-open-closed-reduction.proof.md, Restriction and Part 2
(blueprint: lem-zl-immersion-weil-local-behavior).

The auxiliary structures package the clauses of this statement. No operation is chosen
from their existence. All stalks are the recorded point fibres, and normalization on every
finite stage specifies the local operators and the pullback comparison themselves.

## Main declarations

- `ZlWeilExactOperation`: exact-heart restriction and the normalized Weil cohomology maps.
- `ZlWeilLocalOperators`: the specified local geometric Frobenius on actual stalks.
- `ZlImmersionPullback` and `ZlOpenExtension`: the two clauses of the node.
- `zlOpenStalkIso`: the inside-open stalk comparison constructed from restriction and unit.
- `zlImmersionWeilLocalBehavior`: the immersion and extension-by-zero statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u uC vC uB vB uV vV
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
open CategoryTheory.Endofunctor
namespace WeilConjectures

section Categorical
variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B]
  [HasShift B ℤ] [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]

/-- Cohomology of a fixed pair, with the structure induced by the canonical t-exact
cohomology comparison. Source: Restriction, cohomology sentence
(blueprint: lem-zl-immersion-weil-local-behavior). -/
def zlWeilCohomology {t : TStructure C} {P : ObjectProperty C} {G : C ⥤ C}
    (d : ConstructiblePullbackComparison t t P P G) (a : ℤ) :
    IsoAlgebra G ⥤ IsoAlgebra G :=
  IsoAlgebra.mapOfNatIso (d.cohomology a)

/-- The exact-heart and Weil-cohomology clauses for one specified underlying functor.
The cohomology map is the canonical truncation comparison, not an unspecified iso.
Source: Restriction and Part 2, cohomology and exactness assertions
(blueprint: lem-zl-immersion-weil-local-behavior). -/
structure ZlWeilExactOperation (t : TStructure C) (s : TStructure B)
    (P : ObjectProperty C) (Q : ObjectProperty B) (G : C ⥤ C) (H : B ⥤ B)
    (dG : ConstructiblePullbackComparison t t P P G)
    (dH : ConstructiblePullbackComparison s s Q Q H) (F : C ⥤ B)
    (e : F ⋙ H ≅ G ⋙ F) where
  comparison : ConstructiblePullbackComparison t s P Q F
  sheaf : ((P.inverseImage (IsoAlgebra.forget G)).FullSubcategory) ⥤
    ((Q.inverseImage (IsoAlgebra.forget H)).FullSubcategory)
  sheaf_fac : sheaf ⋙ (Q.inverseImage (IsoAlgebra.forget H)).ι =
    (P.inverseImage (IsoAlgebra.forget G)).ι ⋙ IsoAlgebra.mapOfNatIso e
  sheaf_limits : PreservesFiniteLimits sheaf
  sheaf_colimits : PreservesFiniteColimits sheaf
  cohomology : ∀ a : ℤ, zlWeilCohomology dG a ⋙ IsoAlgebra.mapOfNatIso e ≅
    IsoAlgebra.mapOfNatIso e ⋙ zlWeilCohomology dH a
  cohomology_map : ∀ (a : ℤ) (K : IsoAlgebra G),
    ((cohomology a).hom.app K).hom.f = (comparison.cohomology a).hom.app K.carrier
/-- The inside-open comparison is inverse restriction followed by inverse adjunction
unit. Associators only identify the literal composites of functors.
Source: Part 2, inside-open stalk formula, proof Step 10
(blueprint: lem-zl-immersion-weil-local-behavior). -/
def zlOpenStalkIso {V : Type uV} [Category.{vV} V] {J : C ⥤ B} {P : B ⥤ C}
    (η : 𝟭 C ≅ J ⋙ P) {sx : B ⥤ V} {sz : C ⥤ V} (r : P ⋙ sz ≅ sx) :
    J ⋙ sx ≅ sz :=
  Functor.isoWhiskerLeft J r.symm ≪≫ (Functor.associator J P sz).symm ≪≫
    Functor.isoWhiskerRight η.symm sz ≪≫ Functor.leftUnitor sz

end Categorical

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)

/-- Base change of the actual model morphism to the fixed algebraic closure.
Source: Restriction, h the base change of h₀
(blueprint: lem-zl-immersion-weil-local-behavior). -/
abbrev zlGeometricMap {W₀ X₀ : Over (Spec (.of D.k₀))} (h₀ : W₀ ⟶ X₀) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map h₀).left

variable (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- Finite type of the actual geometric fibre is inherited by base change.
Source: Restriction, geometric base change
(blueprint: lem-zl-immersion-weil-local-behavior). -/
instance zlGeometricFiberLocallyOfFiniteType :
    LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
  inferInstanceAs (LocallyOfFiniteType
    (pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Quasi-compactness of the geometric fibre is inherited by base change.
Source: Restriction, geometric base change
(blueprint: lem-zl-immersion-weil-local-behavior). -/
instance zlGeometricFiberQuasiCompact :
    QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
  inferInstanceAs (QuasiCompact
    (pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- The standard common-stage t-structure on the geometric fibre.
Source: Restriction, standard constructible t-structure
(blueprint: lem-zl-immersion-weil-local-behavior). -/
abbrev zlStandard :=
  sfCommonStageStandardTStructure c.l (D.geometricFiber Y₀).left c.Qbar D c.different

/-- The underlying cohomological point-fibre functor on fixed pairs, in every degree.
Source: Restriction and Part 2, canonical stalk convention
(blueprint: lem-zl-immersion-weil-local-behavior). -/
def zlWeilStalk (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (a : ℤ) :
    sfCommonStageWeilComplex D c.l c.different Y₀ c.Qbar ⥤ ModuleCat.{u} c.Qbar :=
  sfCommonStageWeilForget D c.l c.different Y₀ c.Qbar ⋙
    @commonStageDerivedPullback c.l _ c.Qbar _ _ _ _ _ x
      (frobeniusPointPrimeInvertible D c.l c.different)
      (sfWeilPrimeInvertible D c.l c.different Y₀) ⋙
    pointQbarFibre D c.l c.different c.Qbar ⋙
    DerivedCategory.pointFdQbarRealization c.l c.Qbar ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} c.Qbar) a

/-- The actual stalk at a closed model point with a specified compatible geometric lift.
This wrapper for the stalk expression keeps closed-point clauses small.
Source: Restriction and Part 2, stalk convention
(blueprint: lem-zl-immersion-weil-local-behavior). -/
def zlClosedWeilStalk (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
    (a : ℤ) :=
  zlWeilStalk D c Y₀ (localClosedPoint D Y₀ y ι hι) a

/-- Realize a small finite-stage point complex over the fixed algebraic closure.
Source: common-stage bookkeeping, Step 1 and the stalk convention
(blueprint: lem-zl-immersion-weil-local-behavior). -/
def zlFinitePointRealization (E : AlgebraicallyClosedCoefficients.Index c.l c.Qbar) :
    (DerivedCategory.pointFiniteDimensional
      (AlgebraicallyClosedCoefficients.Coefficient.{u} c.l c.Qbar E)).FullSubcategory ⥤
        DerivedCategory (ModuleCat.{u} c.Qbar) :=
  DerivedCategory.pointFdScalarExtension (Shrink.algEquiv (Padic c.l) E.val).toRingHom ⋙
    DerivedCategory.pointFdQbarStage c.l c.Qbar E ⋙
    DerivedCategory.pointFdQbarRealization c.l c.Qbar

/-- Local geometric Frobenius, as a natural endomorphism of the actual stalk functor.
Its normalization is the specified localClosedFrobenius at every finite coefficient
field, with its point transport, return comparison and iterated Weil structure. HEq
only transports the object equalities in the recorded common-stage functor formulas.
Source: Restriction, local geometric Frobenius assertion
(blueprint: lem-zl-immersion-weil-local-behavior). -/
structure ZlWeilLocalOperators where
  operator : ∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
    (a : ℤ),
    zlClosedWeilStalk D c Y₀ y ι hι a ⟶ zlClosedWeilStalk D c Y₀ y ι hι a
  normalization : ∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
    (a : ℤ) (E : AlgebraicallyClosedCoefficients.Index c.l c.Qbar)
    (K : sfWeilComplex D c.l c.different Y₀
      (AlgebraicallyClosedCoefficients.Coefficient.{u} c.l c.Qbar E)),
    HEq ((operator y ι hι a).app (sfWeilStageObject D c.l c.different Y₀ c.Qbar E K))
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} c.Qbar) a).map
        ((zlFinitePointRealization D c E).map
          (localClosedFrobenius c.l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} c.l c.Qbar E)
            D c.different Y₀ K y ι hι)))

/-- The recorded Frobenius endofunctor, with the fixed coefficient datum.
Source: Restriction, induced Weil structures
(blueprint: lem-zl-immersion-weil-local-behavior). -/
abbrev zlFrobenius := sfCommonStageWeilFrobeniusPullback D c.l c.different Y₀ c.Qbar

/-- The recorded common-stage heart predicate on the geometric fibre.
Source: Restriction, constructible heart
(blueprint: lem-zl-immersion-weil-local-behavior). -/
abbrev zlHeart := sfCommonStageHeartProperty c.l (D.geometricFiber Y₀).left c.Qbar

/-- Cohomology comparisons for geometric Frobenius itself, on the standard heart.
Source: Restriction, proof Step 3
(blueprint: lem-zl-immersion-weil-local-behavior). -/
abbrev ZlFrobeniusComparison := ConstructiblePullbackComparison
  (zlStandard D c Y₀) (zlStandard D c Y₀) (zlHeart D c Y₀) (zlHeart D c Y₀)
  (zlFrobenius D c Y₀)

variable {Y₀}
variable {W₀ X₀ U₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]

/-- The specified common-stage inverse image, using the inherited invertibility proofs.
Source: Restriction, h-star
(blueprint: lem-zl-immersion-weil-local-behavior). -/
def zlPullback (h₀ : W₀ ⟶ X₀) :=
  @commonStageDerivedPullback c.l _ c.Qbar _ _ _ _ _ (zlGeometricMap D h₀)
    (sfWeilPrimeInvertible D c.l c.different W₀)
    (sfWeilPrimeInvertible D c.l c.different X₀)

/-- At a finite field the induced Weil comparison is the two specified composition
comparisons across the geometric Frobenius square.
Source: Restriction, induced structure formula theta_h = h-star(theta) alpha
(blueprint: lem-zl-immersion-weil-local-behavior). -/
def zlRationalFrobeniusComparison (h₀ : W₀ ⟶ X₀)
    (w : (D.geometricFrobenius W₀).hom ≫ zlGeometricMap D h₀ =
      zlGeometricMap D h₀ ≫ (D.geometricFrobenius X₀).hom)
    (E : AlgebraicallyClosedCoefficients.Index c.l c.Qbar)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage c.l c.Qbar
      (D.geometricFiber X₀).left E) :
    (sfWeilFrobeniusPullback D c.l c.different W₀
      (AlgebraicallyClosedCoefficients.Coefficient.{u} c.l c.Qbar E)).obj
        ((@rationalDerivedPullback c.l _
          (AlgebraicallyClosedCoefficients.Coefficient.{u} c.l c.Qbar E) _ _ _ _ _
          (zlGeometricMap D h₀)
          (sfWeilPrimeInvertible D c.l c.different W₀)
          (sfWeilPrimeInvertible D c.l c.different X₀)).obj K) ≅
    (@rationalDerivedPullback c.l _
      (AlgebraicallyClosedCoefficients.Coefficient.{u} c.l c.Qbar E) _ _ _ _ _
      (zlGeometricMap D h₀)
      (sfWeilPrimeInvertible D c.l c.different W₀)
      (sfWeilPrimeInvertible D c.l c.different X₀)).obj
        ((sfWeilFrobeniusPullback D c.l c.different X₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} c.l c.Qbar E)).obj K) :=
  (@localPullbackComposition c.l _
    (AlgebraicallyClosedCoefficients.Coefficient.{u} c.l c.Qbar E) _ _ _ _ _ _
    (D.geometricFrobenius W₀).hom (zlGeometricMap D h₀)
    (sfWeilPrimeInvertible D c.l c.different W₀)
    (sfWeilPrimeInvertible D c.l c.different W₀)
    (sfWeilPrimeInvertible D c.l c.different X₀) K).symm ≪≫
    eqToIso (congrArg (fun f ↦ (@rationalDerivedPullback c.l _
      (AlgebraicallyClosedCoefficients.Coefficient.{u} c.l c.Qbar E) _ _ _ _ _ f
      (sfWeilPrimeInvertible D c.l c.different W₀)
      (sfWeilPrimeInvertible D c.l c.different X₀)).obj K) w) ≪≫
    @localPullbackComposition c.l _
      (AlgebraicallyClosedCoefficients.Coefficient.{u} c.l c.Qbar E) _ _ _ _ _ _
      (zlGeometricMap D h₀) (D.geometricFrobenius X₀).hom
      (sfWeilPrimeInvertible D c.l c.different W₀)
      (sfWeilPrimeInvertible D c.l c.different X₀)
      (sfWeilPrimeInvertible D c.l c.different X₀) K

/-- The inverse composition comparison gives the canonical finite-stage stalk map.
Source: Restriction, canonical stalk comparison, proof Step 5
(blueprint: lem-zl-immersion-weil-local-behavior). -/
def zlRationalStalkComparison (h₀ : W₀ ⟶ X₀)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber W₀).left)
    (E : AlgebraicallyClosedCoefficients.Index c.l c.Qbar)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage c.l c.Qbar
      (D.geometricFiber X₀).left E) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} c.Qbar) 0).map
    ((zlFinitePointRealization D c E).map
      ((pointRationalFibre D c.l c.different
        (AlgebraicallyClosedCoefficients.Coefficient.{u} c.l c.Qbar E)).map
          (@localPullbackComposition c.l _
            (AlgebraicallyClosedCoefficients.Coefficient.{u} c.l c.Qbar E) _ _ _ _ _ _
            z (zlGeometricMap D h₀)
            (frobeniusPointPrimeInvertible D c.l c.different)
            (sfWeilPrimeInvertible D c.l c.different W₀)
            (sfWeilPrimeInvertible D c.l c.different X₀) K).inv))

/-- The full pullback clause. The residue map is the actual induced map, and the
stalk normalization is the inverse pullback-composition comparison. In particular
Frobenius equivariance is required for that comparison, not just for some isomorphism.
Source: Restriction paragraph, proof Steps 2--6 and 11
(blueprint: lem-zl-immersion-weil-local-behavior). -/
structure ZlImmersionPullback (h₀ : W₀ ⟶ X₀)
    (dX : ZlFrobeniusComparison D c X₀) (dW : ZlFrobeniusComparison D c W₀)
    (FX : ZlWeilLocalOperators D c X₀) (FW : ZlWeilLocalOperators D c W₀) where
  commutes : (D.geometricFrobenius W₀).hom ≫ zlGeometricMap D h₀ =
    zlGeometricMap D h₀ ≫ (D.geometricFrobenius X₀).hom
  equivariance : zlPullback D c h₀ ⋙ zlFrobenius D c W₀ ≅
    zlFrobenius D c X₀ ⋙ zlPullback D c h₀
  equivariance_normalization : ∀ K : generalAlgebraicallyClosedConstructibleCategory
      c.l c.Qbar (D.geometricFiber X₀).left,
    HEq (equivariance.hom.app K)
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := c.l) (Ω := c.Qbar) (Y := (D.geometricFiber W₀).left) K.stage).map
          (zlRationalFrobeniusComparison D c h₀ commutes K.stage K.obj).hom)
  operation : ZlWeilExactOperation (zlStandard D c X₀) (zlStandard D c W₀)
    (zlHeart D c X₀) (zlHeart D c W₀) (zlFrobenius D c X₀) (zlFrobenius D c W₀)
      dX dW (zlPullback D c h₀) equivariance
  closed_image : ∀ (z : W₀.left), z ∈ closedPoints W₀.left →
    h₀.left z ∈ closedPoints X₀.left
  residue_iso : ∀ z : {z : W₀.left // z ∈ closedPoints W₀.left},
    IsIso (h₀.left.residueFieldMap z.val)
  degree_eq : ∀ z : {z : W₀.left // z ∈ closedPoints W₀.left},
    localClosedPointDegree D W₀ z =
      localClosedPointDegree D X₀ ⟨h₀.left z.val, closed_image z.val z.property⟩
  stalk : ∀ (z : {z : W₀.left // z ∈ closedPoints W₀.left})
    (ιz : W₀.left.residueField z.val →+* D.k)
    (hz : ιz.comp (W₀.hom.residueFieldAlgebraMap z.val) = algebraMap D.k₀ D.k)
    (ιx : X₀.left.residueField (h₀.left z.val) →+* D.k)
    (hx : ιx.comp (X₀.hom.residueFieldAlgebraMap (h₀.left z.val)) = algebraMap D.k₀ D.k)
    (_compatible : ιz.comp (h₀.left.residueFieldMap z.val).hom = ιx),
    IsoAlgebra.mapOfNatIso equivariance ⋙
      zlClosedWeilStalk D c W₀ z ιz hz 0 ≅
        zlClosedWeilStalk D c X₀
          ⟨h₀.left z.val, closed_image z.val z.property⟩ ιx hx 0
  stalk_normalization : ∀ z ιz hz ιx hx compatible
    (E : AlgebraicallyClosedCoefficients.Index c.l c.Qbar)
    (K : sfWeilComplex D c.l c.different X₀
      (AlgebraicallyClosedCoefficients.Coefficient.{u} c.l c.Qbar E)),
    HEq ((stalk z ιz hz ιx hx compatible).hom.app
      (sfWeilStageObject D c.l c.different X₀ c.Qbar E K))
        (zlRationalStalkComparison D c h₀ (localClosedPoint D W₀ z ιz hz) E K.carrier)
  stalk_frobenius : ∀ z ιz hz ιx hx compatible
    (F : sfCommonStageWeilSheaf D c.l c.different X₀ c.Qbar),
    (FW.operator z ιz hz 0).app ((IsoAlgebra.mapOfNatIso equivariance).obj F.obj) ≫
        (stalk z ιz hz ιx hx compatible).hom.app F.obj =
      (stalk z ιz hz ιx hx compatible).hom.app F.obj ≫
        (FX.operator ⟨h₀.left z.val, closed_image z.val z.property⟩ ιx hx 0).app F.obj

/-- The already normalized compact-support coefficient action for the open
compactification (j,id). Geometric properties are data of the conclusion, not extra
hypotheses on j₀. Source: Part 2, extension by zero, proof Steps 7--9
(blueprint: lem-zl-immersion-weil-local-behavior). -/
abbrev ZlOpenAction (j₀ : U₀ ⟶ X₀)
    (ho : IsOpenImmersion (zlGeometricMap D j₀))
    (hqc : QuasiCompact (zlGeometricMap D j₀))
    (hft : LocallyOfFiniteType (zlGeometricMap D j₀))
    (hsep : IsSeparated (zlGeometricMap D j₀))
    (hover : (zlGeometricMap D j₀).IsOver (Spec (.of D.k)))
    (hl : IsUnit (c.l : D.k)) : Type _ :=
  @SfCompactSupportCoefficientAction c.l _ D.k _ hl
    (D.geometricFiber U₀).left (D.geometricFiber X₀).left (zlGeometricMap D j₀)
    inferInstance inferInstance
    (zlGeometricFiberLocallyOfFiniteType D U₀) (zlGeometricFiberQuasiCompact D U₀)
    (zlGeometricFiberLocallyOfFiniteType D X₀) (zlGeometricFiberQuasiCompact D X₀)
    hover hsep hft hqc c.Qbar _ _ _
    (@Compactification.ofIsOpenImmersion _ _ (zlGeometricMap D j₀) ho)

/-- The open-extension clause, on the actual normalized common-stage compact-support
functor. Its open stalk comparison is the restriction comparison followed by the
inverse open adjunction unit, in that order. The unit is required to lift to Weil
pairs, so it identifies their specified local Frobenius operators as well.
Source: Part 2, extension-by-zero sentence, proof Steps 7--11
(blueprint: lem-zl-immersion-weil-local-behavior). -/
structure ZlOpenExtension (j₀ : U₀ ⟶ X₀)
    (dX : ZlFrobeniusComparison D c X₀) (dU : ZlFrobeniusComparison D c U₀)
    (FX : ZlWeilLocalOperators D c X₀) (FU : ZlWeilLocalOperators D c U₀) where
  geometric_open : IsOpenImmersion (zlGeometricMap D j₀)
  geometric_qc : QuasiCompact (zlGeometricMap D j₀)
  geometric_ft : LocallyOfFiniteType (zlGeometricMap D j₀)
  geometric_sep : IsSeparated (zlGeometricMap D j₀)
  geometric_over : (zlGeometricMap D j₀).IsOver (Spec (.of D.k))
  prime_unit : IsUnit (c.l : D.k)
  action : ZlOpenAction D c j₀ geometric_open geometric_qc geometric_ft geometric_sep
    geometric_over prime_unit
  functor : generalAlgebraicallyClosedConstructibleCategory
    c.l c.Qbar (D.geometricFiber U₀).left ⥤
      generalAlgebraicallyClosedConstructibleCategory c.l c.Qbar (D.geometricFiber X₀).left
  functor_eq : functor = action.system.functor
  restriction : ZlImmersionPullback D c j₀ dX dU FX FU
  equivariance : functor ⋙ zlFrobenius D c X₀ ≅
    zlFrobenius D c U₀ ⋙ functor
  operation : ZlWeilExactOperation (zlStandard D c U₀) (zlStandard D c X₀)
    (zlHeart D c U₀) (zlHeart D c X₀) (zlFrobenius D c U₀) (zlFrobenius D c X₀)
      dU dX functor equivariance
  adjunction : functor ⊣ zlPullback D c j₀
  unit_isIso : IsIso adjunction.unit
  equivariance_mate : ∀ K : generalAlgebraicallyClosedConstructibleCategory
      c.l c.Qbar (D.geometricFiber U₀).left,
    equivariance.inv.app K =
      (adjunction.homEquiv ((zlFrobenius D c U₀).obj K)
        ((zlFrobenius D c X₀).obj (functor.obj K))).symm
          ((zlFrobenius D c U₀).map (adjunction.unit.app K) ≫
            restriction.equivariance.hom.app (functor.obj K))
  weilUnit : 𝟭 (sfCommonStageWeilComplex D c.l c.different U₀ c.Qbar) ≅
    IsoAlgebra.mapOfNatIso equivariance ⋙ IsoAlgebra.mapOfNatIso restriction.equivariance
  weilUnit_map : ∀ K : sfCommonStageWeilComplex D c.l c.different U₀ c.Qbar,
    (weilUnit.hom.app K).hom.f = adjunction.unit.app K.carrier
  openStalk_frobenius : ∀ (z : {z : U₀.left // z ∈ closedPoints U₀.left})
    (ιz : U₀.left.residueField z.val →+* D.k)
    (hz : ιz.comp (U₀.hom.residueFieldAlgebraMap z.val) = algebraMap D.k₀ D.k)
    (ιx : X₀.left.residueField (j₀.left z.val) →+* D.k)
    (hx : ιx.comp (X₀.hom.residueFieldAlgebraMap (j₀.left z.val)) = algebraMap D.k₀ D.k)
    (compatible : ιz.comp (j₀.left.residueFieldMap z.val).hom = ιx)
    (G : sfCommonStageWeilSheaf D c.l c.different U₀ c.Qbar),
    (FX.operator ⟨j₀.left z.val, restriction.closed_image z.val z.property⟩ ιx hx 0).app
        ((IsoAlgebra.mapOfNatIso equivariance).obj G.obj) ≫
          (zlOpenStalkIso weilUnit
            (restriction.stalk z ιz hz ιx hx compatible)).hom.app G.obj =
      (zlOpenStalkIso weilUnit
        (restriction.stalk z ιz hz ιx hx compatible)).hom.app G.obj ≫
          (FU.operator z ιz hz 0).app G.obj
  outside : ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (ι : X₀.left.residueField x.val →+* D.k)
    (hι : ι.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (_outside : x.val ∉ Set.range j₀.left)
    (G : sfCommonStageWeilSheaf D c.l c.different U₀ c.Qbar),
    IsZero ((zlClosedWeilStalk D c X₀ x ι hι 0).obj
      ((IsoAlgebra.mapOfNatIso equivariance).obj G.obj))

/-- Pullback along a locally closed immersion and open extension by zero are exact
on the constructible Weil hearts, commute with all cohomology as Weil functors, and
have the specified Frobenius-equivariant stalks. The geometric residue maps are
isomorphisms; equality of their degrees records the identical residue-field size.

Source: main-20261015, sec-deligne-laumon-general/sk-l-dl-general-excision,
lem-zl-morphism-open-closed-reduction.proof.md, Restriction and Part 2
(blueprint: lem-zl-immersion-weil-local-behavior).

Proof, following the eleven steps of the DAG node:
1. Represent the finitely many Weil arrows, inverses and inverse equations over a
common finite coefficient field. No Frobenius-stable integral lattice is required.
2. Apply lem-a1-constructible-pullback-t-exact to h and to geometric Frobenius.
The two rationalized integral composition comparisons across g_X h = h g_W give
alpha, and the induced structure is alpha followed by h-star(theta).
3. Uniqueness of truncation triangles gives the Weil cohomology comparisons, with
exactly the underlying canonical truncation maps in comparison.cohomology.
4. Factor h₀ as closed then open. The closed map quotients the local ring; the open
map identifies local rings. Their residue maps are isomorphisms. A closed point
has finite residue field, so its image is closed, with the same positive degree.
5. The inverse pullback-composition comparison at compatible geometric points,
followed by the recorded point fibre, is the normalized stalk comparison.
6. Expand the iterated induced Weil structure. Associativity of the integral
composition comparisons and naturality of point transport identify each of the
three factors in local geometric Frobenius, giving the stated operator equation.
7. X is Noetherian, so j is quasi-compact. Use the compactification (j,id). The
integral open reduction comparison identifies compact support with termwise exact
extension by zero, preserves completeness and constructibility, and gives t-exactness.
8. Rationalize, then pass to common stages. Scalar comparisons and extension by
zero through derived limits preserve these comparisons and both standard halves.
9. Completed open base change along Frobenius gives the induced Weil structure.
The normalized open adjunction unit is Weil-equivariant. Truncation uniqueness
then makes the open cohomology comparisons equivariant as in Step 3.
10. Inside the open, compose inverse restriction and inverse open unit. Step 6
intertwines Frobenius with the unchanged residue degree. Outside the open, base
change to the point factors extension through the empty site, whose module is zero.
11. Kernels and cokernels of equivariant maps inherit invertible Weil structures
from exact Frobenius pullback. The two exact underlying heart functors preserve
them, proving preservation of finite limits and colimits on the Weil hearts. -/
theorem zlImmersionWeilLocalBehavior
    [IsSeparated W₀.hom] [IsSeparated X₀.hom] [IsSeparated U₀.hom]
    (h₀ : W₀ ⟶ X₀) [IsImmersion h₀.left]
    (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left] :
    ∃ (dX : ZlFrobeniusComparison D c X₀) (dW : ZlFrobeniusComparison D c W₀)
      (dU : ZlFrobeniusComparison D c U₀)
      (FX : ZlWeilLocalOperators D c X₀) (FW : ZlWeilLocalOperators D c W₀)
      (FU : ZlWeilLocalOperators D c U₀),
      Nonempty (ZlImmersionPullback D c h₀ dX dW FX FW) ∧
        Nonempty (ZlOpenExtension D c j₀ dX dU FX FU) := by
  sorry

end WeilConjectures
