/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.SfCommonStageWeilCohomology
public import Sheaf.Paper.ConstructibleTruncations
public import Sheaf.Paper.IntegralPullbackCompletedComparison
public import Sheaf.SixFunctors.FrobeniusPointTransportNatural
public import Sheaf.Paper.CoefficientCohomologyModules
import Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Sheaf.Paper.SfDerivedDirectImage
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport

/-! # Truncations, triangles and cohomology of rational Weil pairs

Source: blueprint main-20261015, sec-poincare-duality/sk-lem-finite,
prop-weil-operations.proof.md, sentence 2 and the final cohomology assertion;
BBD, Proposition 1.3.3 and paragraph 1.3.4, printed pp. 29--30
(blueprint: lem-pod-fixed-pair-truncation-cohomology).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v uC vC
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

/-- The clauses of the fixed-pair assertion, using the existing transport functor.
The boundary equation includes the specified shift comparison. Triangles are taken
only in C. Source: blueprint prop-weil-operations, truncation and cohomology clauses
(blueprint: lem-pod-fixed-pair-truncation-cohomology). -/
def FixedPairTruncationCohomologySpec
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (t : TStructure C) (P : C ⥤ C) [P.CommShift ℤ] : Prop :=
  ∃ (cLE : ∀ m : ℤ, t.truncLE m ⋙ P ≅ P ⋙ t.truncLE m)
    (cGE : ∀ m : ℤ, t.truncGE m ⋙ P ≅ P ⋙ t.truncGE m),
    (∀ (m : ℤ) (K : C),
      (cLE m).hom.app K ≫ (t.truncLEι m).app (P.obj K) =
        P.map ((t.truncLEι m).app K) ∧
      P.map ((t.truncGEπ m).app K) ≫ (cGE m).hom.app K =
        (t.truncGEπ m).app (P.obj K)) ∧
    (∀ m : ℤ,
      IsoAlgebra.mapOfNatIso (cLE m) ⋙ IsoAlgebra.forget P =
        IsoAlgebra.forget P ⋙ t.truncLE m ∧
      IsoAlgebra.mapOfNatIso (cGE m) ⋙ IsoAlgebra.forget P =
        IsoAlgebra.forget P ⋙ t.truncGE m) ∧
    (∀ (m : ℤ) (K : IsoAlgebra P),
      ((IsoAlgebra.mapOfNatIso (cLE m)).obj K).str.hom ≫
          (t.truncLEι m).app K.carrier =
        P.map ((t.truncLEι m).app K.carrier) ≫ K.str.hom ∧
      K.str.hom ≫ (t.truncGEπ m).app K.carrier =
        P.map ((t.truncGEπ m).app K.carrier) ≫
          ((IsoAlgebra.mapOfNatIso (cGE m)).obj K).str.hom ∧
      ((IsoAlgebra.mapOfNatIso (cGE (m + 1))).obj K).str.hom ≫
          (t.truncGEδLE m (m + 1) rfl).app K.carrier =
        P.map ((t.truncGEδLE m (m + 1) rfl).app K.carrier) ≫
          (P.commShiftIso (1 : ℤ)).hom.app ((t.truncLE m).obj K.carrier) ≫
            (shiftFunctor C (1 : ℤ)).map
              (((IsoAlgebra.mapOfNatIso (cLE m)).obj K).str.hom)) ∧
    (∀ i : ℤ,
      ∃ H : IsoAlgebra P ⥤ IsoAlgebra P,
        H = (IsoAlgebra.mapOfNatIso (cLE i) ⋙ IsoAlgebra.mapOfNatIso (cGE i)) ⋙
          IsoAlgebra.mapOfNatIso (P.commShiftIso i) ∧
        H ⋙ IsoAlgebra.forget P =
          IsoAlgebra.forget P ⋙ constructibleTruncationCohomology t i ∧
        ∀ K : IsoAlgebra P, t.heart (H.obj K).carrier)


variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- The rational shift is the localization of the signed Roos shift, through the
recorded full-subcategory inclusion. Its integral witness retains both the coordinate
normalization and descent equations; an arbitrary shift is not accepted.
Source: blueprint prop-weil-operations, exact Frobenius pullback; Stacks 014E, 0941
(blueprint: lem-pod-fixed-pair-truncation-cohomology). -/
def FixedPairRationalShiftNormalization
    (s : (sfWeilFrobeniusPullback D l hl Y₀ E).CommShift ℤ) : Prop :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  ∃ c : IntegralCompletedComparison.Comparison l E (D.geometricFrobenius Y₀).hom,
    ∃ d : (constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom).CommShift ℤ,
      (fun [_ambientShift : (integralDerivedPullback l E
          (D.geometricFrobenius Y₀).hom).CommShift ℤ]
        [_integralShift : (constructibleIntegralPullback l E
          (D.geometricFrobenius Y₀).hom).CommShift ℤ]
        [_rationalShift : (sfWeilFrobeniusPullback D l hl Y₀ E).CommShift ℤ] ↦
        (∀ (K : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) (r : ℤ),
          (sfIntegralConstructible l E (D.geometricFiber Y₀).left).ι.map
              (((constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom).commShiftIso
                 r).hom.app K) ≫
            (((sfIntegralConstructible l E (D.geometricFiber Y₀).left).ι).commShiftIso
               r).hom.app
                ((constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom).obj K) =
          (integralDerivedPullback l E (D.geometricFrobenius Y₀).hom).map
              ((((sfIntegralConstructible l E (D.geometricFiber Y₀).left).ι).commShiftIso
                 r).hom.app K) ≫
            ((integralDerivedPullback l E (D.geometricFrobenius Y₀).hom).commShiftIso
               r).hom.app K.obj) ∧
        ∃ β : sfRationalConstructibleLocalization l E (D.geometricFiber Y₀).left ⋙
              sfWeilFrobeniusPullback D l hl Y₀ E ≅
            constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom ⋙
              sfRationalConstructibleLocalization l E (D.geometricFiber Y₀).left,
          (∀ K, β.hom.app K = eqToHom
            ((rationalDerivedPullback_existsUnique l E
              (D.geometricFrobenius Y₀).hom).exists.choose_spec.2.1
              ((sfRationalConstructibleLocalization l E (D.geometricFiber Y₀).left).obj K))) ∧
          NatTrans.CommShift β.hom ℤ)
        (_ambientShift := c.derivedShift) (_integralShift := d) (_rationalShift := s)

/-- The standard rational t-structure on the actual geometric fibre.
Source: blueprint prop-constructible-truncations
(blueprint: lem-pod-fixed-pair-truncation-cohomology). -/
def fixedPairRationalTStructure :=
  sfRationalStandardTStructure l E (D.geometricFiber Y₀).left D hl

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The corresponding standard common-stage t-structure.
Source: blueprint prop-constructible-truncations
(blueprint: lem-pod-fixed-pair-truncation-cohomology). -/
def fixedPairCommonStageTStructure :=
  sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl

/-- Compatibility with every finite stage specifies the common-stage shift.
The component of the inclusion comparison is the actual object identification of
commonStageDerivedPullback, so it is not an unspecified commuting isomorphism.
Source: blueprint common-stage coefficient convention and exact Frobenius pullback
(blueprint: lem-pod-fixed-pair-truncation-cohomology). -/
def FixedPairCommonShiftNormalization
    (s : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      (sfWeilFrobeniusPullback D l hl Y₀
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).CommShift ℤ)
    (q : (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).CommShift ℤ) : Prop :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
    ∃ β : sfWeilFrobeniusPullback D l hl Y₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := (D.geometricFiber Y₀).left) L ≅
        GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := (D.geometricFiber Y₀).left) L ⋙
          sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω,
      (∀ K, β.inv.app K = eqToHom
        ((commonStageDerivedPullback_existsUnique l Ω
          (D.geometricFrobenius Y₀).hom).exists.choose_spec.1
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := (D.geometricFiber Y₀).left) L).obj K))) ∧
      ∀ (r : ℤ) (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω
          (D.geometricFiber Y₀).left L),
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := (D.geometricFiber Y₀).left) L).map
            ((Functor.commShiftIso (sfWeilFrobeniusPullback D l hl Y₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)) (self := s L) r).hom.app K) ≫
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := (D.geometricFiber Y₀).left) L).commShiftIso r).hom.app
            ((sfWeilFrobeniusPullback D l hl Y₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).obj K) ≫
          (shiftFunctor _ r).map (β.hom.app K) =
        β.hom.app ((shiftFunctor _ r).obj K) ≫
          (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).map
            (((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := (D.geometricFiber Y₀).left) L).commShiftIso r).hom.app K) ≫
          (Functor.commShiftIso (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω)
            (self := q) r).hom.app
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := (D.geometricFiber Y₀).left) L).obj K)

/-- Truncation functors, the three equivariant triangle arrows and cohomology on
rational Weil pairs, with the signed Roos/localization shift.
Source: blueprint prop-weil-operations.proof.md, sentence 2; BBD 1.3.3--1.3.4
(blueprint: lem-pod-fixed-pair-truncation-cohomology).
Proof (node Steps 1--8 and 10): exact inverse-image transport along the geometric
Frobenius preserves both standard halves (prop-constructible-truncations and
lem-pod-semilinear-field-operation-lifts). The signed Roos shift descends and
localizes as specified by lem-a1-integral-pullback-completed-comparison. Apply
lem-pod-texact-truncation-comparison to obtain the unique comparisons normalized
by the counit and unit. IsoAlgebra.mapOfNatIso gives tau(theta) composed with c,
and maps arrows by tau; its functor laws are the underlying laws. Naturality of
the counit and unit proves equivariance of the first two triangle arrows.
Uniqueness of the whole truncation triangle, including the last arrow
(lem-weil-heart-short-exact-triangles(1)), gives its shift-compatible comparison.
Apply naturality at theta to get the displayed boundary equation. Compose upper
and lower truncations and the normalized i-shift to obtain H^i in the heart.
Apply this to truncated inputs for successive-truncation triangles; uniqueness
of adjoints identifies their absorbed truncations equivariantly. Forgetting
retains exactly the underlying functors and arrows. -/
theorem fixedPairRationalTruncationCohomology :
    ∃ s : (sfWeilFrobeniusPullback D l hl Y₀ E).CommShift ℤ,
      FixedPairRationalShiftNormalization D l hl Y₀ E s ∧
      (fun [shift : (sfWeilFrobeniusPullback D l hl Y₀ E).CommShift ℤ] ↦
        FixedPairTruncationCohomologySpec (fixedPairRationalTStructure D l hl Y₀ E)
          (sfWeilFrobeniusPullback D l hl Y₀ E)) (shift := s) := by
  sorry

/-- The same truncations, triangle arrows and cohomology on the literal common-stage
category, including arrows only representable after extending the coefficient field.
Source: blueprint prop-weil-operations.proof.md, sentence 2 and common-stage convention
(blueprint: lem-pod-fixed-pair-truncation-cohomology).
Proof (node Steps 1--8 and 10): use the preceding rational construction at every
finite field. The normalized scalar pullback comparisons identify the integral
signed shifts and their localizations. Their tower coherence descends the shift
through the actual finite-stage inclusions. Use prop-constructible-truncations
and lem-pod-texact-truncation-comparison in the underlying common-stage category.
IsoAlgebra.mapOfNatIso supplies the functor formulas; truncation triangle
uniqueness in lem-weil-heart-short-exact-triangles includes the shifted boundary.
The composite of the two truncations and shift has its value in the standard
heart, and forgetting recovers its underlying cohomology functor. -/
theorem fixedPairCommonTruncationCohomology :
    ∃ (s : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
        (sfWeilFrobeniusPullback D l hl Y₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).CommShift ℤ)
      (q : (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).CommShift ℤ),
      (∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
        FixedPairRationalShiftNormalization D l hl Y₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (s L)) ∧
      FixedPairCommonShiftNormalization D l hl Y₀ Ω s q ∧
      (fun [shift : (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).CommShift ℤ] ↦
        FixedPairTruncationCohomologySpec (fixedPairCommonStageTStructure D l hl Y₀ Ω)
          (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω)) (shift := q) := by
  sorry



/-- The actual rational Frobenius pullback on Spec k, using the existing derived
pullback and the inherited residue-field inverses.
Source: blueprint def-weil-frobenius-point-transport
(blueprint: lem-pod-fixed-pair-truncation-cohomology). -/
def fixedPairRationalPointPullback :=
  letI := fun x ↦ frobeniusPointPrimeInvertible D l hl x
  rationalDerivedPullback l E (frobeniusPointIso D).hom

/-- The canonical point transport, with only the recorded pullback-object equality
inserted to identify its endpoint with the actual functor's value.
Source: Deligne Weil II (1.1.7), blueprint point-transport convention
(blueprint: lem-pod-fixed-pair-truncation-cohomology). -/
def fixedPairRationalPointTransport
    (A : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (pointRationalFibre D l hl E).obj A ⟶
      (pointRationalFibre D l hl E).obj ((fixedPairRationalPointPullback D l hl E).obj A) :=
  frobeniusPointTransportRational D l hl E A ≫
    (pointRationalFibre D l hl E).map
      (eqToHom (frobeniusPointRationalPullbackEq D l hl E A).symm)

/-- Frobenius is point transport followed by the fibre of the given Weil structure.
Source: blueprint fixed-pair cohomology assertion; Deligne Weil II (1.1.7)
(blueprint: lem-pod-fixed-pair-truncation-cohomology). -/
def fixedPairRationalPointFrobenius
    (A : IsoAlgebra (fixedPairRationalPointPullback D l hl E)) :
    End ((pointRationalFibre D l hl E).obj A.carrier) :=
  fixedPairRationalPointTransport D l hl E A.carrier ≫
    (pointRationalFibre D l hl E).map A.str.hom

/-- Point-fibre maps and their cohomology maps are Frobenius equivariant. This
applies in particular to ordinary or compact-support direct images whenever the
given bounded constructible image has its canonical Weil lift.
Source: blueprint prop-weil-operations.md, final assertion
(blueprint: lem-pod-fixed-pair-truncation-cohomology).
Proof (node Step 9): apply the fibre functor to u theta_A = theta_B P(u).
Functoriality gives the first equality. Naturality in clause (2) of
lem-weil-frobenius-point-transport-natural gives iota_A Fib(Pu) = Fib(u) iota_B,
including the recorded pullback-object identifications. This proves the second
equality. Apply the ordinary H^i functor of def-weil-abstract-derived-category,
restricted by coefficientFdCohomology, and its composition law. No direct image
on a larger domain, or triangulation on pairs, is used. -/
theorem fixedPairRationalPointCohomology
    (A B : IsoAlgebra (fixedPairRationalPointPullback D l hl E)) (f : A ⟶ B) :
    (fixedPairRationalPointFrobenius D l hl E A ≫
        (pointRationalFibre D l hl E).map f.hom.f =
      fixedPairRationalPointTransport D l hl E A.carrier ≫
        (pointRationalFibre D l hl E).map
          ((fixedPairRationalPointPullback D l hl E).map f.hom.f) ≫
        (pointRationalFibre D l hl E).map B.str.hom) ∧
    (fixedPairRationalPointTransport D l hl E A.carrier ≫
        (pointRationalFibre D l hl E).map
          ((fixedPairRationalPointPullback D l hl E).map f.hom.f) ≫
        (pointRationalFibre D l hl E).map B.str.hom =
      (pointRationalFibre D l hl E).map f.hom.f ≫
        fixedPairRationalPointFrobenius D l hl E B) ∧
    ∀ i : ℤ,
      (DerivedCategory.coefficientFdCohomology E i).map
          (fixedPairRationalPointFrobenius D l hl E A) ≫
        (DerivedCategory.coefficientFdCohomology E i).map
          ((pointRationalFibre D l hl E).map f.hom.f) =
      (DerivedCategory.coefficientFdCohomology E i).map
          ((pointRationalFibre D l hl E).map f.hom.f) ≫
        (DerivedCategory.coefficientFdCohomology E i).map
          (fixedPairRationalPointFrobenius D l hl E B) := by
  sorry

section PointCommonStage
variable (Ω' : Type u) [Field Ω'] [Algebra (Padic l) Ω'] [IsAlgClosure (Padic l) Ω']

/-- Actual common-stage point Frobenius pullback, retaining the coefficient stage.
Source: blueprint common-stage point transport
(blueprint: lem-pod-fixed-pair-truncation-cohomology). -/
def fixedPairCommonPointPullback :=
  letI := fun x ↦ frobeniusPointPrimeInvertible D l hl x
  commonStageDerivedPullback l Ω' (frobeniusPointIso D).hom

/-- Canonical common-stage point transport, conjugated only by the existing
point-fibre and pullback-object identifications.
Source: blueprint point transport; Deligne Weil II (1.1.7)
(blueprint: lem-pod-fixed-pair-truncation-cohomology). -/
def fixedPairCommonPointTransport
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω' (Spec (.of D.k))) :
    (pointQbarFibre D l hl Ω').obj A ⟶
      (pointQbarFibre D l hl Ω').obj ((fixedPairCommonPointPullback D l hl Ω').obj A) :=
  eqToHom (frobeniusPointQbarFibreObjEq D l hl Ω' A) ≫
    frobeniusPointTransportQbar D l hl Ω' A ≫
    eqToHom (congrArg (pointQbarFibreObj D l hl Ω')
      (frobeniusPointQbarPullbackEq D l hl Ω' A).symm) ≫
    eqToHom (frobeniusPointQbarFibreObjEq D l hl Ω'
      ((fixedPairCommonPointPullback D l hl Ω').obj A)).symm

/-- The common-stage Frobenius operator uses the given structure and canonical transport.
Source: blueprint fixed-pair cohomology assertion
(blueprint: lem-pod-fixed-pair-truncation-cohomology). -/
def fixedPairCommonPointFrobenius
    (A : IsoAlgebra (fixedPairCommonPointPullback D l hl Ω')) :
    End ((pointQbarFibre D l hl Ω').obj A.carrier) :=
  fixedPairCommonPointTransport D l hl Ω' A.carrier ≫
    (pointQbarFibre D l hl Ω').map A.str.hom

/-- The full point-transport equation and its stagewise cohomology equation at Qbar.
It includes every arrow represented only over a larger common finite field, hence
also both supplied direct-image Weil lifts on their stated domains.
Source: blueprint prop-weil-operations.md, final assertion
(blueprint: lem-pod-fixed-pair-truncation-cohomology).
Proof (node Steps 9--10): the Weil-arrow equation gives the first equality after
applying pointQbarFibre. The actual common-stage naturality assertion of
lem-weil-frobenius-point-transport-natural(2), with its object identifications,
gives the second. Apply coefficientQbarCohomology of
 def-weil-coefficient-cohomology-modules: at stage E' it is H^i(-) tensor_E' Qbar,
and on an arbitrary common-stage representative it is the specified extended
linear map. Its functor laws give the final equation. Scalar-extension and tower
compatibility ensure the equality survives every further extension. -/
theorem fixedPairCommonPointCohomology
    (A B : IsoAlgebra (fixedPairCommonPointPullback D l hl Ω')) (f : A ⟶ B) :
    (fixedPairCommonPointFrobenius D l hl Ω' A ≫
        (pointQbarFibre D l hl Ω').map f.hom.f =
      fixedPairCommonPointTransport D l hl Ω' A.carrier ≫
        (pointQbarFibre D l hl Ω').map
          ((fixedPairCommonPointPullback D l hl Ω').map f.hom.f) ≫
        (pointQbarFibre D l hl Ω').map B.str.hom) ∧
    (fixedPairCommonPointTransport D l hl Ω' A.carrier ≫
        (pointQbarFibre D l hl Ω').map
          ((fixedPairCommonPointPullback D l hl Ω').map f.hom.f) ≫
        (pointQbarFibre D l hl Ω').map B.str.hom =
      (pointQbarFibre D l hl Ω').map f.hom.f ≫
        fixedPairCommonPointFrobenius D l hl Ω' B) ∧
    ∀ i : ℤ,
      (DerivedCategory.coefficientQbarCohomology l Ω' i).map
          (fixedPairCommonPointFrobenius D l hl Ω' A) ≫
        (DerivedCategory.coefficientQbarCohomology l Ω' i).map
          ((pointQbarFibre D l hl Ω').map f.hom.f) =
      (DerivedCategory.coefficientQbarCohomology l Ω' i).map
          ((pointQbarFibre D l hl Ω').map f.hom.f) ≫
        (DerivedCategory.coefficientQbarCohomology l Ω' i).map
          (fixedPairCommonPointFrobenius D l hl Ω' B) := by
  sorry

end PointCommonStage
end WeilConjectures
