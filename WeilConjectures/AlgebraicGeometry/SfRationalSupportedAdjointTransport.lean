/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectCharacterization
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.TriangleShift
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Raw scalar transport of supported adjunctions

Source: main-20261015, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-localization-all-stages.proof.md, Vanishing, Rational stage, Consequences;
BBD, Proposition 1.1.9 and Corollary 1.1.10(ii)
(blueprint: lem-sf-rational-supported-adjoint-transport).

Main statements: `sfRationalSupportedAdjointTransport`,
`sfSupportedRationalHomCoordinates`, `sfSupportedKernelRightAdjoint`, and
`sfSupportedIntegralCategoryIdentification`. Together they give all clauses of the node.
The structures below package the hypotheses and conclusions of this single statement.
All raw localizations are the published tensor-Hom categories; no idempotents are added.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe r u v x y z w e

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TensorProduct

namespace WeilConjectures

section Categories
variable (R : Type r) [CommRing R]
  (X : Type u) [Category.{v} X] [Preadditive X] [Linear R X]
  [HasZeroObject X] [HasShift X ℤ] [∀ n : ℤ, (shiftFunctor X n).Additive]
  [Pretriangulated X] [IsTriangulated X]
  (Z : Type x) [Category.{y} Z] [Preadditive Z] [Linear R Z]
  [HasZeroObject Z] [HasShift Z ℤ] [∀ n : ℤ, (shiftFunctor Z n).Additive]
  [Pretriangulated Z] [IsTriangulated Z]
  (U : Type z) [Category.{w} U] [Preadditive U] [Linear R U]
  [HasZeroObject U] [HasShift U ℤ] [∀ n : ℤ, (shiftFunctor U n).Additive]
  [Pretriangulated U] [IsTriangulated U]

/-- Exactly the supplied five exact linear functors, three compatible adjunctions,
invertible restriction counits, vanishing composite and supported triangles.
Source: blueprint Rational stage, supported input
(blueprint: lem-sf-rational-supported-adjoint-transport). -/
structure SfSupportedAdjunctions where
  closedPush : Z ⥤ X
  [closedPushAdditive : closedPush.Additive]
  [closedPushLinear : closedPush.Linear R]
  [closedPushShift : closedPush.CommShift ℤ]
  [closedPushExact : closedPush.IsTriangulated]
  closedPull : X ⥤ Z
  [closedPullAdditive : closedPull.Additive]
  [closedPullLinear : closedPull.Linear R]
  [closedPullShift : closedPull.CommShift ℤ]
  [closedPullExact : closedPull.IsTriangulated]
  exceptional : X ⥤ Z
  [exceptionalAdditive : exceptional.Additive]
  [exceptionalLinear : exceptional.Linear R]
  [exceptionalShift : exceptional.CommShift ℤ]
  [exceptionalExact : exceptional.IsTriangulated]
  openPull : X ⥤ U
  [openPullAdditive : openPull.Additive]
  [openPullLinear : openPull.Linear R]
  [openPullShift : openPull.CommShift ℤ]
  [openPullExact : openPull.IsTriangulated]
  openPush : U ⥤ X
  [openPushAdditive : openPush.Additive]
  [openPushLinear : openPush.Linear R]
  [openPushShift : openPush.CommShift ℤ]
  [openPushExact : openPush.IsTriangulated]
  closedAdj : closedPull ⊣ closedPush
  exceptionalAdj : closedPush ⊣ exceptional
  openAdj : openPull ⊣ openPush
  [closedCompatibility : closedAdj.CommShift ℤ]
  [exceptionalCompatibility : exceptionalAdj.CommShift ℤ]
  [openCompatibility : openAdj.CommShift ℤ]
  [closedCounitIso : IsIso closedAdj.counit]
  [openCounitIso : IsIso openAdj.counit]
  zeroComposite : ∀ P : Z, IsZero (openPull.obj (closedPush.obj P))
  boundary : ∀ K : X,
    openPush.obj (openPull.obj K) ⟶ (closedPush.obj (exceptional.obj K))⟦(1 : ℤ)⟧
  distinguished : ∀ K : X,
    Triangle.mk (exceptionalAdj.counit.app K) (openAdj.unit.app K) (boundary K) ∈
      distTriang X

attribute [instance]
  SfSupportedAdjunctions.closedPushAdditive
  SfSupportedAdjunctions.closedPushLinear
  SfSupportedAdjunctions.closedPushShift
  SfSupportedAdjunctions.closedPushExact
  SfSupportedAdjunctions.closedPullAdditive
  SfSupportedAdjunctions.closedPullLinear
  SfSupportedAdjunctions.closedPullShift
  SfSupportedAdjunctions.closedPullExact
  SfSupportedAdjunctions.exceptionalAdditive
  SfSupportedAdjunctions.exceptionalLinear
  SfSupportedAdjunctions.exceptionalShift
  SfSupportedAdjunctions.exceptionalExact
  SfSupportedAdjunctions.openPullAdditive
  SfSupportedAdjunctions.openPullLinear
  SfSupportedAdjunctions.openPullShift
  SfSupportedAdjunctions.openPullExact
  SfSupportedAdjunctions.openPushAdditive
  SfSupportedAdjunctions.openPushLinear
  SfSupportedAdjunctions.openPushShift
  SfSupportedAdjunctions.openPushExact
  SfSupportedAdjunctions.closedCompatibility SfSupportedAdjunctions.exceptionalCompatibility
  SfSupportedAdjunctions.openCompatibility SfSupportedAdjunctions.closedCounitIso
  SfSupportedAdjunctions.openCounitIso

variable {R X Z U}

/-- The given supported triangle, with no chosen replacement of either adjunction map.
Source: blueprint Vanishing and uniqueness
(blueprint: lem-sf-rational-supported-adjoint-transport). -/
abbrev SfSupportedAdjunctions.triangle (S : SfSupportedAdjunctions R X Z U) (K : X) :=
  Triangle.mk (S.exceptionalAdj.counit.app K) (S.openAdj.unit.app K) (S.boundary K)

/-- Consequences in one category. The shift equation includes the sign in every integer
shift, including negative shifts; the interchange of the two shifts is explicit.
Source: blueprint Vanishing and Consequences; BBD 1.1.9--1.1.10
(blueprint: lem-sf-rational-supported-adjoint-transport). -/
structure SfSupportedConsequences (S : SfSupportedAdjunctions R X Z U) : Prop where
  orthogonal : ∀ (P : Z) (N : U) (m n : ℤ),
    Subsingleton ((S.closedPush.obj P)⟦m⟧ ⟶ (S.openPush.obj N)⟦n⟧)
  uniqueMorphism : ∀ (K L : X) (f : K ⟶ L),
    ∃! τ : S.triangle K ⟶ S.triangle L, τ.hom₂ = f
  components : ∀ (K L : X) (τ : S.triangle K ⟶ S.triangle L),
    τ.hom₁ = S.closedPush.map (S.exceptional.map τ.hom₂) ∧
    τ.hom₃ = S.openPush.map (S.openPull.map τ.hom₂)
  uniqueBoundary : ∀ (K : X)
    (δ : S.openPush.obj (S.openPull.obj K) ⟶
      (S.closedPush.obj (S.exceptional.obj K))⟦(1 : ℤ)⟧),
    Triangle.mk (S.exceptionalAdj.counit.app K) (S.openAdj.unit.app K) δ ∈ distTriang X →
      δ = S.boundary K
  natural : ∀ (K L : X) (f : K ⟶ L),
    S.openPush.map (S.openPull.map f) ≫ S.boundary L =
      S.boundary K ≫ (S.closedPush.map (S.exceptional.map f))⟦(1 : ℤ)⟧'
  signedShift : ∀ (K : X) (n : ℤ),
    ((S.openPull ⋙ S.openPush).commShiftIso n).hom.app K ≫
        (n.negOnePow • (S.boundary K)⟦n⟧') ≫
        (shiftFunctorComm X (1 : ℤ) n).hom.app (S.closedPush.obj (S.exceptional.obj K)) =
      S.boundary (K⟦n⟧) ≫
        (((S.exceptional ⋙ S.closedPush).commShiftIso n).hom.app K)⟦(1 : ℤ)⟧'
  exceptionalOpenZero : ∀ N : U, IsZero (S.exceptional.obj (S.openPush.obj N))
  exceptionalUnitIso : ∀ P : Z, IsIso (S.exceptionalAdj.unit.app P)

end Categories

section Raw
variable (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C] (p : R)

/-- The induced raw structures, fixed by the tensor shift and exactly the image triangles.
These are the structures supplied by the recorded scalar-triangulation theorem.
Source: blueprint Rational stage; Stacks 05R6
(blueprint: lem-sf-rational-supported-adjoint-transport). -/
class SfSupportedRawTriangulation where
  [zero : HasZeroObject (ScalarLocalization R C p)]
  [shift : HasShift (ScalarLocalization R C p) ℤ]
  [shiftAdditive : ∀ n : ℤ, (shiftFunctor (ScalarLocalization R C p) n).Additive]
  [triangles : Pretriangulated (ScalarLocalization R C p)]
  [triangulated : IsTriangulated (ScalarLocalization R C p)]
  [localizationShift : (ScalarLocalization.localization R C p).CommShift ℤ]
  [localizationExact : (ScalarLocalization.localization R C p).IsTriangulated]
  tensorShift : ∀ n : ℤ, ∃ hn : (shiftFunctor C n).Linear R,
    (fun [_lin : (shiftFunctor C n).Linear R] ↦
      shiftFunctor (ScalarLocalization R C p) n =
        ScalarLocalization.map R C p (shiftFunctor C n)) (_lin := hn)
  identityComparison : ∀ (K : C) (n : ℤ),
    HEq (((ScalarLocalization.localization R C p).commShiftIso n).hom.app K)
      (𝟙 ((ScalarLocalization.localization R C p).obj (K⟦n⟧)))
  imageTriangles : ∀ Δ : Triangle (ScalarLocalization R C p),
    Δ ∈ distTriang (ScalarLocalization R C p) ↔
      ∃ Δ₀ : Triangle C, Δ₀ ∈ distTriang C ∧
        Nonempty (Δ ≅ (ScalarLocalization.localization R C p).mapTriangle.obj Δ₀)

attribute [instance_reducible] SfSupportedRawTriangulation.shift
  SfSupportedRawTriangulation.triangles SfSupportedRawTriangulation.localizationShift

attribute [instance] SfSupportedRawTriangulation.zero SfSupportedRawTriangulation.shift
  SfSupportedRawTriangulation.shiftAdditive SfSupportedRawTriangulation.triangles
  SfSupportedRawTriangulation.triangulated SfSupportedRawTriangulation.localizationShift
  SfSupportedRawTriangulation.localizationExact
end Raw

section Functor
variable (R : Type r) [CommRing R] (p : R)
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C] [SfSupportedRawTriangulation R C p]
  {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] [SfSupportedRawTriangulation R D p]

/-- Tensor and shift normalization of one localized functor. Its endpoints are the
published raw categories, and its action is fixed on all tensor generators.
Source: blueprint Rational stage (blueprint: lem-sf-rational-supported-adjoint-transport). -/
structure SfSupportedLocalizedFunctor (F : C ⥤ D) [F.CommShift ℤ]
    (G : ScalarLocalization R C p ⥤ ScalarLocalization R D p) [G.CommShift ℤ] : Prop where
  objects : ∀ K : ScalarLocalization R C p, G.obj K = ⟨F.obj K.obj⟩
  tensors : ∀ (K L : C) (f : K ⟶ L) (a : Localization.Away p),
    HEq (G.map (a ⊗ₜ[R] f : ScalarLocalization.mk K ⟶ ScalarLocalization.mk L))
      (a ⊗ₜ[R] F.map f :
        ScalarLocalization.mk (R := R) (p := p) (F.obj K) ⟶
          ScalarLocalization.mk (R := R) (p := p) (F.obj L))
  shifts : ∀ (K : C) (n : ℤ),
    HEq ((G.commShiftIso n).hom.app ⟨K⟩)
      ((ScalarLocalization.localization R D p).map ((F.commShiftIso n).hom.app K))
end Functor

section Transport
variable (R : Type r) [CommRing R] (p : R)
  (X : Type u) [Category.{v} X] [Preadditive X] [Linear R X]
  [HasZeroObject X] [HasShift X ℤ] [∀ n : ℤ, (shiftFunctor X n).Additive]
  [Pretriangulated X] [IsTriangulated X]
  (Z : Type x) [Category.{y} Z] [Preadditive Z] [Linear R Z]
  [HasZeroObject Z] [HasShift Z ℤ] [∀ n : ℤ, (shiftFunctor Z n).Additive]
  [Pretriangulated Z] [IsTriangulated Z]
  (U : Type z) [Category.{w} U] [Preadditive U] [Linear R U]
  [HasZeroObject U] [HasShift U ℤ] [∀ n : ℤ, (shiftFunctor U n).Additive]
  [Pretriangulated U] [IsTriangulated U]

/-- All transport conclusions, including the actual units, counits and boundary.
Source: blueprint Rational stage, Vanishing and Consequences
(blueprint: lem-sf-rational-supported-adjoint-transport). -/
structure SfSupportedAdjunctionTransport (S : SfSupportedAdjunctions R X Z U) where
  [rawX : SfSupportedRawTriangulation R X p]
  [rawZ : SfSupportedRawTriangulation R Z p]
  [rawU : SfSupportedRawTriangulation R U p]
  localized : SfSupportedAdjunctions (Localization.Away p)
    (ScalarLocalization R X p) (ScalarLocalization R Z p) (ScalarLocalization R U p)
  closedPushNormalization : SfSupportedLocalizedFunctor R p S.closedPush localized.closedPush
  closedPullNormalization : SfSupportedLocalizedFunctor R p S.closedPull localized.closedPull
  exceptionalNormalization : SfSupportedLocalizedFunctor R p S.exceptional localized.exceptional
  openPullNormalization : SfSupportedLocalizedFunctor R p S.openPull localized.openPull
  openPushNormalization : SfSupportedLocalizedFunctor R p S.openPush localized.openPush
  closedAdjUnit : ∀ K : X,
    HEq (localized.closedAdj.unit.app ⟨K⟩)
      ((ScalarLocalization.localization R X p).map (S.closedAdj.unit.app K))
  closedAdjCounit : ∀ K : Z,
    HEq (localized.closedAdj.counit.app ⟨K⟩)
      ((ScalarLocalization.localization R Z p).map (S.closedAdj.counit.app K))
  exceptionalAdjUnit : ∀ K : Z,
    HEq (localized.exceptionalAdj.unit.app ⟨K⟩)
      ((ScalarLocalization.localization R Z p).map (S.exceptionalAdj.unit.app K))
  exceptionalAdjCounit : ∀ K : X,
    HEq (localized.exceptionalAdj.counit.app ⟨K⟩)
      ((ScalarLocalization.localization R X p).map (S.exceptionalAdj.counit.app K))
  openAdjUnit : ∀ K : X,
    HEq (localized.openAdj.unit.app ⟨K⟩)
      ((ScalarLocalization.localization R X p).map (S.openAdj.unit.app K))
  openAdjCounit : ∀ K : U,
    HEq (localized.openAdj.counit.app ⟨K⟩)
      ((ScalarLocalization.localization R U p).map (S.openAdj.counit.app K))
  boundaryNormalization : ∀ K : X,
    HEq (localized.boundary ⟨K⟩)
      ((ScalarLocalization.localization R X p).map (S.boundary K) ≫
        ((ScalarLocalization.localization R X p).commShiftIso (1 : ℤ)).hom.app
          (S.closedPush.obj (S.exceptional.obj K)))
  originalConsequences : SfSupportedConsequences S
  localizedConsequences : SfSupportedConsequences localized

/-- Scalar transport of the supported adjunctions with all specified maps.
Source: blueprint prop-sf-localization-all-stages, Rational stage and Consequences
(blueprint: lem-sf-rational-supported-adjoint-transport).

Proof plan (node steps 1--5 and 7):
1. Give an ordinary integral kernel adjoint its unique adjunction-compatible coherent
shifts (lem-weil-pbc-adjunction-shift-compatibility-unique). Exactness follows from
lem-sf-triangulated-right-adjoint, and linearity from lem-sbc-linear-right-adjoint.
The transpose G(h) eta and its inverse epsilon F(a) are linear by bilinearity.
2. Apply lem-weil-linear-scalar-localization-triangulated to the three raw categories.
Apply lem-pur-semilinear-scalar-localization with the identity coefficient map to
all five functors, their shifts and the six unit/counit transformations. The tensor
formulas preserve both triangle identities, invertible counits, and the supported
triangles, with exactly their original first two arrows tensored with one.
3. Adjunction and j* i*=0 kill Hom(i*P[m],j*N[n]); tensoring the zero module with
E gives zero without a faithfulness or finite-generation assumption. The invertible
closed counit makes i* fully faithful, so its other adjunction has invertible unit,
using lem-weil-pbc-adjunction-counit-iso-right-fully-faithful and
lem-sp-adjunction-unit-fully-faithful-left, in either category.
4. Naturality gives the first two squares for the components (i*i!f,f,j*j*f).
Apply lem-weil-pbc-triangle-morphism-extension (BBD 1.1.9--1.1.10) and the shifted
orthogonality to get the unique triangle morphism, unique boundary and naturality.
Identities and composites have their prescribed middle map, giving functoriality.
5. Rotate three times and change signs on the first and third vertices. The resulting
triangle has arrows e[1],u[1],-delta[1]. Adjunction-compatible comparisons and boundary
uniqueness give the displayed signed rule, iterated forwards and backwards for all n.
For H=i!j*G, adjunction identifies End(H) with the zero cross-Hom group, so id(H)=0
and H is zero. Everything applies before and after localization.
7. The localized coefficient is canonically E by the uniformizer localization
identification; commuting the tensor factors recovers precisely Hom tensor E.
No Karoubi completion or new object is used. -/
theorem sfRationalSupportedAdjointTransport
    (l : ℕ) [Fact l.Prime] (E : Type e) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (X : Type u) [Category.{v} X] [Preadditive X]
    [Linear (Padic.coefficientExtensionIntegers l E) X]
    [HasZeroObject X] [HasShift X ℤ] [∀ n : ℤ, (shiftFunctor X n).Additive]
    [Pretriangulated X] [IsTriangulated X]
    [(shiftFunctor X (1 : ℤ)).Linear (Padic.coefficientExtensionIntegers l E)]
    (Z : Type x) [Category.{y} Z] [Preadditive Z]
    [Linear (Padic.coefficientExtensionIntegers l E) Z]
    [HasZeroObject Z] [HasShift Z ℤ] [∀ n : ℤ, (shiftFunctor Z n).Additive]
    [Pretriangulated Z] [IsTriangulated Z]
    [(shiftFunctor Z (1 : ℤ)).Linear (Padic.coefficientExtensionIntegers l E)]
    (U : Type z) [Category.{w} U] [Preadditive U]
    [Linear (Padic.coefficientExtensionIntegers l E) U]
    [HasZeroObject U] [HasShift U ℤ] [∀ n : ℤ, (shiftFunctor U n).Additive]
    [Pretriangulated U] [IsTriangulated U]
    [(shiftFunctor U (1 : ℤ)).Linear (Padic.coefficientExtensionIntegers l E)]
    (S : SfSupportedAdjunctions (Padic.coefficientExtensionIntegers l E) X Z U) :
    Nonempty (SfSupportedAdjunctionTransport (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionUniformizer l E) X Z U S) := by
  sorry
end Transport

section HomCoordinates
variable (l : ℕ) [Fact l.Prime] (E : Type e) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (C : Type u) [Category.{v} C] [Preadditive C]
  [Linear (Padic.coefficientExtensionIntegers l E) C]

/-- The raw Hom is exactly Hom tensor E, with the canonical coefficient identification.
Source: blueprint Rational stage, displayed Hom formula
(blueprint: lem-sf-rational-supported-adjoint-transport).
Proof (node steps 2,3,7): commute the two tensor factors and apply the canonical
uniformizer localization equivalence sfRationalCoefficientEquiv on the coefficient.
The inverse uses its inverse equivalence. The two maps fix all pure tensors, which
generate the tensor product, proving both inverse laws and uniqueness. -/
theorem sfSupportedRationalHomCoordinates
    (K L : ScalarLocalization (Padic.coefficientExtensionIntegers l E) C
      (Padic.coefficientExtensionUniformizer l E)) :
    ∃! c : (K ⟶ L) ≃+ ((K.obj ⟶ L.obj) ⊗[Padic.coefficientExtensionIntegers l E] E),
      ∀ (f : K.obj ⟶ L.obj)
        (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
        c (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f) =
          f ⊗ₜ[Padic.coefficientExtensionIntegers l E] sfRationalCoefficientEquiv l E a := by
  let c := ((TensorProduct.congr (sfRationalCoefficientEquiv l E).toLinearEquiv
    (LinearEquiv.refl (Padic.coefficientExtensionIntegers l E) (K.obj ⟶ L.obj))).trans
      (TensorProduct.comm (Padic.coefficientExtensionIntegers l E) E
        (K.obj ⟶ L.obj))).toAddEquiv
  refine ⟨c, ?_, ?_⟩
  · intro f a
    simp [c]
  · intro c' hc'
    apply AddEquiv.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a f => simp [hc', c]
    | add t t' ht ht' => simp [ht, ht']
end HomCoordinates

section Kernel
variable (R : Type r) [CommRing R]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
  {D : Type x} [Category.{y} D] [Preadditive D] [Linear R D]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D]

private theorem supportedCommShift_ext
    {A B : Type*} [Category* A] [Category* B] [HasShift A ℤ] [HasShift B ℤ]
    (F : A ⥤ B) (s t : F.CommShift ℤ)
    (h : ∀ n : ℤ, F.commShiftIso (self := s) n = F.commShiftIso (self := t) n) :
    s = t := by
  cases s
  cases t
  congr
  funext n
  exact h n

-- The existing statement names instance binders used only through typeclass inference.
set_option linter.unusedVariables false in
/-- An ordinary integral kernel adjoint acquires precisely the compatible exact shifts
and coefficient linearity, rather than being assumed exact in advance.
Source: blueprint Integral and Rational stages, kernel-adjoint refinement
(blueprint: lem-sf-rational-supported-adjoint-transport).
Proof (node step 1): use lem-weil-pbc-adjunction-shift-compatibility-unique to obtain
the unique coherent compatible right-adjoint shifts. With these shifts,
lem-sf-triangulated-right-adjoint gives exactness. Adjoint additivity and
lem-sbc-linear-right-adjoint give the two linear-functor structures. Bilinearity
of G(h) eta and epsilon F(a) proves scalar linearity of the Hom adjunction. -/
theorem sfSupportedKernelRightAdjoint (F : C ⥤ D) [F.Additive] [F.Linear R]
    [F.CommShift ℤ] [F.IsTriangulated] (G : D ⥤ C) (adj : F ⊣ G) :
    G.Additive ∧ G.Linear R ∧
    (∃! s : G.CommShift ℤ,
      (fun [shiftG : G.CommShift ℤ] ↦ adj.CommShift ℤ) (shiftG := s)) ∧
    (fun [shiftG : G.CommShift ℤ] ↦ G.IsTriangulated)
      (shiftG := adj.rightAdjointCommShift ℤ) ∧
    (∀ (P : C) (K : D) (a : R) (h : F.obj P ⟶ K),
      adj.homEquiv P K (a • h) = a • adj.homEquiv P K h) := by
  have _ := ‹IsTriangulated C›
  have _ := ‹IsTriangulated D›
  have : G.Additive := adj.right_adjoint_additive
  have : G.Linear R := adj.right_adjoint_linear
  have compatible (s : G.CommShift ℤ)
      (hs : (fun [_shiftG : G.CommShift ℤ] ↦ adj.CommShift ℤ) (_shiftG := s)) (n : ℤ) :
      Adjunction.CommShift.CompatibilityUnit adj (F.commShiftIso n)
        (G.commShiftIso (self := s) n) := by
    let := s
    let := hs
    intro P
    have h := NatTrans.shift_app_comm adj.unit n P
    simp only [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_id_hom_app] at h
    erw [Category.id_comp] at h
    exact h
  let := adj.rightAdjointCommShift ℤ
  have hcomm : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let := hcomm
  refine ⟨inferInstance, inferInstance, ?_, adj.isTriangulated_rightAdjoint, ?_⟩
  · refine ⟨adj.rightAdjointCommShift ℤ, hcomm, ?_⟩
    intro s hs
    apply supportedCommShift_ext
    intro n
    exact Adjunction.CommShift.compatibilityUnit_unique_right adj _ _ _
      (compatible s hs n) (compatible _ hcomm n)
  · intro P K a h
    simp only [Adjunction.homEquiv_unit, Functor.map_smul, Linear.comp_smul]
end Kernel

section CoefficientIdentification
open AlgebraicGeometry AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The recorded completed-category predicate, read in the detailed ambient category
through the coefficient isomorphism normalized by every quotient projection.
This is only change of presentation, not a new completeness predicate.
Source: blueprint Rational stage, category identification; integral comparison step 8
(blueprint: lem-sf-rational-supported-adjoint-transport). -/
def sfSupportedCompletePresentation :
    ObjectProperty (DerivedCategory (scalarReductionSource.{u, u} l E T)) :=
  fun K ↦ PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)
    ((integralDetailedTransport T l E).obj K)

/-- The stratified-perfect predicate in the identical detailed ambient presentation.
Source: Bhatt--Scholze 6.6.11, 6.8.11(3); blueprint Rational stage
(blueprint: lem-sf-rational-supported-adjoint-transport). -/
def sfSupportedPerfectPresentation :
    ObjectProperty (DerivedCategory (scalarReductionSource.{u, u} l E T)) :=
  fun K ↦ IsIntegralStratifiedPerfect T (pbcIntegralDatum l E)
    ((integralDetailedTransport T l E).obj K)

/-- Equality of full-subcategory predicates gives the literal identity identification
of their raw scalar localizations. The transport is equality elimination, so it adds
neither objects nor maps and does not choose an arbitrary realization equivalence.
Source: blueprint Rational stage, identity on objects and tensor maps
(blueprint: lem-sf-rational-supported-adjoint-transport). -/
def sfSupportedRawPredicateEquivalence
    (R : Type r) [CommRing R] (p : R)
    {C : Type x} [Category.{y} C] [Preadditive C] [Linear R C]
    {P Q : ObjectProperty C} (h : P = Q) :
    ScalarLocalization R P.FullSubcategory p ≌ ScalarLocalization R Q.FullSubcategory p :=
  h ▸ CategoryTheory.Equivalence.refl (C := ScalarLocalization R P.FullSubcategory p)

/-- The completed, detailed and stratified-perfect presentations select the same objects;
the induced raw identification fixes the underlying object and every h tensor a.
The canonical coefficient-ring transport is performed before comparing predicates.
Source: blueprint Rational stage, category identification before transport;
Bhatt--Scholze 6.6.11 and 6.8.11(3)
(blueprint: lem-sf-rational-supported-adjoint-transport).

Proof (node steps 6--7): Spec(k) is Noetherian. The finite-type-over-Noetherian
lemma makes T Noetherian, and lem-kun-dimension-finite-type gives finite dimension.
The unit l in k pulls back to a unit on T. Apply
lem-weil-pbc-integral-stratified-perfect-characterization, including its detailed
comparison and its compatible etale-origin witnesses and common reduction bounds.
The coefficient comparison is fixed by all positive quotient projections, hence
compares precisely the recorded completed ring and recorded reductions. After that
identification both are full subcategories of the identical ambient derived category,
so their predicates are equal. Apply raw scalar localization to this equality. Its
object map and every pure-tensor map are literally unchanged, as the displayed
normalization shows. The Hom-coordinate theorem changes only tensor order and the
canonical coefficient coordinate from Localization.Away to E. No idempotent is added. -/
theorem sfSupportedIntegralCategoryIdentification
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] :
    ∃ h : sfIntegralConstructible l E T = sfSupportedCompletePresentation l E T,
      sfSupportedCompletePresentation l E T = sfSupportedPerfectPresentation l E T ∧
      (∀ K : sfIntegralConstructibleCategory l E T,
        (sfSupportedRawPredicateEquivalence (Padic.coefficientExtensionIntegers l E)
          (Padic.coefficientExtensionUniformizer l E) h).functor.obj
            (ScalarLocalization.mk K) =
          ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l E)
            (p := Padic.coefficientExtensionUniformizer l E)
            (⟨K.obj, Eq.mp (congrFun h K.obj) K.property⟩ :
              (sfSupportedCompletePresentation l E T).FullSubcategory)) ∧
      (∀ (K L : sfIntegralConstructibleCategory l E T) (f : K ⟶ L)
        (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
        HEq ((sfSupportedRawPredicateEquivalence (Padic.coefficientExtensionIntegers l E)
          (Padic.coefficientExtensionUniformizer l E) h).functor.map
            (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
              ScalarLocalization.mk K ⟶ ScalarLocalization.mk L))
          (a ⊗ₜ[Padic.coefficientExtensionIntegers l E]
            (ObjectProperty.homMk f.hom :
              (⟨K.obj, Eq.mp (congrFun h K.obj) K.property⟩ :
                (sfSupportedCompletePresentation l E T).FullSubcategory) ⟶
              (⟨L.obj, Eq.mp (congrFun h L.obj) L.property⟩ :
                (sfSupportedCompletePresentation l E T).FullSubcategory)) :
            ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l E)
                (p := Padic.coefficientExtensionUniformizer l E)
                (⟨K.obj, Eq.mp (congrFun h K.obj) K.property⟩ :
                  (sfSupportedCompletePresentation l E T).FullSubcategory) ⟶
              ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l E)
                (p := Padic.coefficientExtensionUniformizer l E)
                (⟨L.obj, Eq.mp (congrFun h L.obj) L.property⟩ :
                  (sfSupportedCompletePresentation l E T).FullSubcategory))) := by
  let : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
  let : CompactSpace T :=
    QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of k))
  let : IsNoetherian T := ⟨⟩
  have hdim := exists_topologicalKrullDim_le (T ↘ Spec (.of k))
  have hinv : IsUnit (l : Γ(T, ⊤)) := by
    simpa only [map_natCast] using
      hl.map (((Scheme.ΓSpecIso (.of k)).inv ≫ (T ↘ Spec (.of k)).appTop).hom)
  have h : sfIntegralConstructible l E T = sfSupportedCompletePresentation l E T := by
    funext K
    exact propext (integralStratifiedPerfectDetailed T l E hdim hinv K)
  refine ⟨h, ?_, ?_, ?_⟩
  · funext K
    exact propext (integralStratifiedPerfectCharacterization T l E hdim hinv
      ((integralDetailedTransport T l E).obj K)).1
  · intro K
    generalize sfSupportedCompletePresentation l E T = Q at h ⊢
    cases h
    rfl
  · intro K L f a
    generalize sfSupportedCompletePresentation l E T = Q at h ⊢
    cases h
    rfl
end CoefficientIdentification

end WeilConjectures
