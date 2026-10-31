/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemOperationExchangeRealization
public import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Adjunction.Unique

import WeilConjectures.AlgebraicGeometry.IntegralSupportFunctorNormalization
import all WeilConjectures.CategoryTheory.SemilinearScalarLocalization
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom

/-! # Normalized rational localization and cross-object orthogonality

Source: main-20261015, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, rational-stage paragraph
(blueprint: lem-sf-rational-localization-triangle-orthogonality).

The assertions retain the published pullback, compact-support and whole-system direct
image. The integral adjunction maps are fixed by their coherent-system normalization.
Rational adjunctions act on every tensor-Hom arrow. No Karoubi envelope is taken.
-/

@[expose] public noncomputable section
attribute [-instance] WeilConjectures.IntegralSupportNormalization.limitShift
  WeilConjectures.IntegralSupportNormalization.reductionShift
  WeilConjectures.IntegralSupportNormalization.directShift
  WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
set_option autoImplicit false
attribute [local irreducible] WeilConjectures.sfIntegralConstructible
  WeilConjectures.sfRationalTriangulationDatum
  WeilConjectures.FrobeniusExchange.models
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe r u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme TensorProduct
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The right-adjoint identity comparison, fixed by the system pullback identity unit.
Source: rational-stage proof, normalization of the compactification (j,id)
(blueprint: lem-sf-rational-localization-triangle-orthogonality). -/
def sfLocalizationSystemDirectId (X : Scheme.{u}) :
    FrobeniusExchange.systemDirect l E (𝟙 X) ≅ 𝟭 (coefficientSequenceDerived l E X) :=
  Adjunction.rightAdjointUniq
    ((FrobeniusExchange.systemAdjunction l E (𝟙 X)).ofNatIsoLeft
      (integralComparisonSystemUnit l E X)) Adjunction.id

/-- The canonical pullback-to-whole-reduction comparison, before any evaluation.
Source: rational-stage proof, integral-operation normalization
(blueprint: lem-sf-rational-localization-triangle-orthogonality). -/
def sfLocalizationPullReduction {T X : Scheme.{u}} (f : T ⟶ X) :=
  integralComparisonPullbackCounit l E f
    ((FrobeniusExchange.models l E).system X)
    ((FrobeniusExchange.models l E).system T)
    ((FrobeniusExchange.models l E).roos T)
    ((FrobeniusExchange.models l E).pullback f)

section Geometry
variable (k : Type u) [Field k] (hl : IsUnit (l : k))
  {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of k))]
  [∀ x : U, Invertible (l : U.residueField x)]
  [∀ x : X, Invertible (l : X.residueField x)]

/-- The recorded open integral functor's realization, using the projection-normalized
comparison for (j,id), followed by the specified right-adjoint identity comparison.
No isomorphism is selected merely from the existence of matching vertices.
Source: rational-stage proof, integral j! normalization
(blueprint: lem-sf-rational-localization-triangle-orthogonality). -/
def sfLocalizationOpenRealization (K : sfIntegralConstructibleCategory l E U) :
    ((sfCompactSupportFiniteIntegralFunctor l k hl
        (Compactification.ofIsOpenImmersion j) E).obj K).obj ⟶
      (FrobeniusExchange.realize l E (FrobeniusExchange.systemDerivedOpen l E j)).obj K.obj :=
  (FrobeniusExchange.compactRealization l E k hl j
      (Compactification.ofIsOpenImmersion j)).hom.app K ≫
    (coefficientSequenceLimit l E X).map
      ((sfLocalizationSystemDirectId l E X).hom.app
        ((FrobeniusExchange.systemDerivedOpen l E j).obj
          ((FrobeniusExchange.reduction l E U).obj K.obj)))
end Geometry

/-- Exact scalar extension of one of the four specified operations. Object equality,
all pure tensors and the shift square fix the raw localized functor and its exact
structure. The last equation is E-linearity through the canonical coefficient-field
identification; it imposes no integral lift condition on the rational arrow.
Source: rational-stage paragraph, exact linear operations
(blueprint: lem-sf-rational-localization-triangle-orthogonality). -/
structure SfRationalizedExactFunctor (T X : Scheme.{u})
    (F : sfIntegralConstructibleCategory l E T ⥤ sfIntegralConstructibleCategory l E X)
    (G : sfRationalConstructibleCategory l E T ⥤ sfRationalConstructibleCategory l E X) where
  [integralAdditive : F.Additive]
  [integralLinear : F.Linear (Padic.coefficientExtensionIntegers l E)]
  [integralShift : F.CommShift ℤ]
  integralExact : F.IsTriangulated
  [rationalAdditive : G.Additive]
  [rationalShift : G.CommShift ℤ]
  rationalExact : G.IsTriangulated
  objects : ∀ K, G.obj K = (sfRationalConstructibleLocalization l E X).obj (F.obj K.obj)
  tensors : ∀ (K L : sfIntegralConstructibleCategory l E T) (f : K ⟶ L)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
    HEq (G.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
      (sfRationalConstructibleLocalization l E T).obj K ⟶
        (sfRationalConstructibleLocalization l E T).obj L))
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] F.map f :
        (sfRationalConstructibleLocalization l E X).obj (F.obj K) ⟶
          (sfRationalConstructibleLocalization l E X).obj (F.obj L))
  shifts : ∀ (K : sfIntegralConstructibleCategory l E T) (m : ℤ),
    HEq (G.map (((sfRationalConstructibleLocalization l E T).commShiftIso m).hom.app K) ≫
        (G.commShiftIso m).hom.app ((sfRationalConstructibleLocalization l E T).obj K))
      ((sfRationalConstructibleLocalization l E X).map ((F.commShiftIso m).hom.app K) ≫
        ((sfRationalConstructibleLocalization l E X).commShiftIso m).hom.app (F.obj K))
  scalar : ∀ (K L : sfRationalConstructibleCategory l E T) (f : K ⟶ L) (a : E),
    G.map ((sfRationalCoefficientEquiv l E).symm a • f) =
      (sfRationalCoefficientEquiv l E).symm a • G.map f

/-- The canonical cross-Hom identification, characterized on the generators after
transport by the literal object equalities and Q's specified shift comparison.
Both the tensor group and the rational Hom group are zero (expressed as subsingletons).
Source: rational-stage paragraph, Hom tensor E = 0 for independent open/closed inputs
(blueprint: lem-sf-rational-localization-triangle-orthogonality). -/
def SfRationalCrossHom (U Z X : Scheme.{u})
    (J : sfIntegralConstructibleCategory l E U ⥤ sfIntegralConstructibleCategory l E X)
    (I : sfIntegralConstructibleCategory l E Z ⥤ sfIntegralConstructibleCategory l E X)
    (Jq : sfRationalConstructibleCategory l E U ⥤ sfRationalConstructibleCategory l E X)
    (Iq : sfRationalConstructibleCategory l E Z ⥤ sfRationalConstructibleCategory l E X)
    (hJ : ∀ N, Jq.obj N = (sfRationalConstructibleLocalization l E X).obj (J.obj N.obj))
    (hI : ∀ M, Iq.obj M = (sfRationalConstructibleLocalization l E X).obj (I.obj M.obj)) :
    Prop :=
  ∀ (N : sfRationalConstructibleCategory l E U)
    (M : sfRationalConstructibleCategory l E Z) (m : ℤ),
    Subsingleton ((Jq.obj N)⟦m⟧ ⟶ Iq.obj M) ∧
    Subsingleton (((J.obj N.obj)⟦m⟧ ⟶ I.obj M.obj) ⊗[
      Padic.coefficientExtensionIntegers l E] E) ∧
    ∃! e : ((Jq.obj N)⟦m⟧ ⟶ Iq.obj M) ≃+
        (((J.obj N.obj)⟦m⟧ ⟶ I.obj M.obj) ⊗[Padic.coefficientExtensionIntegers l E] E),
      ∀ (f : (J.obj N.obj)⟦m⟧ ⟶ I.obj M.obj)
        (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
        e (eqToHom (congrArg (fun A : sfRationalConstructibleCategory l E X ↦ A⟦m⟧)
              (hJ N)) ≫
            ((sfRationalConstructibleLocalization l E X).commShiftIso m).inv.app
              (J.obj N.obj) ≫
            (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f) ≫ eqToHom (hI M).symm) =
          f ⊗ₜ[Padic.coefficientExtensionIntegers l E] sfRationalCoefficientEquiv l E a

/-- The complete assertion, packaged to keep the four exact structures and the
inherited geometry available without adding hypotheses to the theorem. In particular
U,Z have their inherited finite-type k-structures, not structures supplied as assumptions.
The two integral map normalizations are equations in the coherent system category,
so they retain the chosen units and counits rather than only their reductions' vertices.
Source: rational-stage paragraph and its normalized integral prerequisites
(blueprint: lem-sf-rational-localization-triangle-orthogonality). -/
structure SfRationalLocalizationOrthogonality (D : FiniteFieldDatum.{u})
    {Z U X : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] where
  primeUnit : IsUnit (l : D.k)
  [openOver : U.Over (Spec (.of D.k))]
  [closedOver : Z.Over (Spec (.of D.k))]
  [openIsOver : j.IsOver (Spec (.of D.k))]
  [closedIsOver : i.IsOver (Spec (.of D.k))]
  [openFiniteType : LocallyOfFiniteType (U ↘ Spec (.of D.k))]
  [openQuasiCompact : QuasiCompact (U ↘ Spec (.of D.k))]
  [closedFiniteType : LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
  [closedQuasiCompact : QuasiCompact (Z ↘ Spec (.of D.k))]
  [openQuasiCompactMap : QuasiCompact j]
  [invertibleX : ∀ x : X, Invertible (l : X.residueField x)]
  [invertibleU : ∀ x : U, Invertible (l : U.residueField x)]
  [invertibleZ : ∀ x : Z, Invertible (l : Z.residueField x)]
  closedRationalImage : sfRationalConstructibleCategory l E Z ⥤
    sfRationalConstructibleCategory l E X
  openIntegralAdjunction :
    sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
      (Compactification.ofIsOpenImmersion j) E ⊣ constructibleIntegralPullback l E j
  closedIntegralAdjunction : constructibleIntegralPullback l E i ⊣
    FrobeniusExchange.directImageFunctor l E D.k primeUnit i
  openCounitNormalization : ∀ K : sfIntegralConstructibleCategory l E X,
    (FrobeniusExchange.reduction l E X).map (openIntegralAdjunction.counit.app K).hom =
      (FrobeniusExchange.reduction l E X).map
        (sfLocalizationOpenRealization l E D.k primeUnit j
          ((constructibleIntegralPullback l E j).obj K)) ≫
      (FrobeniusExchange.operationReduction l E
        (FrobeniusExchange.systemDerivedOpen l E j)).app
          ((constructibleIntegralPullback l E j).obj K).obj ≫
      (FrobeniusExchange.systemDerivedOpen l E j).map
        ((sfLocalizationPullReduction l E j).app K.obj) ≫
      (FrobeniusExchange.systemDerivedOpenAdjunction l E j).counit.app
        ((FrobeniusExchange.reduction l E X).obj K.obj)
  closedUnitNormalization : ∀ K : sfIntegralConstructibleCategory l E X,
    (FrobeniusExchange.reduction l E X).map (closedIntegralAdjunction.unit.app K).hom ≫
      (FrobeniusExchange.operationReduction l E
        (FrobeniusExchange.systemDirect l E i)).app
          ((constructibleIntegralPullback l E i).obj K).obj ≫
      (FrobeniusExchange.systemDirect l E i).map
        ((sfLocalizationPullReduction l E i).app K.obj) =
      (FrobeniusExchange.systemAdjunction l E i).unit.app
        ((FrobeniusExchange.reduction l E X).obj K.obj)
  closedPull : SfRationalizedExactFunctor l E X Z
    (constructibleIntegralPullback l E i) (rationalDerivedPullback l E i)
  openPull : SfRationalizedExactFunctor l E X U
    (constructibleIntegralPullback l E j) (rationalDerivedPullback l E j)
  closedPush : SfRationalizedExactFunctor l E Z X
    (FrobeniusExchange.directImageFunctor l E D.k primeUnit i) closedRationalImage
  openPush : SfRationalizedExactFunctor l E U X
    (sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
      (Compactification.ofIsOpenImmersion j) E)
    (sfCompactSupportFiniteFunctor l D.k primeUnit
      (Compactification.ofIsOpenImmersion j) E)
  openRationalAdjunction : sfCompactSupportFiniteFunctor l D.k primeUnit
    (Compactification.ofIsOpenImmersion j) E ⊣ rationalDerivedPullback l E j
  closedRationalAdjunction : rationalDerivedPullback l E i ⊣ closedRationalImage
  openUnit : ∀ N : sfIntegralConstructibleCategory l E U,
    HEq (openRationalAdjunction.unit.app ((sfRationalConstructibleLocalization l E U).obj N))
      ((sfRationalConstructibleLocalization l E U).map (openIntegralAdjunction.unit.app N))
  openCounit : ∀ K : sfIntegralConstructibleCategory l E X,
    HEq (openRationalAdjunction.counit.app ((sfRationalConstructibleLocalization l E X).obj K))
      ((sfRationalConstructibleLocalization l E X).map (openIntegralAdjunction.counit.app K))
  closedUnit : ∀ K : sfIntegralConstructibleCategory l E X,
    HEq (closedRationalAdjunction.unit.app ((sfRationalConstructibleLocalization l E X).obj K))
      ((sfRationalConstructibleLocalization l E X).map (closedIntegralAdjunction.unit.app K))
  closedCounit : ∀ M : sfIntegralConstructibleCategory l E Z,
    HEq (closedRationalAdjunction.counit.app ((sfRationalConstructibleLocalization l E Z).obj M))
      ((sfRationalConstructibleLocalization l E Z).map (closedIntegralAdjunction.counit.app M))
  triangles : ∀ (K : sfIntegralConstructibleCategory l E X)
    (δ : (FrobeniusExchange.directImageFunctor l E D.k primeUnit i).obj
        ((constructibleIntegralPullback l E i).obj K) ⟶
      ((sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
          (Compactification.ofIsOpenImmersion j) E).obj
        ((constructibleIntegralPullback l E j).obj K))⟦(1 : ℤ)⟧),
    Triangle.mk (openIntegralAdjunction.counit.app K)
        (closedIntegralAdjunction.unit.app K) δ ∈
      distTriang (sfIntegralConstructibleCategory l E X) →
    ∃ δE : closedRationalImage.obj ((rationalDerivedPullback l E i).obj
        ((sfRationalConstructibleLocalization l E X).obj K)) ⟶
      ((sfCompactSupportFiniteFunctor l D.k primeUnit
          (Compactification.ofIsOpenImmersion j) E).obj
        ((rationalDerivedPullback l E j).obj
          ((sfRationalConstructibleLocalization l E X).obj K)))⟦(1 : ℤ)⟧,
      Triangle.mk (openRationalAdjunction.counit.app
          ((sfRationalConstructibleLocalization l E X).obj K))
        (closedRationalAdjunction.unit.app
          ((sfRationalConstructibleLocalization l E X).obj K)) δE ∈
            distTriang (sfRationalConstructibleCategory l E X) ∧
      HEq δE ((sfRationalConstructibleLocalization l E X).map δ ≫
        ((sfRationalConstructibleLocalization l E X).commShiftIso (1 : ℤ)).hom.app
          ((sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
            (Compactification.ofIsOpenImmersion j) E).obj
              ((constructibleIntegralPullback l E j).obj K)))
  orthogonality : SfRationalCrossHom l E U Z X
    (sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
      (Compactification.ofIsOpenImmersion j) E)
    (FrobeniusExchange.directImageFunctor l E D.k primeUnit i)
    (sfCompactSupportFiniteFunctor l D.k primeUnit
      (Compactification.ofIsOpenImmersion j) E)
    closedRationalImage openPush.objects closedPush.objects

open CategoryTheory.ScalarLocalization


private theorem sfLocalization_isLocalization (T : Scheme.{u}) :
    (sfRationalConstructibleLocalization l E T).IsLocalization
      (Rationalization.W (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
        (sfIntegralConstructibleCategory l E T)) := by
  have : ∀ n : ℤ, (shiftFunctor (sfIntegralConstructibleCategory l E T) n).Linear
      (Padic.coefficientExtensionIntegers l E) :=
    CategoryTheory.ScalarLocalization.semilinear_all_shift_linear _ _
  exact CategoryTheory.ScalarLocalization.semilinear_localization_isLocalization _ _ _

private theorem sfLocalization_factor {T X : Scheme.{u}}
    (F : sfIntegralConstructibleCategory l E T ⥤ sfIntegralConstructibleCategory l E X)
    (G : sfRationalConstructibleCategory l E T ⥤ sfRationalConstructibleCategory l E X)
    (hobj : ∀ K, G.obj K = (sfRationalConstructibleLocalization l E X).obj (F.obj K.obj))
    (htensor : ∀ (K L : sfIntegralConstructibleCategory l E T) (f : K ⟶ L)
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
      HEq (G.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f))
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] F.map f)) :
    sfRationalConstructibleLocalization l E T ⋙ G =
      F ⋙ sfRationalConstructibleLocalization l E X := by
  apply Functor.hext (fun K ↦ hobj ⟨K⟩)
  intro K L f
  exact htensor K L f 1

private theorem sf_hom_smul_heq {A : Type*} [CommRing A]
    {C : Type*} [Category C] [Preadditive C] [Linear A C]
    {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (hf : HEq f g) (a : A) :
    HEq (a • f) (a • g) := by
  subst X'; subst Y'
  exact heq_of_eq (congrArg (a • ·) (eq_of_heq hf))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sfRationalizedExact {T X : Scheme.{u}}
    (F : sfIntegralConstructibleCategory l E T ⥤ sfIntegralConstructibleCategory l E X)
    [F.Additive] [F.Linear (Padic.coefficientExtensionIntegers l E)]
    [F.CommShift ℤ] [F.IsTriangulated]
    (G : sfRationalConstructibleCategory l E T ⥤ sfRationalConstructibleCategory l E X)
    [G.Additive]
    (hobj : ∀ K, G.obj K = (sfRationalConstructibleLocalization l E X).obj (F.obj K.obj))
    (htensor : ∀ (K L : sfIntegralConstructibleCategory l E T) (f : K ⟶ L)
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
      HEq (G.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f))
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] F.map f)) :
    Nonempty (SfRationalizedExactFunctor l E T X F G) := by
  let Q := sfRationalConstructibleLocalization l E T
  let P := sfRationalConstructibleLocalization l E X
  let W := Rationalization.W
    (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
    (sfIntegralConstructibleCategory l E T)
  have : Q.IsLocalization W := sfLocalization_isLocalization l E T
  let e : Q ⋙ G ≅ F ⋙ P := eqToIso (sfLocalization_factor l E F G hobj htensor)
  let : Localization.Lifting Q W (F ⋙ P) G := ⟨e⟩
  let cs : G.CommShift ℤ := Functor.commShiftOfLocalization Q W ℤ (F ⋙ P) G
  have he : NatTrans.CommShift e.hom ℤ :=
    NatTrans.commShift_iso_hom_of_localization Q W ℤ (F ⋙ P) G
  have htri : G.IsTriangulated := by
    have : (Q ⋙ G).IsTriangulated := (Functor.isTriangulated_iff_of_iso e).2 inferInstance
    have : ∀ n : ℤ, (shiftFunctor (sfIntegralConstructibleCategory l E T) n).Linear
        (Padic.coefficientExtensionIntegers l E) :=
      CategoryTheory.ScalarLocalization.semilinear_all_shift_linear _ _
    have : W.HasLeftCalculusOfFractions := by
      dsimp only [W, Rationalization.W]
      infer_instance
    have : Q.mapArrow.EssSurj := Localization.essSurj_mapArrow Q W
    exact Functor.isTriangulated_of_precomp Q G
  refine ⟨{
    integralExact := inferInstance
    rationalExact := htri
    objects := hobj
    tensors := htensor
    shifts := ?_
    scalar := ?_ }⟩
  · intro K m
    have hh := NatTrans.shift_app_comm e.hom m K
    simp only [Functor.commShiftIso_comp_hom_app] at hh
    have eh (L : sfIntegralConstructibleCategory l E T) :
        e.hom.app L = eqToHom (hobj (Q.obj L)) := by
      simp only [e, eqToIso.hom, eqToHom_app]
    rw [eh, eh] at hh
    rw [eqToHom_map] at hh
    exact (comp_eqToHom_heq _ _).symm.trans
      ((heq_of_eq hh).trans (eqToHom_comp_heq _ _))
  · intro K L f a
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul b f =>
      change G.map ((sfRationalCoefficientEquiv l E).symm a •
        (b ⊗ₜ[Padic.coefficientExtensionIntegers l E] f)) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul]
      have hh := htensor K.obj L.obj f
      have hmul := hh ((sfRationalCoefficientEquiv l E).symm a * b)
      have hb := hh b
      have hsmul := sf_hom_smul_heq (hobj K) (hobj L) hb
        ((sfRationalCoefficientEquiv l E).symm a)
      apply eq_of_heq
      simpa only [TensorProduct.smul_tmul', smul_eq_mul] using hmul.trans hsmul.symm
    | add f g hf hg => simp only [smul_add, G.map_add, hf, hg]

private theorem sfLocalizedAdjunction {T X : Scheme.{u}}
    (F : sfIntegralConstructibleCategory l E T ⥤ sfIntegralConstructibleCategory l E X)
    (G : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E T)
    (Fq : sfRationalConstructibleCategory l E T ⥤ sfRationalConstructibleCategory l E X)
    (Gq : sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E T)
    (adj : F ⊣ G)
    (hf : sfRationalConstructibleLocalization l E T ⋙ Fq =
      F ⋙ sfRationalConstructibleLocalization l E X)
    (hg : sfRationalConstructibleLocalization l E X ⋙ Gq =
      G ⋙ sfRationalConstructibleLocalization l E T) :
    ∃ aq : Fq ⊣ Gq,
      (∀ K : sfIntegralConstructibleCategory l E T,
        HEq (aq.unit.app ((sfRationalConstructibleLocalization l E T).obj K))
          ((sfRationalConstructibleLocalization l E T).map (adj.unit.app K))) ∧
      (∀ K : sfIntegralConstructibleCategory l E X,
        HEq (aq.counit.app ((sfRationalConstructibleLocalization l E X).obj K))
          ((sfRationalConstructibleLocalization l E X).map (adj.counit.app K))) := by
  let Q := sfRationalConstructibleLocalization l E T
  let P := sfRationalConstructibleLocalization l E X
  let W := Rationalization.W
    (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
    (sfIntegralConstructibleCategory l E T)
  let V := Rationalization.W
    (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
    (sfIntegralConstructibleCategory l E X)
  have : Q.IsLocalization W := sfLocalization_isLocalization l E T
  have : P.IsLocalization V := sfLocalization_isLocalization l E X
  let : CatCommSq F Q P Fq := ⟨eqToIso hf.symm⟩
  let : CatCommSq G P Q Gq := ⟨eqToIso hg.symm⟩
  refine ⟨adj.localization Q W P V Fq Gq, ?_, ?_⟩
  · intro K
    rw [Adjunction.localization_unit_app]
    change HEq (Q.map (adj.unit.app K) ≫
      (eqToHom hg.symm).app (F.obj K) ≫
        Gq.map ((eqToHom hf.symm).app K)) _
    simp only [eqToHom_app, eqToHom_map, eqToHom_trans]
    exact comp_eqToHom_heq _ _
  · intro K
    rw [Adjunction.localization_counit_app]
    change HEq (Fq.map ((eqToHom hg).app K) ≫
      (eqToHom hf).app (G.obj K) ≫ P.map (adj.counit.app K)) _
    simp only [eqToHom_app, eqToHom_map, ← Category.assoc, eqToHom_trans]
    exact eqToHom_comp_heq _ _

private def sfReductionFullyFaithful (T : Scheme.{u}) :
    ((sfIntegralConstructible l E T).ι ⋙ FrobeniusExchange.reduction l E T).FullyFaithful := by
  let R := FrobeniusExchange.reduction l E T
  let adj := ((FrobeniusExchange.models l E).system T).adjunction
  have hi (K : sfIntegralConstructibleCategory l E T) : IsIso (adj.unit.app K.obj) :=
    (FrobeniusExchange.models l E).complete T K
  letI (K : sfIntegralConstructibleCategory l E T) : IsIso (adj.unit.app K.obj) := hi K
  refine { preimage := fun {K L} f ↦ ⟨adj.homEquiv _ _ f ≫ inv (adj.unit.app L.obj)⟩
           map_preimage := ?_
           preimage_map := ?_ }
  · intro K L f
    apply (adj.homEquiv _ _).injective
    simp only [Functor.comp_map, ObjectProperty.ι_map]
    simp [Adjunction.homEquiv_unit]
  · intro K L f
    apply ObjectProperty.hom_ext
    simp [Adjunction.homEquiv_unit]

private theorem sfNormalizedClosedAdjunction
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    {Z X : Scheme.{u}} [Z.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)] :
    ∃ adj : constructibleIntegralPullback l E i ⊣
        FrobeniusExchange.directImageFunctor l E k hl i,
      ∀ K : sfIntegralConstructibleCategory l E X,
        (FrobeniusExchange.reduction l E X).map (adj.unit.app K).hom ≫
          (FrobeniusExchange.operationReduction l E
            (FrobeniusExchange.systemDirect l E i)).app
              ((constructibleIntegralPullback l E i).obj K).obj ≫
          (FrobeniusExchange.systemDirect l E i).map
            ((sfLocalizationPullReduction l E i).app K.obj) =
          (FrobeniusExchange.systemAdjunction l E i).unit.app
            ((FrobeniusExchange.reduction l E X).obj K.obj) := by
  let F := constructibleIntegralPullback l E i
  let G := FrobeniusExchange.directImageFunctor l E k hl i
  let RX := FrobeniusExchange.reduction l E X
  let RZ := FrobeniusExchange.reduction l E Z
  let AX := ((FrobeniusExchange.models l E).system X).adjunction
  let A := FrobeniusExchange.systemAdjunction l E i
  let p : F ⋙ (sfIntegralConstructible l E Z).ι ⋙ RZ ≅
      (sfIntegralConstructible l E X).ι ⋙ RX ⋙
        integralComparisonDerivedSequencePullback l E i :=
    NatIso.ofComponents (fun K ↦
      @asIso _ _ _ _ ((sfLocalizationPullReduction l E i).app K.obj)
        ((FrobeniusExchange.models l E).effective i K))
      (fun f ↦ (sfLocalizationPullReduction l E i).naturality f.hom)
  let adj : F ⊣ G := (AX.comp A).restrictFullyFaithful
    (sfIntegralConstructible l E X).fullyFaithfulι
    (sfReductionFullyFaithful l E Z) p.symm (Iso.refl _)
  refine ⟨adj, ?_⟩
  intro K
  have hu : (adj.unit.app K).hom = AX.homEquiv _ _
      (A.homEquiv _ _ (p.inv.app K)) := by
    have hh := (AX.comp A).map_restrictFullyFaithful_unit_app
      (sfIntegralConstructible l E X).fullyFaithfulι
      (sfReductionFullyFaithful l E Z) (L := F) (R := G) p.symm (Iso.refl _) K
    change (adj.unit.app K).hom = _ at hh
    rw [hh]
    simp only [Adjunction.comp_unit_app, Functor.comp_map, Iso.refl_hom,
      NatTrans.id_app, Adjunction.homEquiv_unit,
      Functor.map_comp, Category.assoc]
    simp only [Iso.symm_hom]
    exact congrArg
      (fun f ↦ AX.unit.app K.obj ≫ (coefficientSequenceLimit l E X).map
        (A.unit.app (RX.obj K.obj)) ≫ f)
      (Category.comp_id ((coefficientSequenceLimit l E X).map
        ((FrobeniusExchange.systemDirect l E i).map (p.inv.app K))))
  rw [hu]
  change RX.map (AX.homEquiv _ _ (A.homEquiv _ _ (p.inv.app K))) ≫
    AX.counit.app _ ≫ (FrobeniusExchange.systemDirect l E i).map (p.hom.app K) = _
  have hAX : RX.map (AX.homEquiv _ _ (A.homEquiv _ _ (p.inv.app K))) ≫
      AX.counit.app _ = A.homEquiv _ _ (p.inv.app K) := by
    exact (AX.homEquiv_counit _ _
      (AX.homEquiv _ _ (A.homEquiv _ _ (p.inv.app K)))).symm.trans
        (Equiv.symm_apply_apply _ _)
  rw [← Category.assoc, hAX]
  rw [Adjunction.homEquiv_unit, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app]
  exact (congrArg (fun f ↦ A.unit.app (RX.obj K.obj) ≫ f)
    ((FrobeniusExchange.systemDirect l E i).map_id
      ((integralComparisonDerivedSequencePullback l E i).obj (RX.obj K.obj)))).trans
        (Category.comp_id _)

private theorem sfIntegralCrossHom {U Z X : Scheme.{u}}
    (J : sfIntegralConstructibleCategory l E U ⥤ sfIntegralConstructibleCategory l E X)
    (P : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E U)
    (I : sfIntegralConstructibleCategory l E Z ⥤ sfIntegralConstructibleCategory l E X)
    [J.CommShift ℤ] (adj : J ⊣ P) (hz : ∀ M, IsZero (P.obj (I.obj M)))
    (N : sfIntegralConstructibleCategory l E U)
    (M : sfIntegralConstructibleCategory l E Z) (m : ℤ) :
    Subsingleton ((J.obj N)⟦m⟧ ⟶ I.obj M) := by
  constructor
  intro f g
  apply (cancel_epi ((J.commShiftIso m).hom.app N)).1
  apply (adj.homEquiv (N⟦m⟧) (I.obj M)).injective
  exact (hz M).eq_of_tgt _ _

private theorem sfCrossHom {U Z X : Scheme.{u}}
    (J : sfIntegralConstructibleCategory l E U ⥤ sfIntegralConstructibleCategory l E X)
    (I : sfIntegralConstructibleCategory l E Z ⥤ sfIntegralConstructibleCategory l E X)
    (Jq : sfRationalConstructibleCategory l E U ⥤ sfRationalConstructibleCategory l E X)
    (Iq : sfRationalConstructibleCategory l E Z ⥤ sfRationalConstructibleCategory l E X)
    (hJ : ∀ N, Jq.obj N = (sfRationalConstructibleLocalization l E X).obj (J.obj N.obj))
    (hI : ∀ M, Iq.obj M = (sfRationalConstructibleLocalization l E X).obj (I.obj M.obj))
    (hz : ∀ N M (m : ℤ), Subsingleton ((J.obj N)⟦m⟧ ⟶ I.obj M)) :
    SfRationalCrossHom l E U Z X J I Jq Iq hJ hI := by
  intro N M m
  let Q := sfRationalConstructibleLocalization l E X
  have : Subsingleton ((J.obj N.obj)⟦m⟧ ⟶ I.obj M.obj) := hz N.obj M.obj m
  have ht : Subsingleton
      (((J.obj N.obj)⟦m⟧ ⟶ I.obj M.obj) ⊗[Padic.coefficientExtensionIntegers l E] E) :=
    inferInstance
  have hr : Subsingleton ((Jq.obj N)⟦m⟧ ⟶ Iq.obj M) := by
    rw [hJ N, hI M]
    let e := Iso.homCongr ((Q.commShiftIso m).app (J.obj N.obj)).symm
      (Iso.refl (Q.obj (I.obj M.obj)))
    refine @Function.Injective.subsingleton _ _ e e.injective ?_
    change Subsingleton (Localization.Away (Padic.coefficientExtensionUniformizer l E)
      ⊗[Padic.coefficientExtensionIntegers l E] ((J.obj N.obj)⟦m⟧ ⟶ I.obj M.obj))
    infer_instance
  have := hr
  have := ht
  refine ⟨hr, ht, ?_⟩
  let e : ((Jq.obj N)⟦m⟧ ⟶ Iq.obj M) ≃+
      (((J.obj N.obj)⟦m⟧ ⟶ I.obj M.obj) ⊗[Padic.coefficientExtensionIntegers l E] E) :=
    { toFun := fun _ ↦ 0
      invFun := fun _ ↦ 0
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _
      map_add' := fun _ _ ↦ Subsingleton.elim _ _ }
  refine ⟨e, fun _ _ ↦ Subsingleton.elim _ _, ?_⟩
  intro e' _
  exact AddEquiv.ext (fun _ ↦ Subsingleton.elim _ _)

private theorem sfTriangle_transport
    {C : Type*} [Category C] [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {A B C₀ A' B' C₀' : C} (ha : A' = A) (hb : B' = B) (hc : C₀' = C₀)
    (f : A ⟶ B) (g : B ⟶ C₀) (δ : C₀ ⟶ A⟦(1 : ℤ)⟧)
    (f' : A' ⟶ B') (g' : B' ⟶ C₀') (hf : HEq f' f) (hg : HEq g' g)
    (hΔ : Triangle.mk f g δ ∈ distTriang C) :
    ∃ δ' : C₀' ⟶ A'⟦(1 : ℤ)⟧,
      Triangle.mk f' g' δ' ∈ distTriang C ∧ HEq δ' δ := by
  subst A'; subst B'; subst C₀'
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hg
  exact ⟨δ, hΔ, HEq.rfl⟩

/-- Raw rationalization of the normalized four operations, the specified adjunctions
on all rational arrows, every integral distinguished completion, and cross-object
orthogonality in every integer degree.
Source: main-20261015 rational-stage paragraph
(blueprint: lem-sf-rational-localization-triangle-orthogonality).

Proof plan:
1. By lem-sf-open-roos-unit-adjunction the geometry is Noetherian and the complementary
open is quasi-compact.
The DVR quotients are finite and perfect; coefficient inverse-image comparisons
preserve constants and quotient projections by
lem-weil-pbc-profinite-coefficient-inverse-image.
2. The actual completed-coefficient immersion pullbacks, closed direct image and
open extension are exact by lem-weil-pbc-proetale-ringed-open-closed and
lem-weil-pbc-proetale-immersion-limit-preservation. The exact-derived-functor nodes
lem-sf-exact-functor-derived-triangulated and lem-weil-pbc-exact-functor-derived-functor
supply their termwise R-linear exact derived functors.
3. The completed-pullback comparison, strict open reduction comparison and canonical
direct-image limit comparison identify their restrictions with the recorded operations:
lem-a1-integral-pullback-completed-comparison,
lem-sf-immersion-completed-pullback-comparison,
lem-sf-integral-open-reduction-comparison and prop-weil-pbc-direct-image-limits.
The lem-sf-open-finite-constructibility-interval and
lem-sf-finite-immersion-constructibility-interval preserve the integral full subcategories.
4. Restrict the actual derived adjunctions of lem-sc-derived-adjunction-from-underived.
Coherent-system realization fixes the
open counit and closed unit by the two displayed normalization equations.
5. Extend each linear Hom map by tensors. lem-pur-semilinear-scalar-localization
supplies exactness, transformations and the localized shift comparisons; uniqueness
identifies the published rational pullbacks and open compact-support functor.
6. Tensor the units and counits with one. Naturality on every sum of pure tensors
and the localized triangle identities give the adjunctions on all rational arrows,
without choosing an integral representative of such an arrow.
7. lem-weil-linear-scalar-localization-triangulated makes Q exact, so it carries every
integral completion to a distinguished triangle;
its final arrow is Q(delta) followed by the canonical shift comparison.
8. For independent N,M, the open adjunction and j*i*=0 kill the integral cross Hom
in every shift. The canonical Hom coordinates identify its rational counterpart with
that group tensored with E, which is zero. Empty opens, empty closed schemes, torsion
objects and negative shifts are all included. -/
theorem sfRationalLocalizationTriangleOrthogonality
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {Z U X : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ) :
    Nonempty (SfRationalLocalizationOrthogonality l E D i j) := by
  obtain ⟨S⟩ := IntegralSupportNormalization.integralSupportFunctorNormalization l E D hl i j hij
  let := S.openOver
  let := S.closedOver
  let := S.openIsOver
  let := S.closedIsOver
  let := S.openFiniteType
  let := S.openQuasiCompact
  let := S.closedFiniteType
  let := S.closedQuasiCompact
  let := S.openQuasiCompactMap
  let := S.invertibleX
  let := S.invertibleU
  let := S.invertibleZ
  let := S.openShift
  let := S.closedShift
  have := S.openExact
  have := S.closedExact
  have := S.openLinear
  have := S.closedLinear
  let J := sfCompactSupportFiniteIntegralFunctor l D.k S.primeUnit
    (Compactification.ofIsOpenImmersion j) E
  let I := FrobeniusExchange.directImageFunctor l E D.k S.primeUnit i
  let P := constructibleIntegralPullback l E j
  let C := constructibleIntegralPullback l E i
  have : P.Additive := S.openAdjunction.right_adjoint_additive
  have : P.Linear (Padic.coefficientExtensionIntegers l E) :=
    S.openAdjunction.right_adjoint_linear
  have : C.Additive := S.closedAdjunction.left_adjoint_additive
  have : C.Linear (Padic.coefficientExtensionIntegers l E) :=
    S.closedAdjunction.left_adjoint_linear
  let : P.CommShift ℤ := S.openAdjunction.rightAdjointCommShift ℤ
  have : S.openAdjunction.CommShift ℤ := S.openAdjunction.commShift_of_leftAdjoint ℤ
  have : P.IsTriangulated := S.openAdjunction.isTriangulated_rightAdjoint
  let : C.CommShift ℤ := S.closedAdjunction.leftAdjointCommShift ℤ
  have : S.closedAdjunction.CommShift ℤ := S.closedAdjunction.commShift_of_rightAdjoint ℤ
  have : C.IsTriangulated := S.closedAdjunction.isTriangulated_leftAdjoint
  let Pq := rationalDerivedPullback l E j
  let Cq := rationalDerivedPullback l E i
  let Jq := sfCompactSupportFiniteFunctor l D.k S.primeUnit
    (Compactification.ofIsOpenImmersion j) E
  have hp := (rationalDerivedPullback_existsUnique l E j).exists.choose_spec
  have hc := (rationalDerivedPullback_existsUnique l E i).exists.choose_spec
  have : Pq.Additive := hp.1
  have : Cq.Additive := hc.1
  have : Jq.Additive := ⟨fun {K L} f g ↦
    (sfCompactSupportFiniteHomMap l D.k S.primeUnit
      (Compactification.ofIsOpenImmersion j) E K L).map_add f g⟩
  have hjobj : ∀ K, Jq.obj K = (sfRationalConstructibleLocalization l E X).obj
      (J.obj K.obj) := fun _ ↦ rfl
  have hjtensor : ∀ (K L : sfIntegralConstructibleCategory l E U) (f : K ⟶ L)
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
      HEq (Jq.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f))
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] J.map f) := by
    intro K L f a
    apply heq_of_eq
    exact LinearMap.baseChange_tmul _ _ _
  let t := Padic.coefficientExtensionUniformizer l E
  have hlin : IsSemilinear (RingHom.id (Padic.coefficientExtensionIntegers l E)) I :=
    fun _ _ r f ↦ I.map_smul r f
  let Iq := extension t t (RingHom.id _) (IsLocalization.Away.algebraMap_isUnit t) I hlin
  have hiobj : ∀ K, Iq.obj K = (sfRationalConstructibleLocalization l E X).obj
      (I.obj K.obj) := fun _ ↦ rfl
  have hitensor : ∀ (K L : sfIntegralConstructibleCategory l E Z) (f : K ⟶ L)
      (a : Localization.Away t), HEq (Iq.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f))
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] I.map f) := by
    intro K L f a
    change HEq (extensionHom t t (RingHom.id _) _ I hlin K L (a ⊗ₜ f)) _
    have hm : coefficientMap t t (RingHom.id _) (IsLocalization.Away.algebraMap_isUnit t) =
        RingHom.id (Localization.Away t) := by
      symm
      apply (coefficientMap_unique _ _ _ _ _).1
      rfl
    apply heq_of_eq
    exact (extensionHom_tmul t t (RingHom.id _) (IsLocalization.Away.algebraMap_isUnit t)
      I hlin K L a f).trans (by rw [hm]; rfl)
  obtain ⟨p⟩ := sfRationalizedExact l E P Pq hp.2.1 hp.2.2
  obtain ⟨c⟩ := sfRationalizedExact l E C Cq hc.2.1 hc.2.2
  obtain ⟨jE⟩ := sfRationalizedExact l E J Jq hjobj hjtensor
  obtain ⟨iE⟩ := sfRationalizedExact l E I Iq hiobj hitensor
  obtain ⟨aI, haI⟩ := sfNormalizedClosedAdjunction l E D.k S.primeUnit i
  obtain ⟨aj, hju, hjc⟩ := sfLocalizedAdjunction l E J P Jq Pq S.openAdjunction
    (sfLocalization_factor l E J Jq hjobj hjtensor)
    (sfLocalization_factor l E P Pq hp.2.1 hp.2.2)
  obtain ⟨ai, hiu, hic⟩ := sfLocalizedAdjunction l E C I Cq Iq aI
    (sfLocalization_factor l E C Cq hc.2.1 hc.2.2)
    (sfLocalization_factor l E I Iq hiobj hitensor)
  refine ⟨{
    primeUnit := S.primeUnit
    openOver := S.openOver
    closedOver := S.closedOver
    openIsOver := S.openIsOver
    closedIsOver := S.closedIsOver
    openFiniteType := S.openFiniteType
    openQuasiCompact := S.openQuasiCompact
    closedFiniteType := S.closedFiniteType
    closedQuasiCompact := S.closedQuasiCompact
    openQuasiCompactMap := S.openQuasiCompactMap
    invertibleX := S.invertibleX
    invertibleU := S.invertibleU
    invertibleZ := S.invertibleZ
    closedRationalImage := Iq
    openIntegralAdjunction := S.openAdjunction
    closedIntegralAdjunction := aI
    openCounitNormalization := ?_
    closedUnitNormalization := haI
    closedPull := c
    openPull := p
    closedPush := iE
    openPush := jE
    openRationalAdjunction := aj
    closedRationalAdjunction := ai
    openUnit := hju
    openCounit := hjc
    closedUnit := hiu
    closedCounit := hic
    triangles := ?_
    orthogonality := sfCrossHom l E J I Jq Iq jE.objects iE.objects
      (sfIntegralCrossHom l E J P I S.openAdjunction S.disjoint) }⟩
  · set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    intro K
    rw [S.openSystemCounit]
    dsimp only [sfLocalizationOpenRealization, sfLocalizationSystemDirectId,
      IntegralSupportNormalization.systemDirectId,
      sfLocalizationPullReduction, FrobeniusExchange.compactOperationReduction,
      FrobeniusExchange.operationReduction, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [Functor.map_comp, Category.assoc]
    let α := (sfLocalizationSystemDirectId l E X).hom.app
      ((FrobeniusExchange.systemDerivedOpen l E j).obj
        ((FrobeniusExchange.reduction l E U).obj (P.obj K).obj))
    have hn := (((FrobeniusExchange.models l E).system X).adjunction.counit).naturality α
    simpa only [Functor.comp_map, Functor.id_map, Functor.comp_obj,
      Functor.id_obj, ObjectProperty.ι_obj, Compactification.ofIsOpenImmersion,
      sfLocalizationSystemDirectId, sfLocalizationPullReduction, α, P, Category.assoc] using
      congrArg (fun f ↦ (FrobeniusExchange.reduction l E X).map
        ((FrobeniusExchange.compactRealization l E D.k S.primeUnit j
          (Compactification.ofIsOpenImmersion j)).hom.app (P.obj K)) ≫ f ≫
          (FrobeniusExchange.systemDerivedOpen l E j).map
            ((sfLocalizationPullReduction l E j).app K.obj) ≫
          (FrobeniusExchange.systemDerivedOpenAdjunction l E j).counit.app
            ((FrobeniusExchange.reduction l E X).obj K.obj)) hn.symm
  · set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    intro K δ hδ
    let Q := sfRationalConstructibleLocalization l E X
    have hΔ := Q.map_distinguished _ hδ
    let hjv := hjobj (Pq.obj (Q.obj K)) |>.trans
      (congrArg (fun A ↦ Q.obj (J.obj A)) (congrArg ScalarLocalization.obj (hp.2.1 (Q.obj K))))
    let hiv := hiobj (Cq.obj (Q.obj K)) |>.trans
      (congrArg (fun A ↦ Q.obj (I.obj A)) (congrArg ScalarLocalization.obj (hc.2.1 (Q.obj K))))
    exact sfTriangle_transport hjv rfl hiv
      (Q.map (S.openAdjunction.counit.app K)) (Q.map (aI.unit.app K))
      (Q.map δ ≫ (Q.commShiftIso (1 : ℤ)).hom.app (J.obj (P.obj K)))
      (aj.counit.app (Q.obj K)) (ai.unit.app (Q.obj K)) (hjc K) (hiu K) hΔ

end WeilConjectures
