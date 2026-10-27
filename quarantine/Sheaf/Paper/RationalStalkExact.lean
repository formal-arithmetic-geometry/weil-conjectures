/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.LocalFrobeniusTrace
import Sheaf.Paper.IntegralPullbackComposition
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.Paper.DlConstructibleFibresExact
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.IntegralPullbackComparisonRealization
import Sheaf.Paper.LocalFrobeniusTransportNormalization
import Sheaf.SixFunctors.FrobeniusPointTransportNatural

/-!
# Exact rational coefficient fibres with local Frobenius

Source: Bhatt--Scholze, Corollary 6.8.5, Lemma 6.8.7, Proposition 6.8.14 and
Remark 6.8.15; the opening punctual-bounds argument of blueprint
sec-deligne-laumon-a1/sk-l-dl-a1-energy/lem-wf-l2-upper.proof.md
(blueprint: lem-wf-rational-stalk-exact).
The helpers extend the recorded local operator to the literal common-stage category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The defining object identification for common-stage pullback.
Source: recorded common-stage pullback formula
(blueprint: lem-wf-rational-stalk-exact). -/
def wfPullbackObjectIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonStageDerivedPullback l Ω f).obj K ≅ commonStagePullbackObject l Ω f K :=
  eqToIso ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 K)

/-- Localize the specified integral composition comparison at the object's own stage.
Source: local-Frobenius pullback-composition convention
(blueprint: lem-wf-rational-stalk-exact). -/
def wfPullbackComposition {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    (commonStageDerivedPullback l Ω (h ≫ k)).obj K ≅
      (commonStageDerivedPullback l Ω h).obj ((commonStageDerivedPullback l Ω k).obj K) :=
  wfPullbackObjectIso l Ω (h ≫ k) K ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) K.stage).mapIso
      (localPullbackComposition l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage)
        h k K.obj) ≪≫
    (wfPullbackObjectIso l Ω h (commonStagePullbackObject l Ω k K)).symm ≪≫
    (commonStageDerivedPullback l Ω h).mapIso (wfPullbackObjectIso l Ω k K).symm

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The canonical common-stage geometric-point complex functor.
Source: Bhatt--Scholze 6.8.14 and the rational coefficient-fibre convention
(blueprint: lem-wf-rational-stalk-exact). -/
def wfPointFunctor (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left ⥤
      DerivedCategory.PointFdQbar l Ω :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  commonStageDerivedPullback l Ω x ⋙ pointQbarFibre D l hl Ω

/-- The Weil isomorphism iterated with the prescribed composition comparisons.
The index n represents exponent n+1, as in localWeilIterate.
Source: the local-Frobenius definition (blueprint: lem-wf-rational-stalk-exact). -/
def wfWeilIterate (K : sfCommonStageWeilComplex D l hl Y₀ Ω) :
    (n : ℕ) →
    (@commonStageDerivedPullback l _ Ω _ _ _ _ _
      (localPositivePower (D.geometricFrobenius Y₀).hom n)
      (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).obj K.carrier ≅
      K.carrier
  | 0 => K.str
  | n + 1 =>
    letI := sfWeilPrimeInvertible D l hl Y₀
    wfPullbackComposition l Ω (localPositivePower (D.geometricFrobenius Y₀).hom n)
      (D.geometricFrobenius Y₀).hom K.carrier ≪≫
      (commonStageDerivedPullback l Ω
        (localPositivePower (D.geometricFrobenius Y₀).hom n)).mapIso K.str ≪≫
      wfWeilIterate K n

/-- Point transport, at the object's finite coefficient stage, to the actual pullback.
Source: the recorded point transport and local-Frobenius convention
(blueprint: lem-wf-rational-stalk-exact). -/
def wfPointTransport
    (N : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :=
  letI := frobeniusPointPrimeInvertible D l hl
  let e := wfPullbackObjectIso l Ω (frobeniusPointIso D).hom N
  eqToHom ((pointQbarFibre_existsUnique D l hl Ω).exists.choose_spec.1 N) ≫
    frobeniusPointTransportQbar D l hl Ω N ≫
    eqToHom (((pointQbarFibre_existsUnique D l hl Ω).exists.choose_spec.1
      (frobeniusPointQbarPullbackObj D l hl Ω N)).symm) ≫
    (pointQbarFibre D l hl Ω).map
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := Spec (.of D.k)) N.stage).mapIso
          (localPullbackObjectIso l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N.stage)
            (frobeniusPointIso D).hom N.obj).symm).hom ≫
    (pointQbarFibre D l hl Ω).map e.inv

/-- Iterated point transport; n represents exponent n+1.
Source: the local-Frobenius definition (blueprint: lem-wf-rational-stalk-exact). -/
def wfPointTransportIterate
    (N : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    (n : ℕ) → (pointQbarFibre D l hl Ω).obj N ⟶
      (pointQbarFibre D l hl Ω).obj
        ((@commonStageDerivedPullback l _ Ω _ _ _ _ _
          (localPositivePower (frobeniusPointIso D).hom n)
          (frobeniusPointPrimeInvertible D l hl)
          (frobeniusPointPrimeInvertible D l hl)).obj N)
  | 0 => wfPointTransport l Ω D hl N
  | n + 1 =>
    letI := frobeniusPointPrimeInvertible D l hl
    wfPointTransport l Ω D hl N ≫
      wfPointTransportIterate
        ((commonStageDerivedPullback l Ω (frobeniusPointIso D).hom).obj N) n ≫
      (pointQbarFibre D l hl Ω).map
        (wfPullbackComposition l Ω (localPositivePower (frobeniusPointIso D).hom n)
          (frobeniusPointIso D).hom N).inv

/-- The local geometric Frobenius on a common-stage point complex at a closed point.
The return is reparametrization of Spec(k), with the closed point's actual residue degree.
Source: the closed-point local-Frobenius definition
(blueprint: lem-wf-rational-stalk-exact). -/
def wfClosedFrobenius (K : sfCommonStageWeilComplex D l hl Y₀ Ω)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    (wfPointFunctor l Ω D hl Y₀ (localClosedPoint D Y₀ y ι hι)).obj K.carrier ⟶
      (wfPointFunctor l Ω D hl Y₀ (localClosedPoint D Y₀ y ι hι)).obj K.carrier :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  let x := localClosedPoint D Y₀ y ι hι
  let n := localClosedPointDegree D Y₀ y - 1
  let N := (commonStageDerivedPullback l Ω x).obj K.carrier
  let c := (wfPullbackComposition l Ω (localPositivePower (frobeniusPointIso D).hom n)
      x K.carrier).symm ≪≫
    eqToIso (congrArg (fun f ↦ (commonStageDerivedPullback l Ω f).obj K.carrier)
      (localClosedPoint_return D Y₀ y ι hι).symm) ≪≫
    wfPullbackComposition l Ω x (localPositivePower (D.geometricFrobenius Y₀).hom n) K.carrier
  wfPointTransportIterate l Ω D hl N n ≫
    (pointQbarFibre D l hl Ω).map c.hom ≫
    (pointQbarFibre D l hl Ω).map
      ((commonStageDerivedPullback l Ω x).map (wfWeilIterate l Ω D hl Y₀ K n).hom)

/-- Forget the Weil structure, retaining the same object in the constructible heart.
Source: the fixed-pair and full-heart definitions
(blueprint: lem-wf-rational-stalk-exact). -/
def wfHeartForget : sfCommonStageWeilSheaf D l hl Y₀ Ω ⥤
    sfCommonStageHeart l (D.geometricFiber Y₀).left Ω where
  obj K := ⟨K.obj.carrier, K.property⟩
  map f := ObjectProperty.homMk f.hom.hom.f

/-- The degree-zero rational coefficient fibre, including scalar realization in Ω.
Source: Bhatt--Scholze Proposition 6.8.14 and the coefficient cohomology convention
(blueprint: lem-wf-rational-stalk-exact). -/
def wfSheafFibre (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    sfCommonStageWeilSheaf D l hl Y₀ Ω ⥤ ModuleCat.{u} Ω :=
  wfHeartForget l Ω D hl Y₀ ⋙
    (sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Ω).ι ⋙
    wfPointFunctor l Ω D hl Y₀ x ⋙ DerivedCategory.coefficientQbarCohomology l Ω 0

/-- The local geometric Frobenius on the degree-zero rational fibre of a Weil sheaf.
Source: the closed-point local operator followed by coefficient H^0
(blueprint: lem-wf-rational-stalk-exact). -/
def wfSheafClosedFrobenius (K : sfCommonStageWeilSheaf D l hl Y₀ Ω)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    (wfSheafFibre l Ω D hl Y₀ (localClosedPoint D Y₀ y ι hι)).obj K ⟶
      (wfSheafFibre l Ω D hl Y₀ (localClosedPoint D Y₀ y ι hι)).obj K :=
  (DerivedCategory.coefficientQbarCohomology l Ω 0).map
    (wfClosedFrobenius l Ω D hl Y₀ K.obj y ι hι)

/-- A short exact sequence of constructible rational Weil sheaves has short exact
finite-dimensional coefficient fibres; both induced maps intertwine local geometric
Frobenius. Short exactness of Weil sheaves means short exactness in the underlying
constructible heart; the two arrows are required to be Weil morphisms.
Source: Bhatt--Scholze Corollary 6.8.5, Lemma 6.8.7, Proposition 6.8.14 and
Remark 6.8.15 (blueprint: lem-wf-rational-stalk-exact).
Proof: apply lem-dl-a1-constructible-fibres-exact to the forgotten sequence, using
separated finite type and l ≠ p, to obtain short exact finite-dimensional fibres.
Represent the two Weil maps, their inverse structure maps and equations at a common
finite coefficient field E, enlarging the field to realize their finitely many
relations. For T = Lg_Y^*, induction on n gives
u theta_K^[n] = theta_L^[n] T^n(u), starting with the defining Weil morphism square.
At n = [κ(y):k₀], naturality of point transport and of the specified composition
comparisons gives P(T^n u) J_K = J_L P(u), for P = Fib_s Lx^*.
Since F_y = P(theta^[n]) J, composition gives P(u) F_K = F_L P(u).
The return used here is g_Y^n x = x g_s^n. The composition/scalar equations of
lem-trf-integral-pullback-comparison-realization and the coefficient equation of
lem-trf-local-frobenius-transport-normalization identify this composite after every
further finite extension, including identities and towers. Thus it descends in the
recorded common-stage category. Apply coefficient H^0 and scalar realization to Ω
to obtain the asserted two intertwining equations. -/
theorem wfRationalStalkExact [IsSeparated Y₀.hom]
    (F₁ F₂ F₃ : sfCommonStageWeilSheaf D l hl Y₀ Ω) (i : F₁ ⟶ F₂) (j : F₂ ⟶ F₃)
    (w : (wfHeartForget l Ω D hl Y₀).map i ≫
      (wfHeartForget l Ω D hl Y₀).map j = 0)
    (hS : (ShortComplex.mk ((wfHeartForget l Ω D hl Y₀).map i)
      ((wfHeartForget l Ω D hl Y₀).map j) w).ShortExact)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    ∃ w' : (wfSheafFibre l Ω D hl Y₀ (localClosedPoint D Y₀ y ι hι)).map i ≫
        (wfSheafFibre l Ω D hl Y₀ (localClosedPoint D Y₀ y ι hι)).map j = 0,
      (ShortComplex.mk
        ((wfSheafFibre l Ω D hl Y₀ (localClosedPoint D Y₀ y ι hι)).map i)
        ((wfSheafFibre l Ω D hl Y₀ (localClosedPoint D Y₀ y ι hι)).map j) w').ShortExact ∧
      FiniteDimensional Ω
        ((wfSheafFibre l Ω D hl Y₀ (localClosedPoint D Y₀ y ι hι)).obj F₁) ∧
      FiniteDimensional Ω
        ((wfSheafFibre l Ω D hl Y₀ (localClosedPoint D Y₀ y ι hι)).obj F₂) ∧
      FiniteDimensional Ω
        ((wfSheafFibre l Ω D hl Y₀ (localClosedPoint D Y₀ y ι hι)).obj F₃) ∧
      ((wfSheafFibre l Ω D hl Y₀ (localClosedPoint D Y₀ y ι hι)).map i ≫
          wfSheafClosedFrobenius l Ω D hl Y₀ F₂ y ι hι =
        wfSheafClosedFrobenius l Ω D hl Y₀ F₁ y ι hι ≫
          (wfSheafFibre l Ω D hl Y₀ (localClosedPoint D Y₀ y ι hι)).map i) ∧
      ((wfSheafFibre l Ω D hl Y₀ (localClosedPoint D Y₀ y ι hι)).map j ≫
          wfSheafClosedFrobenius l Ω D hl Y₀ F₃ y ι hι =
        wfSheafClosedFrobenius l Ω D hl Y₀ F₂ y ι hι ≫
          (wfSheafFibre l Ω D hl Y₀ (localClosedPoint D Y₀ y ι hι)).map j) := by
  sorry

end WeilConjectures
