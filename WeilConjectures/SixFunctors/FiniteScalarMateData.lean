/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteAdjunctionDiagramRealization
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SixFunctors.FiniteExceptional
public import WeilConjectures.AlgebraicGeometry.FiniteFreeCoefficientExtension
public import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.SystemOperationExchangeRealization
public import WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison
public import WeilConjectures.CategoryTheory.StrictTowerArithmeticRestrictionDefs
public import WeilConjectures.AlgebraicGeometry.IntegralPullbackComparisonRealization
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement

/-! # Coherent finite scalar mates and their integral realization

Source: the coefficient-extension paragraph of the exceptional-image proof,
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/`;
Stacks 0941, 079P and 07A6 (blueprint: def-coef-finite-scalar-mate-data).
Index n denotes exponent n+1. The retained upper index is e*(n+1)-1.
All system morphisms below are formed in ordinary derived categories of strict
systems. Retaining the upper indices composes the actual quotient transitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteScalarMate

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L)

/-- Retaining precisely the positive exponents en, rather than the exponents n.
Source: the node's B tower (blueprint: def-coef-finite-scalar-mate-data). -/
abbrev retainedIndex (e n : ℕ) : ℕ :=
  ((CategoryTheory.StrictTowerArithmetic.index e).obj (op n)).unop

/-- The positive-exponent convention for the retained quotient.
Source: the node's B tower (blueprint: def-coef-finite-scalar-mate-data).
Proof: e and n+1 are positive; subtracting one and then adding one cancels. -/
theorem retainedIndex_succ (e : ℕ) (he : 1 ≤ e) (n : ℕ) :
    retainedIndex e n + 1 = e * (n + 1) := by
  exact Nat.sub_add_cancel (Nat.mul_pos he (Nat.succ_pos n))

/-- Retained indices preserve every quotient arrow, including equal indices.
Source: the retained B tower (blueprint: def-coef-finite-scalar-mate-data).
Proof: multiply n+1 ≤ m+1 by e and subtract one from both sides. -/
theorem retainedIndex_mono (e : ℕ) {m n : ℕ} (h : n ≤ m) :
    retainedIndex e n ≤ retainedIndex e m := by
  exact Nat.sub_le_sub_right (Nat.mul_le_mul_left e (Nat.add_le_add_right h 1)) 1

/-- Restrict the strict completed-coefficient tower to the retained exponents.
It composes the actual quotient transitions before derived localization.
Source: total-limit realization in the node
(blueprint: def-coef-finite-scalar-mate-data). -/
def retainedRestriction (W : Scheme.{u}) (e : ℕ) :
    coefficientSequenceModules l L W ⥤ (ℕᵒᵖ ⥤ scalarReductionSource l L W) :=
  coefficientSequenceRestriction l L W ⋙
    CategoryTheory.StrictTowerArithmetic.restriction (scalarReductionSource l L W) e

/-- Additivity of strict subsequence restriction is componentwise additivity.
Source: the retained tower in the node
(blueprint: def-coef-finite-scalar-mate-data). -/
instance retainedRestrictionAdditive (W : Scheme.{u}) (e : ℕ) :
    (retainedRestriction l L W e).Additive := by
  dsimp only [retainedRestriction]
  infer_instance

/-- Exact subsequence restriction preserves kernels component by component.
Source: the strict tower in the node
(blueprint: def-coef-finite-scalar-mate-data). -/
instance retainedRestrictionLimits (W : Scheme.{u}) (e : ℕ) :
    PreservesFiniteLimits (retainedRestriction l L W e) := by
  dsimp only [retainedRestriction]
  infer_instance

/-- Exact subsequence restriction preserves cokernels component by component.
Source: the strict tower in the node
(blueprint: def-coef-finite-scalar-mate-data). -/
instance retainedRestrictionColimits (W : Scheme.{u}) (e : ℕ) :
    PreservesFiniteColimits (retainedRestriction l L W e) := by
  dsimp only [retainedRestriction]
  infer_instance

/-- Localize the exact restriction of entire strict towers.
Source: the coherent B-system realization in the node
(blueprint: def-coef-finite-scalar-mate-data). -/
def retainedDerivedRestriction (W : Scheme.{u}) (e : ℕ) :
    coefficientSequenceDerived l L W ⥤ coefficientSequenceRestrictedDerived l L W :=
  (retainedRestriction l L W e).mapDerivedCategory

/-- Total derived limit of the retained tower after restriction to completed coefficients.
Source: the total inverse limit in the node
(blueprint: def-coef-finite-scalar-mate-data). -/
def retainedLimit (W : Scheme.{u}) (e : ℕ) :
    coefficientSequenceDerived l L W ⥤ DerivedCategory (scalarReductionSource l L W) :=
  retainedDerivedRestriction l L W e ⋙ coefficientConstantTowerLimit l L W

/-- Total-limit comparison with the published strict Roos cone, before retention.
Source: simultaneous total limit in the node
(blueprint: def-coef-finite-scalar-mate-data). -/
def fullRoosComparison (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l L W) ℤ) :=
  (coefficientConstantTowerLimit l L W).map
      ((coefficientSequenceRestriction l L W).mapDerivedCategoryFactors.hom.app C) ≫
    ((FrobeniusExchange.models l L).roos W).comparison.hom.app
      (((coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)).obj C)

/-- Total-limit comparison with the same strict cone after retaining the en tower.
Source: canonical cofinal limit in the node
(blueprint: def-coef-finite-scalar-mate-data). -/
def retainedRoosComparison (W : Scheme.{u}) (e : ℕ)
    (C : CochainComplex (coefficientSequenceModules l L W) ℤ) :=
  (coefficientConstantTowerLimit l L W).map
      ((retainedRestriction l L W e).mapDerivedCategoryFactors.hom.app C) ≫
    ((FrobeniusExchange.models l L).roos W).comparison.hom.app
      (((retainedRestriction l L W e).mapHomologicalComplex (.up ℤ)).obj C)

/-- The published ramified coefficient map, transported only along the exponent equality.
Source: the node's A-to-B inclusion
(blueprint: def-coef-finite-scalar-mate-data). -/
def finiteChange (e : ℕ) (he : PurCompactSupport.Ramification l E L i e) (hp : 1 ≤ e)
    (n : ℕ) : PurCompactSupport.Change (PurCompactSupport.finite l E (n + 1)
      (Nat.succ_pos n)) (PurCompactSupport.finite l L (retainedIndex e n + 1)
        (Nat.succ_pos (retainedIndex e n))) := by
  simpa only [retainedIndex_succ e hp n] using
    PurCompactSupport.finiteChange l E L i e he hp (n + 1) (Nat.succ_pos n)

/-- Actual derived tensor with B at the retained exponent.
Source: T_{W,n} in the node (blueprint: def-coef-finite-scalar-mate-data). -/
abbrev finiteTensor (e : ℕ) (he : PurCompactSupport.Ramification l E L i e)
    (hp : 1 ≤ e) (W : Scheme.{u}) (n : ℕ) :
    proEtaleDerivedCategory W (Padic.coefficientExtensionRing l E (n + 1)) ⥤
      proEtaleDerivedCategory W
        (Padic.coefficientExtensionRing l L (retainedIndex e n + 1)) :=
  pbcDerivedExtend ((finiteChange l E L i e he hp n).map W)

/-- The coefficient square is the equality of the actual quotient ring sheaf maps.
Source: quotient squares in the node
(blueprint: def-coef-finite-scalar-mate-data).
Proof: quotient induction reduces both paths to the residue of i(x), and the
constant-sheaf functor preserves that equality. Equal indices give identity maps. -/
theorem quotientSquare (e : ℕ) (he : PurCompactSupport.Ramification l E L i e)
    (hp : 1 ≤ e) (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    (finiteChange l E L i e he hp m).map W ≫
      (PurCompactSupport.finiteQuotientChange l L
        (retainedIndex e m + 1) (retainedIndex e n + 1)
        (Nat.succ_pos _) (Nat.succ_pos _)
        (Nat.add_le_add_right (retainedIndex_mono e h) 1)).map W =
    (PurCompactSupport.finiteQuotientChange l E (m + 1) (n + 1)
      (Nat.succ_pos m) (Nat.succ_pos n) (Nat.add_le_add_right h 1)).map W ≫
        (finiteChange l E L i e he hp n).map W := by
  cases e with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hp)
  | succ e =>
    change
      (PurCompactSupport.finiteChange l E L i (e + 1) he hp (m + 1)
        (Nat.succ_pos m)).map W ≫
        PurCompactSupport.finiteQuotient l L ((e + 1) * (m + 1))
          ((e + 1) * (n + 1)) (Nat.mul_pos hp (Nat.succ_pos m))
          (Nat.mul_pos hp (Nat.succ_pos n))
          (Nat.mul_le_mul_left (e + 1) (Nat.add_le_add_right h 1)) W =
      PurCompactSupport.finiteQuotient l E (m + 1) (n + 1)
        (Nat.succ_pos m) (Nat.succ_pos n) (Nat.add_le_add_right h 1) W ≫
        (PurCompactSupport.finiteChange l E L i (e + 1) he hp (n + 1)
          (Nat.succ_pos n)).map W
    exact PurCompactSupport.ramified_quotient_square l E L i (e + 1) he hp
      (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n)
      (Nat.add_le_add_right h 1) W

/-- The canonical scalar/quotient square is tensor reassociation, normalized by
its actual scalar-adjunction units. Source: finite-free coefficient squares
(blueprint: def-coef-finite-scalar-mate-data). -/
def quotientTensorSquare (e : ℕ) (he : PurCompactSupport.Ramification l E L i e)
    (hp : 1 ≤ e) (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :=
  PurCompactSupport.tensorSquare
    ((finiteChange l E L i e he hp m).map W)
    ((finiteChange l E L i e he hp n).map W)
    ((PurCompactSupport.finiteQuotientChange l E (m + 1) (n + 1)
      (Nat.succ_pos m) (Nat.succ_pos n) (Nat.add_le_add_right h 1)).map W)
    ((PurCompactSupport.finiteQuotientChange l L
      (retainedIndex e m + 1) (retainedIndex e n + 1)
      (Nat.succ_pos _) (Nat.succ_pos _)
      (Nat.add_le_add_right (retainedIndex_mono e h) 1)).map W)
    (quotientSquare l E L i e he hp W h)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- The canonical comparison to the fixed whole-system proper/open model.
Both factors are adjoint-uniqueness comparisons for the actual ordinary units.
Source: simultaneous realization in the node
(blueprint: def-coef-finite-scalar-mate-data). -/
def supportModel
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y}
    (r : FiniteAdjunctionDiagram.Realization l E D hl f c SX SZ SY) :
    r.support.functor ≅
      FrobeniusExchange.systemDerivedOpen l E c.i ⋙ FrobeniusExchange.systemDirect l E c.g :=
  Functor.isoWhiskerLeft _
      ((r.support.properGeometry.adjunction l E).rightAdjointUniq
        (FrobeniusExchange.systemAdjunction l E c.g)) ≪≫
    Functor.isoWhiskerRight
      (r.support.openAdj.leftAdjointUniq
        (FrobeniusExchange.systemDerivedOpenAdjunction l E c.i)) _

/-- Presentation of the restricted system support functor in that fixed model.
Source: the same simultaneous realization
(blueprint: def-coef-finite-scalar-mate-data). -/
def supportPresentation
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y}
    (r : FiniteAdjunctionDiagram.Realization l E D hl f c SX SZ SY) :
    r.F ⋙ (FiniteAdjunctionDiagram.domain l E Y).ι ≅
      (FiniteAdjunctionDiagram.domain l E X).ι ⋙
        (FrobeniusExchange.systemDerivedOpen l E c.i ⋙ FrobeniusExchange.systemDirect l E c.g) :=
  r.supportIso ≪≫ Functor.isoWhiskerLeft _ (supportModel l E D hl f c r)

/-- All realization data used by the assertion, supplied as a conclusion.
The systems have their recorded finite exceptional quotient maps and counit squares.
The integral adjunctions have the fixed compact-support LEFT functors.
Source: simultaneous adjunctions and completed scalar realization in the node
(blueprint: def-coef-finite-scalar-mate-data). -/
structure Context where
  SX : CoefficientDerivedSystemCalculus l E X
  SZ : CoefficientDerivedSystemCalculus l E c.Z
  SY : CoefficientDerivedSystemCalculus l E Y
  UX : CoefficientDerivedSystemCalculus l L X
  UZ : CoefficientDerivedSystemCalculus l L c.Z
  UY : CoefficientDerivedSystemCalculus l L Y
  r : FiniteAdjunctionDiagram.Realization l E D hl f c SX SZ SY
  s : FiniteAdjunctionDiagram.Realization l L D hl f c UX UZ UY
  supportR : FiniteAdjunctionDiagram.IntegralSupport r
  supportS : FiniteAdjunctionDiagram.IntegralSupport s
  reductionY : ∀ M : sfIntegralConstructibleCategory l E Y,
    FiniteAdjunctionDiagram.domain l E Y (SY.reduction.obj M.obj)
  reductionSY : ∀ M : sfIntegralConstructibleCategory l L Y,
    FiniteAdjunctionDiagram.domain l L Y (UY.reduction.obj M.obj)
  scalarX : ∀ N : (FiniteAdjunctionDiagram.domain l E X).FullSubcategory,
    FiniteAdjunctionDiagram.domain l L X
      ((integralComparisonDerivedSequenceScalar l E L i X).obj N.obj)
  scalarY : ∀ N : (FiniteAdjunctionDiagram.domain l E Y).FullSubcategory,
    FiniteAdjunctionDiagram.domain l L Y
      ((integralComparisonDerivedSequenceScalar l E L i Y).obj N.obj)
  integralX : ∀ K : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l L X ((integralScalarExtensionOfUniverses l E L i X).obj K.obj)
  integralY : ∀ K : sfIntegralConstructibleCategory l E Y,
    sfIntegralConstructible l L Y ((integralScalarExtensionOfUniverses l E L i Y).obj K.obj)
  GR : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X
  GS : sfIntegralConstructibleCategory l L Y ⥤ sfIntegralConstructibleCategory l L X
  adjR : sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) c E ⊣ GR
  adjS : sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl) c L ⊣ GS
  scalarModelX : IntegralComparisonScalarModel l E L i X SX ((FrobeniusExchange.models l L).roos X)
  scalarModelY : IntegralComparisonScalarModel l E L i Y SY ((FrobeniusExchange.models l L).roos Y)

variable {l E L i D hl f c}

/-- Whole-system scalar extension restricted to normalized finite-Tor systems on X.
Source: the coherent scalar functor in the node
(blueprint: def-coef-finite-scalar-mate-data). -/
def Context.TX (a : Context l E L i D hl f c) :=
  (FiniteAdjunctionDiagram.domain l L X).lift
    ((FiniteAdjunctionDiagram.domain l E X).ι ⋙
      integralComparisonDerivedSequenceScalar l E L i X) a.scalarX

/-- Whole-system scalar extension on Y, before finite evaluation.
Source: the coherent scalar functor in the node
(blueprint: def-coef-finite-scalar-mate-data). -/
def Context.TY (a : Context l E L i D hl f c) :=
  (FiniteAdjunctionDiagram.domain l L Y).lift
    ((FiniteAdjunctionDiagram.domain l E Y).ι ⋙
      integralComparisonDerivedSequenceScalar l E L i Y) a.scalarY

/-- The prescribed strict-Roos completed scalar functor on X.
Source: T_X in the node (blueprint: def-coef-finite-scalar-mate-data). -/
def Context.TIX (a : Context l E L i D hl f c) :=
  (sfIntegralConstructible l L X).lift
    ((sfIntegralConstructible l E X).ι ⋙ integralScalarExtensionOfUniverses l E L i X) a.integralX

/-- The prescribed strict-Roos completed scalar functor on Y.
Source: T_Y in the node (blueprint: def-coef-finite-scalar-mate-data). -/
def Context.TIY (a : Context l E L i D hl f c) :=
  (sfIntegralConstructible l L Y).lift
    ((sfIntegralConstructible l E Y).ι ⋙ integralScalarExtensionOfUniverses l E L i Y) a.integralY

/-- Coherent reduction on X with its actual quotient transitions.
Source: M_n and simultaneous reduction in the node
(blueprint: def-coef-finite-scalar-mate-data). -/
def Context.RX (a : Context l E L i D hl f c) :=
  FiniteAdjunctionDiagram.reducedConstructible X a.SX a.supportR.reductionPreserves

/-- Coherent reduction on Y with its actual quotient transitions.
Source: M_n in the node (blueprint: def-coef-finite-scalar-mate-data). -/
def Context.RY (a : Context l E L i D hl f c) :=
  FiniteAdjunctionDiagram.reducedConstructible Y a.SY a.reductionY

/-- Coherent upper reduction on X, including all retained levels.
Source: simultaneous realization in the node
(blueprint: def-coef-finite-scalar-mate-data). -/
def Context.SXred (a : Context l E L i D hl f c) :=
  FiniteAdjunctionDiagram.reducedConstructible X a.UX a.supportS.reductionPreserves

/-- Coherent upper reduction on Y, including all retained levels.
Source: simultaneous realization in the node
(blueprint: def-coef-finite-scalar-mate-data). -/
def Context.SYred (a : Context l E L i D hl f c) :=
  FiniteAdjunctionDiagram.reducedConstructible Y a.UY a.reductionSY

/-- The proper scalar projection followed by the open tensor identification, on systems.
The full-subcategory preimage changes no component or morphism.
Source: alpha before evaluation in the node
(blueprint: def-coef-finite-scalar-mate-data). -/
def Context.alpha (a : Context l E L i D hl f c) : a.r.F ⋙ a.TY ⟶ a.TX ⋙ a.s.F :=
  ((Functor.whiskeringRight _ _ _).obj (FiniteAdjunctionDiagram.domain l L Y).ι).preimage
    (Functor.whiskerRight (supportPresentation l E D hl f c a.r).hom
        (integralComparisonDerivedSequenceScalar l E L i Y) ≫
      Functor.whiskerLeft (FiniteAdjunctionDiagram.domain l E X).ι
        (FrobeniusExchange.systemCompactScalar l E L i c) ≫
      Functor.whiskerLeft a.TX (supportPresentation l L D hl f c a.s).inv)

/-- The actual coherent transpose, formed before taking ANY evaluation or limit.
Source: b^sys in the node (blueprint: def-coef-finite-scalar-mate-data). -/
def Context.beta (a : Context l E L i D hl f c) (h : IsIso a.alpha) :
    a.r.G ⋙ a.TX ⟶ a.TY ⋙ a.s.G :=
  letI := h
  (mateEquiv a.r.adjunction a.s.adjunction
    (TwoSquare.mk _ _ _ _ (inv a.alpha))).natTrans


/-- Integral support comparison with the actual two completion conjugations.
Source: alpha in the node (blueprint: def-coef-finite-scalar-mate-data). -/
def Context.integralAlphaComponent (a : Context l E L i D hl f c)
    (K : sfIntegralConstructibleCategory l E X) :
    (a.TIY.obj ((sfCompactSupportFiniteIntegralFunctor l D.k
      (finiteFieldDatumPrimeUnit D l hl) c E).obj K)).obj ⟶
    ((sfCompactSupportFiniteIntegralFunctor l D.k
      (finiteFieldDatumPrimeUnit D l hl) c L).obj (a.TIX.obj K)).obj :=
  (IntegralFiniteExtension.completion l E L i Y _
    ((sfCompactSupportFiniteIntegralFunctor l D.k
      (finiteFieldDatumPrimeUnit D l hl) c E).obj K).property.1).inv ≫
  (pbcDerivedExtend (completedCoefficientMap l E L i Y)).map
    ((sfQcqsCompactSupportRealization l E D.k
      (finiteFieldDatumPrimeUnit D l hl) c).inv.app K) ≫
  (PurCompactSupport.comparison (PurCompactSupport.completedChange l E L i) c).app K.obj ≫
  (PurCompactSupport.image (PurCompactSupport.completed l L) c).map
    (IntegralFiniteExtension.completion l E L i X K.obj K.property.1).hom ≫
    (sfQcqsCompactSupportRealization l L D.k (finiteFieldDatumPrimeUnit D l hl) c).hom.app
      (a.TIX.obj K)

variable (l E L i D hl f c) in
/-- The finite-free proper/open map, independent of the chosen integral basis.
Source: alpha_n in the node (blueprint: def-coef-finite-scalar-mate-data). -/
def finiteAlpha (e : ℕ) (he : PurCompactSupport.Ramification l E L i e) (hp : 1 ≤ e)
    (n : ℕ) (K : (FiniteExceptional.domain l E X n).FullSubcategory) :
    (finiteTensor l E L i e he hp Y n).obj
      ((FiniteExceptional.F l E D hl f c n).obj K).obj ⟶
    (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l L
      (retainedIndex e n + 1))).obj ((finiteTensor l E L i e he hp X n).obj K.obj) :=
  (finiteTensor l E L i e he hp Y n).map
      ((PurCompactSupport.finiteImageIso l E n c).inv.app K.obj) ≫
    (PurCompactSupport.comparison (finiteChange l E L i e he hp n) c).app K.obj ≫
    (PurCompactSupport.finiteImageIso l L (retainedIndex e n) c).hom.app
      ((finiteTensor l E L i e he hp X n).obj K.obj)

variable (l E L i) in
/-- Retained finite tensor on the actual full finite-Tor subcategories.
Source: T_{W,n} in the node (blueprint: def-coef-finite-scalar-mate-data). -/
def finiteTensorRestricted (e : ℕ) (he : PurCompactSupport.Ramification l E L i e)
    (hp : 1 ≤ e) (W : Scheme.{u}) (n : ℕ)
    (h : ∀ K : (FiniteExceptional.domain l E W n).FullSubcategory,
      FiniteExceptional.domain l L W (retainedIndex e n)
        ((finiteTensor l E L i e he hp W n).obj K.obj)) :
    (FiniteExceptional.domain l E W n).FullSubcategory ⥤
      (FiniteExceptional.domain l L W (retainedIndex e n)).FullSubcategory :=
  (FiniteExceptional.domain l L W (retainedIndex e n)).lift
    ((FiniteExceptional.domain l E W n).ι ⋙ finiteTensor l E L i e he hp W n) h

end WeilConjectures.FiniteScalarMate
