/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarFiniteEvaluationTransport
public import WeilConjectures.SmoothPurity.PurStrictScalar.NativeOpenFiniteEvaluationLegacy
public import WeilConjectures.SmoothPurity.PurStrictScalar.NativeProperFiniteEvaluation

/-! # Proper image part of geometric scalar finite evaluation

Source: Stacks 07A6, 0D6E and 0940.
(blueprint: lem-pur-native-support-finite-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem finiteImageRestriction_factor
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ)
    (N : DerivedCategory (ProEtale.StrictTower.Modules
      (compactSupportSystemLevel l E n) X)) :
    (positiveImageRestriction l E c (n + 1) (Nat.le_add_left 1 n)).hom.app N =
      (moduleDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
        c.g).rightDerivedFunctor.map ((finiteOpenRestriction l E c.i n).hom.app N) ≫
      (finiteProperRestriction l E c.g n).hom.app
        ((PurCompactSupport.openExtension
          (PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n))
          c.i).mapDerivedCategory.obj N) := by
  simp only [positiveImageRestriction, finiteOpenRestriction, finiteProperRestriction,
    PurCompactSupport.restriction, PurCompactSupport.image, Functor.comp_map,
    moduleDirectImage, proEtaleRingDerivedDirectImage, constants,
    Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Category.comp_id]

private theorem nativeFiniteImage_factor
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ)
    (N : coefficientSequenceDerived.{u, u} l E X) :
    (compactSupportSystemEvaluation l E c n).hom.app N ≫
        (PurCompactSupport.finiteImageIso l E n c).inv.app
          ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj N) =
      (nativeFiniteProper l E c.g n).hom.app
          ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) c.i).obj N) ≫
        (proEtaleRingDerivedDirectImage c.g
          ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring Y)
          ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring c.Z)
          ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).pull c.g)).map
            ((nativeFiniteOpen l E c.i n).hom.app N) := by
  simp only [compactSupportSystemEvaluation, nativeFiniteProper, nativeFiniteOpen,
    PurCompactSupport.finiteImageIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Category.assoc, Category.id_comp, Category.comp_id]
  have := proEtaleConstantModuleDirectImage_additive c.g
    (Padic.coefficientExtensionRing l E (n + 1))
  have := sfIntrinsicExtensionByZero_additive c.i
    (Padic.coefficientExtensionRing l E (n + 1))
  have := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  have := (sfIntrinsicExtensionByZero_exact c.i
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  have h := (Functor.rightDerivedFunctorNatIso
    (eqToIso (PurCompactSupport.finiteDirectImage_eq l E n c.g))).inv.naturality
      (((ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.i n).hom.app N) ≫
        (Functor.mapDerivedCategoryNatIso (compactSupportOpenModel c.i
          (Padic.coefficientExtensionRing l E (n + 1)))).hom.app
            ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj N))
  simp only [Functor.map_comp, Category.assoc] at h
  erw [reassoc_of% h]
  rfl

private theorem nativeImage_paste
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ)
    (N : coefficientSequenceDerived.{u, u} l E X) :
    (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y n).map
        ((systemProper l E c.g).hom.app
          ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) c.i).obj N)) ≫
      (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y n).map
        ((R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.g).map
          ((systemOpen l E c.i).inv.app N)) ≫
      (constantImageEvaluation l E c n).hom.app ((systemU l E X).obj N) ≫
      (PurCompactSupport.image (constants l E) c).map
        ((evaluationRestriction l E X n).hom.app N) ≫
      (positiveImageRestriction l E c (n + 1) (Nat.le_add_left 1 n)).hom.app
        ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj N) =
    (evaluationRestriction l E Y n).hom.app
        ((ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.g).obj
            ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
              (compactSupportSystemQuotient l E) c.i).obj N)) ≫
      (finiteRestriction l E Y n).map
        ((nativeFiniteProper l E c.g n).hom.app
          ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) c.i).obj N)) ≫
      (finiteRestriction l E Y n).map
        ((proEtaleRingDerivedDirectImage c.g
          ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring Y)
          ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring c.Z)
          ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).pull c.g)).map
            ((nativeFiniteOpen l E c.i n).hom.app N)) := by
  have hp := nativeProper_finiteEvaluation l E c.g n
    ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.i).obj N)
  have ho := nativeOpen_finiteEvaluation_legacy l E c.i n N
  have hn := (evalR (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
    c.g n).naturality ((systemOpen l E c.i).inv.app N)
  have ht := (finiteProperRestriction l E c.g n).hom.naturality
    ((nativeFiniteOpen l E c.i n).hom.app N)
  rw [finiteImageRestriction_factor]
  simp only [constantImageEvaluation, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Category.assoc]
  have hmap := congrArg
    (fun t ↦ (moduleDirectImage
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
      c.g).rightDerivedFunctor.map t) ho
  simp only [Functor.comp_map, Functor.comp_obj, Functor.map_comp] at hn ht hmap
  erw [reassoc_of% hn, reassoc_of% hmap, ht, reassoc_of% hp]
  rfl

/-- Evaluation of the native support model is compatible with its restriction to
constant coefficients, input reduction and finite image restriction.
Source: Stacks 07A6, 0D6E and 0940; evaluation/scalar-restriction normalization.
(blueprint: lem-pur-native-support-finite-evaluation).
Proof: expand supportModel into its proper and open comparisons. Transpose the
proper square under the finite geometric adjunction. The normalized whole-system
counit and identity-on-sections restriction comparison give equal transposes,
so injectivity of the adjunction bijection proves that square. For the open
square, both comparisons localize the identity on the open and the zero map off
it. Paste these squares, then use naturality of the input reductionEvaluation.
The finiteReductionIso and finiteImageIso factors agree with those used in
supportEvaluation. This proves the equality for every derived input without
asserting faithfulness of evaluation. -/
theorem nativeSupport_finiteEvaluation
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y n).map
        ((supportModel l E c S).hom.app M) ≫
      (constantImageEvaluation l E c n).hom.app ((reduction l E X S).obj M) ≫
      (PurCompactSupport.image (constants l E) c).map
        ((reductionEvaluation l E X S n).hom.app M) ≫
      (positiveImageRestriction l E c (n + 1) (Nat.le_add_left 1 n)).hom.app
        ((pbcDerivedExtend (PurCompactSupport.projection l E (n + 1)
          (Nat.le_add_left 1 n) X)).obj M) =
      (supportEvaluation l E c S n).hom.app M := by
  let N := S.reduction.obj M
  let U := finiteRestriction l E Y n
  let C := PurCompactSupport.image (constants l E) c
  let B := PurCompactSupport.image
    (PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)) c
  let r := (S.reductionEvaluation n).hom.app M ≫
    (PurCompactSupport.finiteReductionIso l E X n).inv.app M
  let a := (positiveImageRestriction l E c (n + 1) (Nat.le_add_left 1 n)).hom
  let v := (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y n).map
      ((supportModel l E c S).hom.app M) ≫
    (constantImageEvaluation l E c n).hom.app ((reduction l E X S).obj M) ≫
    C.map ((evaluationRestriction l E X n).hom.app N) ≫
    a.app ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj N)
  let w := (evaluationRestriction l E Y n).hom.app
      ((ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.g).obj
          ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
            (compactSupportSystemQuotient l E) c.i).obj N)) ≫
    U.map ((compactSupportSystemEvaluation l E c n).hom.app N ≫
      (PurCompactSupport.finiteImageIso l E n c).inv.app
        ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj N))
  have hvw : v = w := by
    dsimp only [v, w]
    rw [nativeFiniteImage_factor, U.map_comp]
    simpa only [N, U, C, a, reduction, Functor.comp_obj,
      supportModel, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Functor.map_comp, Category.assoc] using nativeImage_paste l E c n N
  have hr := a.naturality r
  have hf := congrArg U.map
    ((PurCompactSupport.finiteImageIso l E n c).inv.naturality r)
  simp only [r, U, Functor.comp_map, Functor.map_comp, Category.assoc] at hr hf
  have hleft :
      (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y n).map
          ((supportModel l E c S).hom.app M) ≫
        (constantImageEvaluation l E c n).hom.app ((reduction l E X S).obj M) ≫
        C.map ((reductionEvaluation l E X S n).hom.app M) ≫
        a.app ((pbcDerivedExtend (PurCompactSupport.projection l E (n + 1)
          (Nat.le_add_left 1 n) X)).obj M) = v ≫ U.map (B.map r) := by
    simp only [reductionEvaluation, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Functor.map_comp, Category.assoc, v]
    erw [hr]
    simp only [N, U, B, r, Functor.map_comp]
    rfl
  have hright : (supportEvaluation l E c S n).hom.app M = w ≫ U.map (B.map r) := by
    simp only [supportEvaluation, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Functor.comp_map, Functor.map_comp, Category.assoc, w, U, B, r]
    erw [hf]
    rfl
  exact hleft.trans ((congrArg (fun t ↦ t ≫ U.map (B.map r)) hvw).trans hright.symm)

end WeilConjectures.PurStrictScalar
