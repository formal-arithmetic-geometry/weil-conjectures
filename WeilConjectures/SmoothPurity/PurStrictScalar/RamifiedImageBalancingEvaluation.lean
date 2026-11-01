/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarFiniteEvaluationTransport
import WeilConjectures.SmoothPurity.PurStrictScalar.RamifiedReductionFiniteEvaluation
import WeilConjectures.SmoothPurity.PurStrictScalar.NativeSupportFiniteEvaluationCompatibility
import WeilConjectures.SmoothPurity.PurStrictScalar.ConstantImageReindexEvaluation

/-! # Evaluation of ramified reduction balancing through geometric image

Source: Stacks 03EK, 06YY, 0D6E, 0E8I and 0940.
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
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

end WeilConjectures.PurStrictScalar

namespace WeilConjectures.PurStrictScalar

private theorem map_four_three
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {A₀ A₁ A₂ A₃ A₄ B₁ B₂ : C} {Z W : D}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄)
    (e : A₀ ⟶ B₁) (f : B₁ ⟶ B₂) (g : B₂ ⟶ A₄)
    (h : a ≫ b ≫ c ≫ d = e ≫ f ≫ g) (p : Z ⟶ G.obj A₀)
    (q : G.obj A₄ ⟶ W) :
    p ≫ G.map a ≫ G.map b ≫ G.map c ≫ G.map d ≫ q =
      p ≫ G.map e ≫ G.map f ≫ G.map g ≫ q := by
  have hh := congrArg (fun z ↦ p ≫ G.map z ≫ q) h
  simpa only [G.map_comp, Category.assoc] using hh

/-- Ramified reduction transport has the finite tensor normalization. This is an
equality between isomorphisms; it contains neither the proper/open scalar mate
nor finiteTensorMap. Source: Stacks 03EK, 06YY, 0940 (section-derived-limits),
0D6E, and sites-modules.tex 0E8I (lemma-j-shriek-and-tensor).
(blueprint: lem-pur-ramified-image-balancing-evaluation).
Proof: evaluate the universal whole-cochain counit equation characterizing
reductionBalancing on a K-flat diagram representative. Evaluation of its ordinary
balancing sends b tensor (1 tensor x) to the quotient of b tensor (1 tensor x)
at exponent e(n+1). The finiteOrdinaryBalancing pure-tensor equation gives the
same coefficient and section. The reductionEvaluation comparisons and the
completed coefficient tensorSquare identify the remaining scalar-extension
associators; their cochain equations are the successive derived-quotient
normalization. Universal derived counits therefore give equality of the two
local reduction isomorphisms, before applying geometric image. Apply the
constant-coefficient proper/open image to this equation. Its evaluation
comparisons are natural. The ordinary selection squares for direct image and
open extension are identity squares, and their derived comparisons are fixed
by the same derived units. Consequently constantImageEvaluation carries
reindexImage to evaluation at e(n+1)-1. Finally the identity-on-sections
restriction/proper square and the normalized open unit identify supportModel
followed by constantImageEvaluation with the native positiveSupportEvaluation
followed by positiveImageRestriction. Cancel the supportModel and reindexImage
inverse pairs. The factors left on the ramified side are targetEvaluation;
the other side is scalarImageEvaluation. Localization gives the equality on
all derived inputs. Positivity e(n+1)≥1 justifies the retained index even when
e=1 and n=0; the zero and empty-open cases use the same equations. -/
theorem ramifiedImageBalancing_finiteEvaluation
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Y n).map
        ((ramifiedImageBalancing l E F i c S S' e he hepos).hom.app M) ≫
        (targetEvaluation l E F i c S' e he hepos n).hom.app M =
      (scalarImageEvaluation l E F i c S e he hepos n).hom.app M := by
  let m := e * (n + 1)
  have hm : 1 ≤ m := Nat.mul_pos hepos (Nat.le_add_left 1 n)
  let A := pbcDerivedExtend (completedCoefficientMap l E F i X)
  let Q := pbcDerivedExtend (PurCompactSupport.projection l E (n + 1)
    (Nat.le_add_left 1 n) X)
  let B := pbcDerivedExtend ((PurCompactSupport.finiteChange l E F i e he hepos
    (n + 1) (Nat.le_add_left 1 n)).map X)
  let QF := pbcDerivedExtend (PurCompactSupport.projection l F m hm X)
  let V := ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Y n
  let Vk := ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Y (m - 1)
  let VX := ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) X n
  let P := PurCompactSupport.image (constants l F) c
  let Pf := PurCompactSupport.image (PurCompactSupport.finite l F m hm) c
  let U := positiveRestriction l F Y m hm
  let UX := positiveRestriction l F X m hm
  let N := (reduction l F X S').obj (A.obj M)
  let t := (PurCompactSupport.tensorSquare (completedCoefficientMap l E F i X)
    ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
      (Nat.le_add_left 1 n)).map X)
    (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) X)
    (PurCompactSupport.projection l F m hm X)
    (PurCompactSupport.ramified_reduction_square l E F i e he hepos (n + 1)
      (Nat.le_add_left 1 n) X)).hom.app M
  let r := (positiveReductionEvaluation l F X S' m hm).hom.app (A.obj M)
  let b := (reductionBalancing l E F i X S S' e he hepos).hom.app M
  have hmodel :
      Vk.map ((supportModel l F c S').inv.app (A.obj M)) ≫
        (positiveSupportEvaluation l F c S' m hm).hom.app (A.obj M) =
      (constantImageEvaluation l F c (m - 1)).hom.app N ≫
        P.map r ≫ (positiveImageRestriction l F c m hm).hom.app (QF.obj (A.obj M)) := by
    apply (cancel_epi (Vk.map ((supportModel l F c S').hom.app (A.obj M)))).mp
    rw [← Category.assoc, ← Vk.map_comp, Iso.hom_inv_id_app, Vk.map_id,
      Category.id_comp]
    exact (nativeSupport_positiveFiniteEvaluation l F c S' m hm (A.obj M)).symm
  have hsub := (subsequenceEvaluation l F Y e n).hom.naturality
    ((supportModel l F c S').inv.app (A.obj M))
  have hreindex := constantImage_reindexEvaluation l F c e hepos n N
  have hrho : P.map (UX.map t) ≫
      (positiveImageRestriction l F c m hm).hom.app (B.obj (Q.obj M)) =
      (positiveImageRestriction l F c m hm).hom.app (QF.obj (A.obj M)) ≫
        U.map (Pf.map t) :=
    (positiveImageRestriction l F c m hm).hom.naturality t
  have hlocal := ramifiedReduction_finiteEvaluation l E F i X S S' e he hepos M n
  have hnat : V.map ((image l F c).map b) ≫
      (constantImageEvaluation l F c n).hom.app ((subsequence l F X e).obj N) =
      (constantImageEvaluation l F c n).hom.app
        ((T l E F i X).obj ((reduction l E X S).obj M)) ≫ P.map (VX.map b) :=
    (constantImageEvaluation l F c n).hom.naturality b
  simp only [ramifiedImageBalancing, targetEvaluation, scalarImageEvaluation,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  change V.map ((image l F c).map b) ≫
    V.map ((reindexImage l F c e hepos).inv.app N) ≫
    V.map ((subsequence l F Y e).map ((supportModel l F c S').inv.app (A.obj M))) ≫
    (subsequenceEvaluation l F Y e n).hom.app ((support l F c S').obj (A.obj M)) ≫
    (positiveSupportEvaluation l F c S' m hm).hom.app (A.obj M) ≫ U.map (Pf.map t) =
    (constantImageEvaluation l F c n).hom.app ((T l E F i X).obj
      ((reduction l E X S).obj M)) ≫
    P.map ((tensorEvaluation l E F i X n).hom.app ((reduction l E X S).obj M)) ≫
    P.map ((baseTensor l E F i X).map ((reductionEvaluation l E X S n).hom.app M)) ≫
    P.map ((finiteBalancing l E F i X e he hepos n).hom.app (Q.obj M)) ≫
    (positiveImageRestriction l F c m hm).hom.app (B.obj (Q.obj M))
  rw [reassoc_of% hsub, reassoc_of% hmodel, reassoc_of% hreindex]
  rw [← hrho]
  rw [reassoc_of% hnat]
  exact map_four_three P _ _ _ _ _ _ _ hlocal _ _

end WeilConjectures.PurStrictScalar
