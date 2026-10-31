/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleSectionComparison
public import WeilConjectures.AlgebraicGeometry.Adic.AdicNativeBidual
import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleTensorComparisonCore
import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleHomComparisonCore

/-! # Closed comparison for the explicit adic section equivalence -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

/-- Tensor and Hom comparisons for the already constructed section equivalence.
Source: Stacks 03EK, 03EO and 0E8H
(blueprint: lem-sf-adic-module-tensor-hom-comparison). -/
structure AdicModuleTensorHomComparison (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) where
  /-- The tensor comparison is natural in the first variable. -/
  tensorIso : ∀ M : AdicSheaf l X,
    Mod.tensorLeft M ⋙ (comparisonModuleFunctor l X) ≅
      (comparisonModuleFunctor l X) ⋙ SheafOfModules.siteSheafTensorRight
        (A := comparisonRing l X) ((comparisonModuleFunctor l X).obj M)
  /-- It is natural in the second variable too. -/
  tensor_naturality : ∀ {M M' N N' : AdicSheaf l X} (f : M ⟶ M') (g : N ⟶ N'),
    (comparisonModuleFunctor l X).map ((Mod.tensorLeft N).map f ≫ (Mod.tensorLeftMap g).app M') ≫
        (tensorIso N').hom.app M' =
      (tensorIso N).hom.app M ≫
        (SheafOfModules.siteSheafTensorRight (A := comparisonRing l X)
          ((comparisonModuleFunctor l X).obj N)).map ((comparisonModuleFunctor l X).map f) ≫
          SheafOfModules.siteSheafTensorSecondMap (A := comparisonRing l X)
            ((comparisonModuleFunctor l X).obj M') ((comparisonModuleFunctor l X).map g)
  /-- Tensor comparison sends each canonical pure tensor to the same pure tensor. -/
  tensor_sections : ∀ (M N : AdicSheaf l X) (V : X.ProEtᵒᵖ)
    (x : M.X.obj.obj V) (y : N.X.obj.obj V),
    ((tensorIso N).hom.app M).val.app V
        ((AddEquiv.refl _) (adicComparisonTmul M N V x y)) =
      SheafOfModules.siteSheafTensorTmul (A := comparisonRing l X)
        ((comparisonModuleFunctor l X).obj M) ((comparisonModuleFunctor l X).obj N) V
        ((AddEquiv.refl _) x) ((AddEquiv.refl _) y)
  /-- The Hom comparison is natural in the target. -/
  homIso : ∀ M : AdicSheaf l X,
    AdicSheaf.ihom M ⋙ (comparisonModuleFunctor l X) ≅
      (comparisonModuleFunctor l X) ⋙ (SheafOfModules.homFunctor (comparisonRing l X)).obj
        (op ((comparisonModuleFunctor l X).obj M))
  /-- It is contravariantly natural in the source. -/
  hom_naturality : ∀ {M M' N N' : AdicSheaf l X} (f : M' ⟶ M) (g : N ⟶ N'),
    (comparisonModuleFunctor l X).map ((Mod.ihomMap f).app N ≫ (AdicSheaf.ihom M').map g) ≫
        (homIso M').hom.app N' =
      (homIso M).hom.app N ≫ SheafOfModules.homObjMap (R := comparisonRing l X)
        ((comparisonModuleFunctor l X).map f) ((comparisonModuleFunctor l X).map g)
  /-- Native evaluation is the slice map `(x, λ) ↦ λ(x)`. -/
  evaluation : ∀ (M N : AdicSheaf l X) (V : X.ProEtᵒᵖ)
    (z : ((AdicSheaf.ihom M).obj N).X.obj.obj V) (x : M.X.obj.obj V),
    (AddEquiv.refl _) (adicComparisonEval M N V z x) =
      ((((homIso M).hom.app N).val.app V ((AddEquiv.refl _) z)).app
        (op (Over.mk (𝟙 V.unop)))) ((AddEquiv.refl _) x)
  /-- In slice coordinates the bidual sends `x` to `λ ↦ λ(x|_W)` on every further object. -/
  bidual_sections : ∀ (M : AdicSheaf l X) (V : X.ProEtᵒᵖ) (x : M.X.obj.obj V)
    (W : Over V.unop)
    (z : ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)).X.obj.obj (op W.left)),
    (((homIso ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X))).hom.app
        (AdicSheaf.unit l X)).val.app V
      ((AddEquiv.refl _) ((adicNativeBidual M).hom.hom.app V x))).app (op W)
        ((AddEquiv.refl _) z) =
      (AddEquiv.refl _)
        (adicComparisonEval M (AdicSheaf.unit l X) (op W.left) z (M.X.obj.map W.hom.op x))

/-- The explicit section equivalence preserves balanced tensor and slice Hom with
its counit and bidual normalization. Source: Stacks 03EK and 03EO
(blueprint: lem-sf-adic-module-tensor-hom-comparison).

Proof: a sectionwise R-bilinear pairing is K-bilinear after restricting scalars along
constant functions. Extend it uniquely across vector-space sheafification. Test the
two internal bilinearity diagrams on threefold pure tensors, then descend through
the native balanced coequalizer. In the opposite direction the native quotient
pairing is sectionwise R-bilinear and extends across module sheafification. Both
composites are identities by pure-tensor extensionality. Naturality is checked on
the same pure tensors. For Hom, send a native section z over V to the morphism on
each W/V given by x ↦ ev(z|_W,x). Conversely evaluate a slice-Hom section on the
identity object to obtain a natural bilinear pairing, extend it across sheafification
and curry it into native Hom. Uncurrying-currying identities and slice restriction
naturality prove the two composites are identities. The same evaluation formula
proves contravariant and covariant naturality. Transpose the identity of the dual
using braided evaluation to obtain bidual evaluation; naturality in W and the
transpose-pairing identity give the stated formula on every further slice. -/
theorem adicModuleTensorHomComparison (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    Nonempty (AdicModuleTensorHomComparison l X) := by
  obtain ⟨t⟩ := adicModuleTensorComparisonCore l X
  obtain ⟨h⟩ := adicModuleHomComparisonCore l X
  exact ⟨{
    tensorIso := t.tensorIso
    tensor_naturality := t.tensor_naturality
    tensor_sections := t.tensor_sections
    homIso := h.homIso
    hom_naturality := h.hom_naturality
    evaluation := h.evaluation
    bidual_sections := h.bidual_sections
  }⟩

end AlgebraicGeometry.ProEtale
