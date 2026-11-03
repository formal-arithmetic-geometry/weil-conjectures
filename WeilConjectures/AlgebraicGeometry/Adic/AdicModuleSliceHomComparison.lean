/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleSectionComparison
import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleSectionAssembly
import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleSliceCompatibility
import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientLocalization

/-!
# Native adic modules and sectionwise slice Hom

Source: Stacks Project, Modules on Sites, Tags 03EO and 0E8H; the native constructions in
`WeilConjectures.SixFunctors.ProEtale.Adic.Module`, `Hom`, `InternalHom` and
`InternalHomEvaluation` (blueprint: lem-sf-adic-module-slice-hom-comparison).

The imported section record and the slice record below package the conclusions,
with all comparison maps normalized on sections.
They impose no freeness, constructibility, or rank assumption on a module.

## Main definitions

* `adicComparisonTmul`, `adicComparisonEval`: the canonical native maps on local sections.
* `AdicModuleSectionComparison`: the equivalence and its tensor, Hom and evaluation formulas.
* `adicComparisonRestriction`, `adicComparisonPullSection`, `adicComparisonDualSlice`:
  the existing canonical restriction maps in the forms used by the comparison.
* `AdicModuleSliceHomComparison`: all comparison conclusions, including slice compatibility.

## Main statements

* `adicModuleSliceHomComparison`: existence of the normalized comparisons for every scheme.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale

/-- The complete native/slice comparison, including its normalization under the actual native
pullback and compatibility on every further slice. All fields are conclusions, not hypotheses
on a scheme or on its modules.
Source: Stacks 03EO, 0E8H, 03EL, and native adic pullback and evaluation
(blueprint: lem-sf-adic-module-slice-hom-comparison). -/
structure AdicModuleSliceHomComparison (l : ℕ) [Fact l.Prime] where
  /-- The same construction at every base scheme. -/
  base : ∀ X : Scheme.{u}, AdicModuleSectionComparison l X
  /-- Coefficients on the localized site are the restriction of the base coefficients. -/
  coefficientSlice : ∀ (X : Scheme.{u}) (U : X.ProEt),
    (base U.left).ring ≅
      (localizationRestriction RingCat.{u + 1} U.hom U.prop).obj (base X).ring
  /-- The coefficient identification is the identity on each further object's functions. -/
  coefficientSlice_identity : ∀ (X : Scheme.{u}) (U : X.ProEt)
    (V : U.left.ProEtᵒᵖ) (r : (base U.left).ring.obj.obj V),
    HEq (((coefficientSlice X U).hom.hom.app V) r) r
  /-- The actual native coefficient pullback map is identity after localization. -/
  nativeCoefficient_identity : ∀ (X : Scheme.{u}) (U : X.ProEt)
    (V : U.left.ProEtᵒᵖ)
    (r : ((upperStar (WeilCoefficients.{u} l) U.hom).obj (adicConstantSheaf l X)).obj.obj V),
    (upperStarAdicConstantSheafHom l U.hom).hom.app V r =
      ((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) U.hom U.prop).hom.app
        (adicConstantSheaf l X)).hom.app V r
  /-- Native module pullback corresponds naturally to the literal restriction functor. -/
  sliceIso : ∀ (X : Scheme.{u}) (U : X.ProEt),
    adicUpperStar l U.hom ⋙ (base U.left).E.functor ≅
      (base X).E.functor ⋙ adicComparisonRestriction U (base X) (base U.left)
        (coefficientSlice X U)
  /-- Its underlying section map is the canonical inverse-image/localization comparison. -/
  slice_sections : ∀ (X : Scheme.{u}) (U : X.ProEt) (M : AdicSheaf l X)
    (V : U.left.ProEtᵒᵖ) (x : ((adicUpperStar l U.hom).obj M).X.obj.obj V),
    ((sliceIso X U).hom.app M).val.app V ((base U.left).sectionsEquiv _ V x) =
      (base X).sectionsEquiv M
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
        (adicComparisonPullSection U M V x)
  /-- The native balanced tensor comparison along pullback. -/
  nativeTensorSlice : ∀ (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X),
    (Mod.tensorLeft ((adicUpperStar l U.hom).obj N)).obj ((adicUpperStar l U.hom).obj M) ≅
      (adicUpperStar l U.hom).obj ((Mod.tensorLeft N).obj M)
  /-- This is the canonical coequalizer comparison, normalized before the quotient. -/
  nativeTensorSlice_quotient : ∀ (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X),
    Mod.tensorπ ((adicUpperStar l U.hom).obj M) ((adicUpperStar l U.hom).obj N) ≫
        (nativeTensorSlice X U M N).hom.hom =
      Functor.LaxMonoidal.μ (upperStar (WeilCoefficients.{u} l) U.hom) M.X N.X ≫
        (upperStar (WeilCoefficients.{u} l) U.hom).map (Mod.tensorπ M N)
  /-- The sectionwise balanced tensor comparison along restriction. -/
  tensorSlice : ∀ (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X),
    (adicComparisonRestriction U (base X) (base U.left) (coefficientSlice X U)).obj
        ((SheafOfModules.siteSheafTensorRight (A := (base X).R)
          ((base X).E.functor.obj N)).obj ((base X).E.functor.obj M)) ≅
      (SheafOfModules.siteSheafTensorRight (A := (base U.left).R)
        ((adicComparisonRestriction U (base X) (base U.left) (coefficientSlice X U)).obj
          ((base X).E.functor.obj N))).obj
        ((adicComparisonRestriction U (base X) (base U.left) (coefficientSlice X U)).obj
          ((base X).E.functor.obj M))
  /-- The restriction comparison preserves the canonical local pure tensors. -/
  tensorSlice_sections : ∀ (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X)
    (V : U.left.ProEtᵒᵖ)
    (x : ((base X).E.functor.obj M).val.obj
      (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)))
    (y : ((base X).E.functor.obj N).val.obj
      (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))),
    (tensorSlice X U M N).hom.val.app V
      (SheafOfModules.siteSheafTensorTmul (A := (base X).R)
        ((base X).E.functor.obj M) ((base X).E.functor.obj N)
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)) x y) =
      SheafOfModules.siteSheafTensorTmul (A := (base U.left).R)
        ((adicComparisonRestriction U (base X) (base U.left) (coefficientSlice X U)).obj
          ((base X).E.functor.obj M))
        ((adicComparisonRestriction U (base X) (base U.left) (coefficientSlice X U)).obj
          ((base X).E.functor.obj N)) V x y
  /-- The native/sectionwise tensor comparisons commute with restriction. -/
  tensor_slice : ∀ (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X),
    (base U.left).E.functor.map (nativeTensorSlice X U M N).hom ≫
        (sliceIso X U).hom.app ((Mod.tensorLeft N).obj M) ≫
        (adicComparisonRestriction U (base X) (base U.left) (coefficientSlice X U)).map
          (((base X).tensorIso N).hom.app M) ≫ (tensorSlice X U M N).hom =
      ((base U.left).tensorIso ((adicUpperStar l U.hom).obj N)).hom.app
          ((adicUpperStar l U.hom).obj M) ≫
        (SheafOfModules.siteSheafTensorRight (A := (base U.left).R)
          ((base U.left).E.functor.obj ((adicUpperStar l U.hom).obj N))).map
          ((sliceIso X U).hom.app M) ≫
        SheafOfModules.siteSheafTensorSecondMap (A := (base U.left).R)
          ((adicComparisonRestriction U (base X) (base U.left) (coefficientSlice X U)).obj
            ((base X).E.functor.obj M)) ((sliceIso X U).hom.app N)

  /-- The Hom comparison commutes with restriction, tested on every further slice object.
  The native vertical map is the recorded `adicUpperStarIhomIso`, not an unspecified iso. -/
  hom_slice : ∀ (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X)
    (V : U.left.ProEtᵒᵖ)
    (z : ((adicUpperStar l U.hom).obj ((AdicSheaf.ihom M).obj N)).X.obj.obj V)
    (W : Over V.unop) (x : ((adicUpperStar l U.hom).obj M).X.obj.obj (op W.left)),
    ((sliceIso X U).hom.app N).val.app (op W.left)
      (((((base U.left).homIso ((adicUpperStar l U.hom).obj M)).hom.app
          ((adicUpperStar l U.hom).obj N)).val.app V
        ((base U.left).sectionsEquiv _ V
          (((adicUpperStarIhomIso l U.hom M).hom.app N).hom.hom.app V z))).app (op W)
            ((base U.left).sectionsEquiv _ (op W.left) x)) =
      ((((base X).homIso M).hom.app N).val.app
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
        ((base X).sectionsEquiv _
          (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
          (adicComparisonPullSection U ((AdicSheaf.ihom M).obj N) V z))).app
            (op (Over.mk ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).map W.hom)))
              ((base X).sectionsEquiv M
                (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj W.left))
                (adicComparisonPullSection U M (op W.left) x))
  /-- Native evaluation commutes with the specified restriction on underlying sections. -/
  evaluation_slice : ∀ (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X)
    (V : U.left.ProEtᵒᵖ)
    (z : ((adicUpperStar l U.hom).obj ((AdicSheaf.ihom M).obj N)).X.obj.obj V)
    (x : ((adicUpperStar l U.hom).obj M).X.obj.obj V),
    adicComparisonPullSection U N V
      (adicComparisonEval ((adicUpperStar l U.hom).obj M) ((adicUpperStar l U.hom).obj N) V
        (((adicUpperStarIhomIso l U.hom M).hom.app N).hom.hom.app V z) x) =
      adicComparisonEval M N
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
        (adicComparisonPullSection U ((AdicSheaf.ihom M).obj N) V z)
        (adicComparisonPullSection U M V x)
  /-- Bidual evaluation commutes with restriction through the actual native dual maps. -/
  bidual_slice : ∀ (X : Scheme.{u}) (U : X.ProEt) (M : AdicSheaf l X),
    (adicUpperStar l U.hom).map ((base X).bidual M) ≫
        adicComparisonDualSlice U ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)) =
      (base U.left).bidual ((adicUpperStar l U.hom).obj M) ≫
        (Mod.ihomMap (adicComparisonDualSlice U M)).app (AdicSheaf.unit l U.left)
  /-- All finite free trivializations, in both directions, correspond on each slice. -/
  trivializations : ∀ (X : Scheme.{u}) (U : X.ProEt) (M : AdicSheaf l X) (n : ℕ),
    (((adicUpperStar l U.hom).obj M) ≅
        ∐ (fun (_ : ULift.{u + 1} (Fin n)) ↦ AdicSheaf.unit l U.left)) ≃
      ((adicComparisonRestriction U (base X) (base U.left) (coefficientSlice X U)).obj
          ((base X).E.functor.obj M) ≅
        SheafOfModules.free (R := (base U.left).ring) (ULift.{u + 1} (Fin n)))
  /-- The correspondence is the actual functor on trivializations with its fixed coordinate
  and restriction comparisons, so the claim is about trivializations and their inverses. -/
  trivializations_hom : ∀ (X : Scheme.{u}) (U : X.ProEt) (M : AdicSheaf l X) (n : ℕ)
    (e : ((adicUpperStar l U.hom).obj M) ≅
      ∐ (fun (_ : ULift.{u + 1} (Fin n)) ↦ AdicSheaf.unit l U.left)),
    (trivializations X U M n e).hom =
      (sliceIso X U).inv.app M ≫ (base U.left).E.functor.map e.hom ≫
        ((base U.left).freeIso n).hom

attribute [local irreducible] adicSectionModuleEquivalence comparisonModuleFunctor
  comparisonRing adicUpperStarIhomIso

private def isoConjugation {C : Type*} [Category C] {A B C' D : C}
    (i : C' ≅ A) (j : B ≅ D) : (A ≅ B) ≃ (C' ≅ D) where
  toFun e := i ≪≫ e ≪≫ j
  invFun e := i.symm ≪≫ e ≪≫ j.symm
  left_inv e := by ext; simp
  right_inv e := by ext; simp

/-- Native adic modules and sectionwise module sheaves agree, preserving balanced tensor,
slice Hom, evaluation, bidual evaluation, site-object restriction, and finite free charts.
Source: Stacks Project, Modules on Sites, Tags 03EO and 0E8H, and the native adic module
construction (blueprint: lem-sf-adic-module-slice-hom-comparison).

Proof:
1. Use vector-space sheafification and its strong monoidality
   (`def-weil-pbc-sheafification`, `lem-weil-pbc-sheaf-tensor-closed`) to identify an internal
   action with natural sectionwise bilinear actions. Associativity and the unit are checked
   on threefold pure tensors and on `1`, respectively.
2. Restrict scalars along constant functions to recover the original vector-space structure.
   Internal module maps are exactly the sectionwise linear maps. These inverse assignments
   give the equivalence with `def-weil-sheaf-of-modules-category`, unchanged on all sections
   and maps. Multiplication gives the regular module comparison.
3. The native coequalizer represents balanced bilinear pairings. Module sheafification
   (`def-weil-presheaf-modules-sheafification`) and `def-pur-sheaf-tensor-product` represent
   the same pairings. The mutually inverse comparisons preserve pure tensors and are natural.
4. For the slice Hom (`def-pur-sheaf-hom`), curry a pairing by sending a section `g` on `V`
   to the map on `W/V` given by `m ↦ b(m,g|_W)`. Evaluation is the inverse construction.
   Thus evaluation is a counit, and counit-preserving uniqueness (`det-sp-unique-right-adjoint`)
   identifies this adjunction with native Hom. This proves both naturality and evaluation;
   transposing with the factors exchanged gives the bidual formula, without invertibility.
5. Identify the site over a site object with the slice using
   `lem-weil-proetale-weakly-etale-localization`. Both coefficient rings on a further object
   consist of exactly the same functions. The initial indexing object in
   `lem-sfb-proetale-object-inverse-image-restriction` makes the actual coefficient pullback
   the identity. The monoidal inverse image carries the action to the restricted action.
   Extension along the identity is inverted by `m ↦ 1 ⊗ m` and `r ⊗ m ↦ rm`.
6. Tensor comparisons commute with restriction by their identical pure tensors
   (`lem-sfb-localized-site-tensor-restriction`). On Hom both sides consist of the same maps
   on the further slice; their evaluation formulas agree. Counit-preserving uniqueness then
   gives the displayed Hom restriction equation and compatibility of evaluations and their
   bidual transposes, also under successive restrictions.
7. Coordinate inclusions and projections identify finite sums on both sides. Applying the
   equivalence and its inverse to a trivialization gives exactly the stated bijection,
   including the zero-rank case. No finiteness hypothesis on an arbitrary module is used. -/
theorem adicModuleSliceHomComparison (l : ℕ) [Fact l.Prime] :
    Nonempty (AdicModuleSliceHomComparison.{u} l) := by
  classical
  choose base hbase using fun X : Scheme.{u} ↦ adicModuleSectionComparison l X
  obtain ⟨q⟩ := adicModuleSliceCompatibility l base
  refine ⟨{
    base := base
    coefficientSlice := q.coefficientSlice
    coefficientSlice_identity := q.coefficientSlice_identity
    nativeCoefficient_identity := ?_
    sliceIso := q.sliceIso
    slice_sections := q.slice_sections
    nativeTensorSlice := q.nativeTensorSlice
    nativeTensorSlice_quotient := q.nativeTensorSlice_quotient
    tensorSlice := q.tensorSlice
    tensorSlice_sections := q.tensorSlice_sections
    tensor_slice := q.tensor_slice
    hom_slice := q.hom_slice
    evaluation_slice := q.evaluation_slice
    bidual_slice := q.bidual_slice
    trivializations := fun X U M n ↦
      (Functor.FullyFaithful.ofFullyFaithful (base U.left).E.functor).isoEquiv.trans
        (isoConjugation ((q.sliceIso X U).app M).symm ((base U.left).freeIso n))
    trivializations_hom := ?_ }⟩
  · intro X U V r
    have h := ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f ↦ f.hom)
        (comparisonNativeCoefficient (l := l) U.hom U.prop)) V) r
    exact h
  · intro X U M n e
    rfl

end AlgebraicGeometry.ProEtale
