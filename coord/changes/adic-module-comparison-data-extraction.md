# AdicModuleSectionComparison and canonical section comparison maps

## Reason

Separate the unchanged public comparison data from its existence proof so the
fixed-functor closed comparison and restriction compatibility can be independent
results without cyclic imports. The original final theorem and full comparison
record retain their exact signatures. Construct the actual native/sectionwise
module equivalence, regular-module comparison and coordinate free comparisons.
No definition is weakened or replaced by proof-irrelevant or arbitrary data.

## Old

The following declarations were in
`Sheaf.SixFunctors.AdicModuleSliceHomComparison`:

```lean
noncomputable def adicComparisonTmul {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M N : AdicSheaf l X) (V : X.ProEtᵒᵖ)
    (x : M.X.obj.obj V) (y : N.X.obj.obj V) :
    ((Mod.tensorLeft N).obj M).X.obj.obj V :=
  (Mod.tensorπ M N).hom.app V
    ((Sheaf.tensorObjComparison (Scheme.ProEt.topology X) M.X N.X).app V
      (x ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] y))

/-- The native evaluation on a pair of local sections, using the canonical map into the
sheaf tensor. Source: Stacks 03EO and native `Mod.evaluation`
(blueprint: lem-sf-adic-module-slice-hom-comparison). -/
noncomputable def adicComparisonEval {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M N : AdicSheaf l X) (V : X.ProEtᵒᵖ)
    (z : ((AdicSheaf.ihom M).obj N).X.obj.obj V) (x : M.X.obj.obj V) : N.X.obj.obj V :=
  (Mod.evaluation M N).hom.app V
    ((Sheaf.tensorObjComparison (Scheme.ProEt.topology X)
      ((AdicSheaf.ihom M).obj N).X M.X).app V
      (z ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] x))

/-- The assertions of the native/sectionwise comparison at one base. The identity conditions
mean that sections and coefficient functions really are unchanged, rather than arbitrarily
identified. The Hom comparisons use the recorded slice Hom, not another right adjoint.
Source: Stacks 03EO, 0E8H and the native adic module presentation
(blueprint: lem-sf-adic-module-slice-hom-comparison). -/
structure AdicModuleSectionComparison (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) where
  /-- The commutative coefficient sheaf with its specified function sections. -/
  R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}
  /-- Its section rings are the native locally finite continuous functions. -/
  coefficient : ∀ V : X.ProEtᵒᵖ,
    R.obj.obj V ≃+* ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l V.unop.left)
  /-- This is the identity on functions, including the universe lift. -/
  coefficient_identity : ∀ (V : X.ProEtᵒᵖ) (r : R.obj.obj V), HEq (coefficient V r) r
  /-- Restriction is precomposition with the underlying map of schemes. -/
  coefficient_naturality : ∀ {V W : X.ProEtᵒᵖ} (f : V ⟶ W) (r : R.obj.obj V),
    coefficient W (R.obj.map f r) = WeilCoefficients.uliftAlgHom
      (PadicAlgCl.locallyFiniteFunctionsCompAlgHom l f.unop.left.base.hom) (coefficient V r)
  /-- The equivalence with the recorded category of sectionwise module sheaves. -/
  E : AdicSheaf l X ≌ ringedSiteModules.{u + 1}
    ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  /-- Underlying sections are unchanged, additively. -/
  sectionsEquiv : ∀ (M : AdicSheaf l X) (V : X.ProEtᵒᵖ),
    M.X.obj.obj V ≃+ (E.functor.obj M).val.obj V
  /-- The section identification is literally the identity on elements. -/
  section_identity : ∀ (M : AdicSheaf l X) (V : X.ProEtᵒᵖ) (x : M.X.obj.obj V),
    HEq (sectionsEquiv M V x) x
  /-- The unchanged section maps respect restriction. -/
  section_restriction : ∀ (M : AdicSheaf l X) {V W : X.ProEtᵒᵖ}
    (f : V ⟶ W) (x : M.X.obj.obj V),
    sectionsEquiv M W (M.X.obj.map f x) = (E.functor.obj M).val.map f (sectionsEquiv M V x)
  /-- Morphisms are unchanged on sections. -/
  section_map : ∀ {M N : AdicSheaf l X} (f : M ⟶ N) (V : X.ProEtᵒᵖ)
    (x : M.X.obj.obj V),
    sectionsEquiv N V (f.hom.hom.app V x) = (E.functor.map f).val.app V (sectionsEquiv M V x)
  /-- The internal action becomes exactly the sectionwise scalar action. -/
  action : ∀ (M : AdicSheaf l X) (V : X.ProEtᵒᵖ) (r : R.obj.obj V)
    (x : M.X.obj.obj V),
    sectionsEquiv M V ((Mod.act M.X).hom.app V
      ((Sheaf.tensorObjComparison (Scheme.ProEt.topology X) (adicConstantSheaf l X) M.X).app V
        (coefficient V r ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] x))) = r • sectionsEquiv M V x
  /-- The regular module is carried to the regular sectionwise module. -/
  unitIso : E.functor.obj (AdicSheaf.unit l X) ≅ SheafOfModules.unit
    ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  /-- The unit comparison is the identity on functions. -/
  unit_sections : ∀ (V : X.ProEtᵒᵖ) (r : (AdicSheaf.unit l X).X.obj.obj V),
    coefficient V (unitIso.hom.val.app V (sectionsEquiv _ V r)) = r
  /-- The tensor comparison is natural in the first variable. -/
  tensorIso : ∀ M : AdicSheaf l X,
    Mod.tensorLeft M ⋙ E.functor ≅
      E.functor ⋙ SheafOfModules.siteSheafTensorRight (A := R) (E.functor.obj M)
  /-- It is natural in the second variable too. -/
  tensor_naturality : ∀ {M M' N N' : AdicSheaf l X} (f : M ⟶ M') (g : N ⟶ N'),
    E.functor.map ((Mod.tensorLeft N).map f ≫ (Mod.tensorLeftMap g).app M') ≫
        (tensorIso N').hom.app M' =
      (tensorIso N).hom.app M ≫
        (SheafOfModules.siteSheafTensorRight (A := R) (E.functor.obj N)).map (E.functor.map f) ≫
          SheafOfModules.siteSheafTensorSecondMap (A := R) (E.functor.obj M') (E.functor.map g)
  /-- Tensor comparison sends each canonical pure tensor to the same pure tensor. -/
  tensor_sections : ∀ (M N : AdicSheaf l X) (V : X.ProEtᵒᵖ)
    (x : M.X.obj.obj V) (y : N.X.obj.obj V),
    ((tensorIso N).hom.app M).val.app V
        (sectionsEquiv _ V (adicComparisonTmul M N V x y)) =
      SheafOfModules.siteSheafTensorTmul (A := R) (E.functor.obj M) (E.functor.obj N) V
        (sectionsEquiv M V x) (sectionsEquiv N V y)
  /-- The Hom comparison is natural in the target. -/
  homIso : ∀ M : AdicSheaf l X,
    AdicSheaf.ihom M ⋙ E.functor ≅
      E.functor ⋙ (SheafOfModules.homFunctor R).obj (op (E.functor.obj M))
  /-- It is contravariantly natural in the source. -/
  hom_naturality : ∀ {M M' N N' : AdicSheaf l X} (f : M' ⟶ M) (g : N ⟶ N'),
    E.functor.map ((Mod.ihomMap f).app N ≫ (AdicSheaf.ihom M').map g) ≫
        (homIso M').hom.app N' =
      (homIso M).hom.app N ≫ SheafOfModules.homObjMap (R := R) (E.functor.map f) (E.functor.map g)
  /-- Native evaluation is the slice map `(x, λ) ↦ λ(x)`. -/
  evaluation : ∀ (M N : AdicSheaf l X) (V : X.ProEtᵒᵖ)
    (z : ((AdicSheaf.ihom M).obj N).X.obj.obj V) (x : M.X.obj.obj V),
    sectionsEquiv N V (adicComparisonEval M N V z x) =
      ((((homIso M).hom.app N).val.app V (sectionsEquiv _ V z)).app
        (op (Over.mk (𝟙 V.unop)))) (sectionsEquiv M V x)
  /-- The native bidual evaluation map, with no invertibility assertion. -/
  bidual : ∀ M : AdicSheaf l X,
    M ⟶ (AdicSheaf.ihom ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X))).obj
      (AdicSheaf.unit l X)
  /-- It is the transpose of evaluation with the two factors exchanged. -/
  bidual_transpose : ∀ M : AdicSheaf l X,
    (bidual M).hom ▷ ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)).X ≫
        Mod.evaluation ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)) (AdicSheaf.unit l X) =
      (β_ M.X ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)).X).hom ≫
        Mod.evaluation M (AdicSheaf.unit l X)
  /-- In slice coordinates the bidual sends `x` to `λ ↦ λ(x|_W)` on every further object. -/
  bidual_sections : ∀ (M : AdicSheaf l X) (V : X.ProEtᵒᵖ) (x : M.X.obj.obj V)
    (W : Over V.unop)
    (z : ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)).X.obj.obj (op W.left)),
    (((homIso ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X))).hom.app
        (AdicSheaf.unit l X)).val.app V
      (sectionsEquiv _ V ((bidual M).hom.hom.app V x))).app (op W)
        (sectionsEquiv _ (op W.left) z) =
      sectionsEquiv (AdicSheaf.unit l X) (op W.left)
        (adicComparisonEval M (AdicSheaf.unit l X) (op W.left) z (M.X.obj.map W.hom.op x))

  /-- Finite free modules are identified with the same coordinate sums, also in rank zero. -/
  freeIso : ∀ n : ℕ,
    E.functor.obj (∐ (fun (_ : ULift.{u + 1} (Fin n)) ↦ AdicSheaf.unit l X)) ≅
      SheafOfModules.free (R := (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (ULift.{u + 1} (Fin n))
  /-- The free comparison preserves each coordinate inclusion. -/
  free_coordinates : ∀ (n : ℕ) (i : ULift.{u + 1} (Fin n)),
    E.functor.map (Sigma.ι (fun (_ : ULift.{u + 1} (Fin n)) ↦ AdicSheaf.unit l X) i) ≫
        (freeIso n).hom = unitIso.hom ≫ SheafOfModules.ιFree i

namespace AdicModuleSectionComparison

/-- The underlying ring sheaf in a comparison, by the standard forgetful functor.
Source: Stacks 03CV (blueprint: lem-sf-adic-module-slice-hom-comparison). -/
abbrev ring {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (P : AdicModuleSectionComparison l X) : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj P.R

end AdicModuleSectionComparison

/-- Literal sectionwise restriction along a site object, with the coefficient map specified
by a ring-sheaf isomorphism. This is Mathlib's module pushforward along the composition
functor of sites, not a new inverse-image construction.
Source: Stacks 03DH, 0E8H (blueprint: lem-sf-adic-module-slice-hom-comparison). -/
noncomputable abbrev adicComparisonRestriction {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (U : X.ProEt) (P : AdicModuleSectionComparison l X)
    (Q : AdicModuleSectionComparison l U.left)
    (c : Q.ring ≅ (localizationRestriction RingCat.{u + 1} U.hom U.prop).obj P.ring) :
    ringedSiteModules.{u + 1} P.ring ⥤ ringedSiteModules.{u + 1} Q.ring :=
  letI : (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).IsContinuous
      (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap (V := U.left) (U := X) U.prop
  SheafOfModules.pushforward.{u + 1}
    (F := MorphismProperty.Over.map (f := U.hom) ⊤ U.prop)
    (J := Scheme.ProEt.topology U.left) (K := Scheme.ProEt.topology X)
    (S := Q.ring) (R := P.ring) c.hom

/-- The actual inverse-image/localization comparison on one section of a native module.
Source: Stacks 03CE and native `upperStarIsoLocalizationRestriction`
(blueprint: lem-sf-adic-module-slice-hom-comparison). -/
noncomputable def adicComparisonPullSection {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (U : X.ProEt) (M : AdicSheaf l X) (V : U.left.ProEtᵒᵖ)
    (x : ((adicUpperStar l U.hom).obj M).X.obj.obj V) :
    M.X.obj.obj (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)) :=
  ((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) U.hom U.prop).hom.app
    M.X).hom.app V x

/-- The specified native dual comparison on a site object: pull back the internal Hom,
then use the canonical pullback of the regular module. Source: native adic Hom and unit
pullback, Stacks 0E8H (blueprint: lem-sf-adic-module-slice-hom-comparison). -/
noncomputable def adicComparisonDualSlice {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (U : X.ProEt) (M : AdicSheaf l X) :
    (adicUpperStar l U.hom).obj ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)) ⟶
      (AdicSheaf.ihom ((adicUpperStar l U.hom).obj M)).obj (AdicSheaf.unit l U.left) :=
  (adicUpperStarIhomIso l U.hom M).hom.app (AdicSheaf.unit l X) ≫
    (AdicSheaf.ihom ((adicUpperStar l U.hom).obj M)).map (adicUpperStarUnitIso l U.hom).hom

```

## New

The declarations above are verbatim in
`Sheaf.SixFunctors.AdicModuleSectionComparison`, which the original module publicly
imports. Only docstring blueprint pointers and the containing module changed.
The explicit equivalence construction is new, in
`Sheaf.SixFunctors.AdicSectionModuleEquivalence`; every definition there is a real
construction with fully proved laws. The remaining closed and restriction results
are named theorems, each in its own module and DAG node.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.AdicModuleSliceHomComparison | E2 | Publicly imports unchanged data; proves final assembly from the two comparisons, and constructs the trivialization bijection. |

`tools/downstream.py Sheaf.SixFunctors.AdicModuleSliceHomComparison --uses
AdicModuleSectionComparison` reports no downstream modules and only the item's
own uses. No other module or target signature changes. The unit route is retained.

## Status

landed 20261024T224912-L-1826302 2026-10-24 (merge of deliver/E2/Sheaf.SixFunctors.AdicModuleSliceHomComparison)
