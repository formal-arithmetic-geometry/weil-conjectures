# SheafOfModules.strictPerfectRingedPullbackModel

## Reason

The stage-3 proof adds private, proved helpers with an explicitly scoped elaboration
context. Preflight classifies the added `open`, `set_option`, and `omit` commands as
an interface change requiring this record. All existing public theorem headers and
all five public definition bodies remain verbatim. No target or mathematical
statement changes; no definition is replaced or hidden.

The extra `open MonoidalCategory`, transparency option and instance-search bound
are inside `section DerivedHelpers`, which ends before the existing public
parameters and definitions. The two `omit ... in` commands apply only to new private
lemmas. Options using `... in` elsewhere apply to individual private helpers, except
for disabling the unused-section-variable warning on the finite-free uniqueness
theorem so its existing presentation parameters remain present. Existing local
sheaf-compose instance priorities remain identical. No new global instance,
attribute, public import, or notation is registered.

## Old

The existing public declaration was:

```lean
theorem strictPerfectRingedPullbackModel
    [LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (ringedSiteModules.{r}
        ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (ComplexShape.up ℤ))]
    (F : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (package : StrictPerfectCoefficientPackageOnSite _ F)
    (a b : ℤ) (hbounded : ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n)) :
    (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (F.X n)) ∧
    F.IsKFlatIndependentCoefficients ∧
    (∀ n : ℤ, n < a ∨ b < n →
      IsZero (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X n)) ∧
    (∀ n : ℤ, IsFlatOnSite (J := JD) (R := S)
      (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X n)) ∧
    CochainComplex.IsKFlatIndependentCoefficients
      ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F) ∧
    IsIso ((ringedPullbackComplexComparison uStar LF epsilon).app F) ∧
    (∀ (P : DerivedCategory (ringedSiteModules.{r}
        ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
      (e : DerivedCategory.Q.obj F ≅ P),
      IsIso (LF.map e.inv ≫ (ringedPullbackComplexComparison uStar LF epsilon).app F)) ∧
    (∀ (G : CochainComplex (ringedSiteModules.{r}
        ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
      (_ : StrictPerfectCoefficientPackageOnSite _ G) (a' b' : ℤ)
      (_ : ∀ n : ℤ, n < a' ∨ b' < n → IsZero (G.X n)) (v : F ⟶ G),
      (ringedPullbackComplexComparison uStar LF epsilon).app F ≫
          DerivedCategory.Q.map ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).map v) =
        LF.map (DerivedCategory.Q.map v) ≫
          (ringedPullbackComplexComparison uStar LF epsilon).app G) := sorry
```

There was no `DerivedHelpers` section or private tensor-section helper context.

## New

The same public declaration, with its proof filled, is:

```lean
theorem strictPerfectRingedPullbackModel
    [LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (ringedSiteModules.{r}
        ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (ComplexShape.up ℤ))]
    (F : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (package : StrictPerfectCoefficientPackageOnSite _ F)
    (a b : ℤ) (hbounded : ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n)) :
    (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (F.X n)) ∧
    F.IsKFlatIndependentCoefficients ∧
    (∀ n : ℤ, n < a ∨ b < n →
      IsZero (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X n)) ∧
    (∀ n : ℤ, IsFlatOnSite (J := JD) (R := S)
      (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X n)) ∧
    CochainComplex.IsKFlatIndependentCoefficients
      ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj F) ∧
    IsIso ((ringedPullbackComplexComparison uStar LF epsilon).app F) ∧
    (∀ (P : DerivedCategory (ringedSiteModules.{r}
        ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
      (e : DerivedCategory.Q.obj F ≅ P),
      IsIso (LF.map e.inv ≫ (ringedPullbackComplexComparison uStar LF epsilon).app F)) ∧
    (∀ (G : CochainComplex (ringedSiteModules.{r}
        ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
      (_ : StrictPerfectCoefficientPackageOnSite _ G) (a' b' : ℤ)
      (_ : ∀ n : ℤ, n < a' ∨ b' < n → IsZero (G.X n)) (v : F ⟶ G),
      (ringedPullbackComplexComparison uStar LF epsilon).app F ≫
          DerivedCategory.Q.map ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).map v) =
        LF.map (DerivedCategory.Q.map v) ≫
          (ringedPullbackComplexComparison uStar LF epsilon).app G) := by
  have hflat : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (F.X n) := fun n ↦
    flat_finiteFree_retract R (F.X n) (package.N n) (package.i n) (package.p n)
      (package.splitting n)
  have : F.IsStrictlyLE b :=
    (F.isStrictlyLE_iff b).2 (fun n hn ↦ hbounded n (Or.inr hn))
  have hk := isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R F b hflat
  have hpull := isKFlat_ringedToposPullback uInv uPush adj I c uStar hobj hmap F hk hflat
  have hcomp := pullback_comparison_iso uInv I c uStar hobj uPush adj hmap LF epsilon
    F hk hflat
  refine ⟨hflat, hk, ?_, hpull.2, hpull.1, hcomp, ?_, ?_⟩
  · intro n hn
    exact uStar.map_isZero (hbounded n hn)
  · intro P e
    infer_instance
  · intro G _ a' b' _ v
    exact ((ringedPullbackComplexComparison uStar LF epsilon).naturality v).symm
```

The new private-helper section starts with this exact context:

```lean
section DerivedHelpers
open MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
```

It ends with `end DerivedHelpers`. The other command additions are
`omit adj hlim hadd in` before private `tensorSection_naturality`, and
`omit adj hmap hlim hadd in` before private `tensorSection_hom_ext`.
The uniqueness theorem has the scoped command
`set_option linter.unusedSectionVars false in`.

## Users

`python3 tools/downstream.py Sheaf.Paper.StrictPerfectRingedPullbackModel` reports
zero downstream Lean modules. Repeating it with `--uses` for the six public
construction/predicate/main-theorem names finds only the item module itself.
The textual library search likewise finds no external Lean consumers. This item
remains required by its DAG parent; no withdrawal is proposed. No consumer needs
adaptation, and target meanings remain identical because definitions are identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.StrictPerfectRingedPullbackModel | Q3 | Three theorem proofs completed; private helper contexts added; public signatures and definitions preserved. |

The source module compiles without warnings in 18.8 seconds. A diagnostic copy with
the standard axiom probe compiles in 16.8 seconds and prints `SHEAF-PROBED 11`, with
no forbidden axiom or direct-sorry findings. Its only warning belongs to the
standard appended probe line, outside the delivered source.

## Status

landed 20261021T120448-L-3898536 2026-10-21 (merge of deliver/Q3/Sheaf.Paper.StrictPerfectRingedPullbackModel)
