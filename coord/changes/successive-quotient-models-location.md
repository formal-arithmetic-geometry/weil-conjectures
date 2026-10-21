# SheafOfModules.successiveQuotientTensorModel, successiveQuotientTensorSection, successiveQuotientRestrictedModel

## Reason

Move these three typed model definitions verbatim from the triangle module into
SuccessiveQuotientFlatTensorSequence. The triangle module publicly imports that
module, so existing importers still see exactly the same declarations. Their names,
signatures, bodies and docstrings are unchanged. The ordinary sequence needs the
same typed expressions to package its maps before specializing the coefficient
rings; importing its consumer would form a cycle. The fully expanded ordinary
statement alone exceeded the 60-second compile limit. A generic record with these
typed definitions checks in 8.5 seconds. This changes no mathematical definition or
target meaning, and does not split a proof to evade the compile limit.

## Old

In Sheaf.Algebra.Homology.SuccessiveQuotientLinearTriangle:

```lean
section Models
variable {B S : Sheaf J CommRingCat.{r}} {φ : B ⟶ S}
  [HasDerivedCategory.{wB} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J B))]
  [HasDerivedCategory.{wS} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J S))]

/-- The termwise extension in the recorded derived-change-of-rings presentation.
Source: Stacks 06YY (blueprint: lem-pe-successive-quotient-linear-triangle). -/
def successiveQuotientTensorModel (F : DerivedChangeOfRingsCochainModel φ)
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ) :
    CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S)) ℤ :=
  (F.E.mapHomologicalComplex (.up ℤ)).obj P

/-- A pure tensor in the presented extension, using its fixed object equality.
The existing scalar-first convention writes the paper's x tensor s as s tensor x.
Source: Stacks 03EK, 06YY (blueprint: lem-pe-successive-quotient-linear-triangle). -/
def successiveQuotientTensorSection (F : DerivedChangeOfRingsCochainModel φ)
    (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J B))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) : (F.E.obj M).val.obj U :=
  (eqToHom (F.obj_eq M).symm).val.app U
    ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
      (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] x))

/-- Restrict the scalar action on every term and differential of the tensor model.
Source: Stacks 03D7, 06YY (blueprint: lem-pe-successive-quotient-linear-triangle). -/
def successiveQuotientRestrictedModel {A : Sheaf J CommRingCat.{r}} (a : A ⟶ S)
    (F : DerivedChangeOfRingsCochainModel φ)
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ) :
    CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J A)) ℤ :=
  (Functor.mapHomologicalComplex
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map a))
    (.up ℤ)).obj (successiveQuotientTensorModel F P)
end Models
```

## New

In Sheaf.Algebra.Homology.SuccessiveQuotientFlatTensorSequence, publicly re-exported
by Sheaf.Algebra.Homology.SuccessiveQuotientLinearTriangle:

```lean
section Models
variable {B S : Sheaf J CommRingCat.{r}} {φ : B ⟶ S}
  [HasDerivedCategory.{wB} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J B))]
  [HasDerivedCategory.{wS} (ringedSiteModules.{r}
    (derivedChangeRingIndependentCoefficients J S))]

/-- The termwise extension in the recorded derived-change-of-rings presentation.
Source: Stacks 06YY (blueprint: lem-pe-successive-quotient-linear-triangle). -/
def successiveQuotientTensorModel (F : DerivedChangeOfRingsCochainModel φ)
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ) :
    CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S)) ℤ :=
  (F.E.mapHomologicalComplex (.up ℤ)).obj P

/-- A pure tensor in the presented extension, using its fixed object equality.
The existing scalar-first convention writes the paper's x tensor s as s tensor x.
Source: Stacks 03EK, 06YY (blueprint: lem-pe-successive-quotient-linear-triangle). -/
def successiveQuotientTensorSection (F : DerivedChangeOfRingsCochainModel φ)
    (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J B))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) : (F.E.obj M).val.obj U :=
  (eqToHom (F.obj_eq M).symm).val.app U
    ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
      (s ⊗ₜ[B.obj.obj U, (φ.hom.app U).hom] x))

/-- Restrict the scalar action on every term and differential of the tensor model.
Source: Stacks 03D7, 06YY (blueprint: lem-pe-successive-quotient-linear-triangle). -/
def successiveQuotientRestrictedModel {A : Sheaf J CommRingCat.{r}} (a : A ⟶ S)
    (F : DerivedChangeOfRingsCochainModel φ)
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J B)) ℤ) :
    CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J A)) ℤ :=
  (Functor.mapHomologicalComplex
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map a))
    (.up ℤ)).obj (successiveQuotientTensorModel F P)
end Models
```

## Users

`tools/downstream.py Sheaf.Algebra.Homology.SuccessiveQuotientLinearTriangle --uses
successiveQuotientTensorModel successiveQuotientTensorSection
successiveQuotientRestrictedModel` reports zero downstream modules and only the
item itself as a textual user of these three declarations. Unfinished DAG parents
remain unchanged and retain the same public import interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.SuccessiveQuotientLinearTriangle | Q3 | Publicly imports the definitions; its structure, theorem signature and every definition body stay unchanged. |
| Sheaf.Algebra.Homology.SuccessiveQuotientFlatTensorSequence | Q3 (new) | Hosts the same definitions and uses them in the ordinary cochain data structure. |

## Status

landed 20261021T111443-L-148638 2026-10-21 (merge of deliver/Q3/Sheaf.Algebra.Homology.SuccessiveQuotientLinearTriangle)
