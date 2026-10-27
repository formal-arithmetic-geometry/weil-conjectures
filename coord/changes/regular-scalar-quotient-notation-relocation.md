# CategoryTheory.RegularScalarQuotient notation declarations

## Reason

Move the existing, fully constructed notation into a common support module so the
presentation, exact module row and tensor comparison can be separate proof items.
They cannot import their consumer theorem without an import cycle. Every declaration
keeps its name, signature and body. The original module publicly re-exports the support
module and therefore the complete original public API. This is a relocation, with
no mathematical definition or statement change and no target meaning change.

## Old

In `Sheaf.Algebra.Homology.RegularScalarQuotientExactRow`, verbatim:

```lean
/-- The recorded module category over a commutative ring sheaf.
Source: Stacks 03D7 (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- The existing regular module sheaf.
Source: Stacks 03EK (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev unit (R : Sheaf J CommRingCat.{r}) : Modules R :=
  SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- The recorded scalar restriction.
Source: Stacks 03D7 (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev res {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S) :=
  SheafOfModules.restrictScalars.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map f)

/-- The canonical linear map induced by a ring-sheaf map.
Source: Stacks 03D7 (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev ringMap {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S) :=
  SheafOfModules.RegularQuotientCone.ringMap f

variable (R : Sheaf J CommRingCat.{r}) (t : (unit R).sections)

/-- Scalar powers on any module, using the recorded global scalar transformation.
Source: Stacks 03EK (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev mul (M : Modules R) (k : ℕ) : M ⟶ M :=
  endoPow ((SheafOfModules.RegularQuotientCone.scalar R t).app M) k

/-- The existing quotient ring sheaf at positive level n+1.
Source: Stacks 03CY (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev B (n : ℕ) := principalPowerRingQuotient R t (n + 1)

/-- Its canonical quotient projection.
Source: Stacks 03CY (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev projection (n : ℕ) : R ⟶ B R t n := principalPowerRingProjection R t (n + 1)

/-- The quotient, regarded as an R-module by the canonical projection.
Source: Stacks 03D7 (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev Q (n : ℕ) : Modules R := (res (projection R t n)).obj (unit (B R t n))

/-- A module concentrated in degree zero, using the existing single functor.
Source: Stacks 05RR (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev single {S : Sheaf J CommRingCat.{r}} (M : Modules S) :=
  (CochainComplex.singleFunctor (Modules S) 0).obj M

/-- The two-term scalar cone, in degrees minus one and zero.
Source: blueprint sk-lem-sp-tower, coefficient tensor
(blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev twoTerm (M : Modules R) (k : ℕ) :=
  CochainComplex.mappingCone ((CochainComplex.singleFunctor (Modules R) 0).map (mul R t M k))

/-- Inclusion of the degree-zero coefficient into its single complex.
Source: Stacks 05RR (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev singleIn {S : Sheaf J CommRingCat.{r}} (M : Modules S) :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv

/-- The degree-zero coordinate inclusion of the two-term scalar cone.
Source: blueprint sk-lem-sp-tower (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev rightIn (M : Modules R) (k : ℕ) : M ⟶ (twoTerm R t M k).X 0 :=
  singleIn M ≫ (CochainComplex.mappingCone.inr
    ((CochainComplex.singleFunctor (Modules R) 0).map (mul R t M k))).f 0

/-- The degree-minus-one coordinate inclusion of the two-term scalar cone.
Source: blueprint sk-lem-sp-tower (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev leftIn (M : Modules R) (k : ℕ) : M ⟶ (twoTerm R t M k).X (-1) :=
  singleIn M ≫ (CochainComplex.mappingCone.inl
    ((CochainComplex.singleFunctor (Modules R) 0).map (mul R t M k))).v 0 (-1) rfl

/-- The actual total tensor, with the quotient in the first factor.
Source: Stacks 06YN (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev tensor (n m : ℕ) :=
  CochainComplex.mapBifunctor (single (Q R t n)) (principalKoszul R t m)
    (curriedTensor (Modules R))

/-- The global scalar transported along a coefficient map.
Source: Stacks 03D7 (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
def scalarImage {S : Sheaf J CommRingCat.{r}} (f : R ⟶ S) : (unit S).sections :=
  (Functor.sectionsFunctor Cᵒᵖ).map
    (Functor.whiskerRight f.hom (forget CommRingCat.{r})) t

/-- The two-term complex over the higher quotient coefficient ring itself.
Source: blueprint sk-lem-sp-tower (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev P (n m : ℕ) :=
  twoTerm (B R t n) (scalarImage R t (projection R t n)) (unit (B R t n)) (m + 1)

/-- Restriction of the two-term quotient-linear complex to R.
Source: Stacks 03D7 (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev restrictedP (n m : ℕ) :=
  ((res (projection R t n)).mapHomologicalComplex (.up ℤ)).obj (P R t n m)

/-- The coefficient summand inclusion in the total tensor, normalized by x tensor 1.
Source: Stacks 03EK, tensor unit (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
def tensorIn (n m : ℕ) (i : ℤ) (j : unit R ⟶ (principalKoszul R t m).X i) :
    Q R t n ⟶ (tensor R t n m).X i :=
  (ρ_ (Q R t n)).inv ≫
    tensorHom (singleIn (Q R t n)) j ≫
    CochainComplex.ιMapBifunctor (single (Q R t n)) (principalKoszul R t m)
      (curriedTensor (Modules R)) 0 i i (zero_add i)

/-- The degree-zero inclusion in the recorded principal Koszul complex.
Source: blueprint sk-lem-sp-tower (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev koszulRight (m : ℕ) : unit R ⟶ (principalKoszul R t m).X 0 :=
  singleIn (unit R) ≫ (CochainComplex.mappingCone.inr
    ((CochainComplex.singleFunctor (Modules R) 0).map
      (endoPow (globalSectionMultiplication R t) (m + 1)))).f 0

/-- The degree-minus-one inclusion in the recorded principal Koszul complex.
Source: blueprint sk-lem-sp-tower (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev koszulLeft (m : ℕ) : unit R ⟶ (principalKoszul R t m).X (-1) :=
  singleIn (unit R) ≫ (CochainComplex.mappingCone.inl
    ((CochainComplex.singleFunctor (Modules R) 0).map
      (endoPow (globalSectionMultiplication R t) (m + 1)))).v 0 (-1) rfl
```

## New

In `Sheaf.Algebra.Homology.RegularScalarQuotientNotation`, the same declarations:

```lean
/-- The recorded module category over a commutative ring sheaf.
Source: Stacks 03D7 (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- The existing regular module sheaf.
Source: Stacks 03EK (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev unit (R : Sheaf J CommRingCat.{r}) : Modules R :=
  SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- The recorded scalar restriction.
Source: Stacks 03D7 (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev res {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S) :=
  SheafOfModules.restrictScalars.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map f)

/-- The canonical linear map induced by a ring-sheaf map.
Source: Stacks 03D7 (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev ringMap {R S : Sheaf J CommRingCat.{r}} (f : R ⟶ S) :=
  SheafOfModules.RegularQuotientCone.ringMap f

variable (R : Sheaf J CommRingCat.{r}) (t : (unit R).sections)

/-- Scalar powers on any module, using the recorded global scalar transformation.
Source: Stacks 03EK (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev mul (M : Modules R) (k : ℕ) : M ⟶ M :=
  endoPow ((SheafOfModules.RegularQuotientCone.scalar R t).app M) k

/-- The existing quotient ring sheaf at positive level n+1.
Source: Stacks 03CY (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev B (n : ℕ) := principalPowerRingQuotient R t (n + 1)

/-- Its canonical quotient projection.
Source: Stacks 03CY (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev projection (n : ℕ) : R ⟶ B R t n := principalPowerRingProjection R t (n + 1)

/-- The quotient, regarded as an R-module by the canonical projection.
Source: Stacks 03D7 (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev Q (n : ℕ) : Modules R := (res (projection R t n)).obj (unit (B R t n))

/-- A module concentrated in degree zero, using the existing single functor.
Source: Stacks 05RR (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev single {S : Sheaf J CommRingCat.{r}} (M : Modules S) :=
  (CochainComplex.singleFunctor (Modules S) 0).obj M

/-- The two-term scalar cone, in degrees minus one and zero.
Source: blueprint sk-lem-sp-tower, coefficient tensor
(blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev twoTerm (M : Modules R) (k : ℕ) :=
  CochainComplex.mappingCone ((CochainComplex.singleFunctor (Modules R) 0).map (mul R t M k))

/-- Inclusion of the degree-zero coefficient into its single complex.
Source: Stacks 05RR (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev singleIn {S : Sheaf J CommRingCat.{r}} (M : Modules S) :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv

/-- The degree-zero coordinate inclusion of the two-term scalar cone.
Source: blueprint sk-lem-sp-tower (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev rightIn (M : Modules R) (k : ℕ) : M ⟶ (twoTerm R t M k).X 0 :=
  singleIn M ≫ (CochainComplex.mappingCone.inr
    ((CochainComplex.singleFunctor (Modules R) 0).map (mul R t M k))).f 0

/-- The degree-minus-one coordinate inclusion of the two-term scalar cone.
Source: blueprint sk-lem-sp-tower (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev leftIn (M : Modules R) (k : ℕ) : M ⟶ (twoTerm R t M k).X (-1) :=
  singleIn M ≫ (CochainComplex.mappingCone.inl
    ((CochainComplex.singleFunctor (Modules R) 0).map (mul R t M k))).v 0 (-1) rfl

/-- The actual total tensor, with the quotient in the first factor.
Source: Stacks 06YN (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev tensor (n m : ℕ) :=
  CochainComplex.mapBifunctor (single (Q R t n)) (principalKoszul R t m)
    (curriedTensor (Modules R))

/-- The global scalar transported along a coefficient map.
Source: Stacks 03D7 (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
def scalarImage {S : Sheaf J CommRingCat.{r}} (f : R ⟶ S) : (unit S).sections :=
  (Functor.sectionsFunctor Cᵒᵖ).map
    (Functor.whiskerRight f.hom (forget CommRingCat.{r})) t

/-- The two-term complex over the higher quotient coefficient ring itself.
Source: blueprint sk-lem-sp-tower (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev P (n m : ℕ) :=
  twoTerm (B R t n) (scalarImage R t (projection R t n)) (unit (B R t n)) (m + 1)

/-- Restriction of the two-term quotient-linear complex to R.
Source: Stacks 03D7 (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev restrictedP (n m : ℕ) :=
  ((res (projection R t n)).mapHomologicalComplex (.up ℤ)).obj (P R t n m)

/-- The coefficient summand inclusion in the total tensor, normalized by x tensor 1.
Source: Stacks 03EK, tensor unit (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
def tensorIn (n m : ℕ) (i : ℤ) (j : unit R ⟶ (principalKoszul R t m).X i) :
    Q R t n ⟶ (tensor R t n m).X i :=
  (ρ_ (Q R t n)).inv ≫
    tensorHom (singleIn (Q R t n)) j ≫
    CochainComplex.ιMapBifunctor (single (Q R t n)) (principalKoszul R t m)
      (curriedTensor (Modules R)) 0 i i (zero_add i)

/-- The degree-zero inclusion in the recorded principal Koszul complex.
Source: blueprint sk-lem-sp-tower (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev koszulRight (m : ℕ) : unit R ⟶ (principalKoszul R t m).X 0 :=
  singleIn (unit R) ≫ (CochainComplex.mappingCone.inr
    ((CochainComplex.singleFunctor (Modules R) 0).map
      (endoPow (globalSectionMultiplication R t) (m + 1)))).f 0

/-- The degree-minus-one inclusion in the recorded principal Koszul complex.
Source: blueprint sk-lem-sp-tower (blueprint: lem-sp-regular-scalar-quotient-exact-row). -/
abbrev koszulLeft (m : ℕ) : unit R ⟶ (principalKoszul R t m).X (-1) :=
  singleIn (unit R) ≫ (CochainComplex.mappingCone.inl
    ((CochainComplex.singleFunctor (Modules R) 0).map
      (endoPow (globalSectionMultiplication R t) (m + 1)))).v 0 (-1) rfl
```

Only the blueprint docstring references change to the definition node owning the
relocated notation. `RegularScalarQuotientExactRow` publicly imports this module.
Its sole theorem has the same statement, with the unused inequality binder renamed
`_hm`; all universe parameters, hypotheses and conclusions are retained.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.RegularScalarQuotientExactRow` reported
zero downstream Lean modules. No original consumer needs adaptation. The unfinished
parent DAG proof still needs this item, so the module is retained.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.RegularScalarQuotientExactRow | W3 | Imports the relocated notation and proves the original theorem. |
| Sheaf.Algebra.Homology.RegularScalarQuotientPresentation | new, W3 | Uses the canonical quotient notation. |
| Sheaf.Algebra.Homology.RegularScalarQuotientModuleRow | new, W3 | States the module-sheaf part of the original argument. |
| Sheaf.Algebra.Homology.RegularScalarQuotientTensorComparison | new, W3 | States the normalized chain isomorphism part. |

## Status

landed 20261025T164638-L-1046783 2026-10-25 (merge of deliver/W3/Sheaf.Algebra.Homology.RegularScalarQuotientExactRow)
