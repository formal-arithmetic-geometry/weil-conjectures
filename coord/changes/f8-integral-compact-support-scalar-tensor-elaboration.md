# WeilConjectures.PurCompactSupport.scalarTensorTotal and scalar tensor comparisons

## Reason

Repair of returned head `935fb735823` (C-935fb): the original landing rejected
the reviewer override basename. This record is included directly at
`coord/changes/f8-integral-compact-support-scalar-tensor-elaboration.md` in the
rebased delivery. If a further reviewer correction is necessary, the landing tool
expects the override basename
`f8-integral-compact-support-scalar-tensor-elaboration.change.md`; the ordinary
record basename is not an accepted override name. The reviewer of head `93fe92d714f`
completed the users table below (four computed users were missing, and three holders were
stale) and supplies this record under that override basename.

The unchanged item exceeded the per-file compile limit in this session. The expensive
work was repeated reconstruction and kernel checking of scalar tensor model types.
Spell out the already inferred result types, pin the canonical tensor-preadditive
instances in the total-map construction, and keep derived-category and monoidal
constructions locally irreducible when only their API is needed. These are elaboration
repairs: neither the comparison objects nor their normalization changes.

The ordinary naturality proof uses the existing pure-tensor mapping and extensionality
lemmas. Its scalar-extension unit is the same normalized tensor section.

## Old

```lean
def scalarOrdinaryTensor {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) :=
  (scalarOrdinaryTensor_existsUnique a).exists.choose

def scalarTensorTotal {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (P Q : CochainComplex (pbcModules W R) ℤ) :=
  letI := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  letI := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} S
  tensorPullbackTotal (pbcExtend a) (scalarOrdinaryTensor a)
    (fun {_ _ _ _} v z ↦ scalarOrdinaryTensor_naturality a v z) P Q

def scalarTensor {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (r : ProEtaleTensorModel W R) (s : ProEtaleTensorModel W S) :=
  (scalarTensor_existsUnique a r s).exists.choose
```

## New

```lean
def scalarOrdinaryTensor {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S) :
    ∀ M N : pbcModules W R,
      (pbcExtend a).obj (((proEtaleOrdinaryTensor W R).obj M).obj N) ≅
        ((proEtaleOrdinaryTensor W S).obj ((pbcExtend a).obj M)).obj
          ((pbcExtend a).obj N) :=
  (scalarOrdinaryTensor_existsUnique a).exists.choose

def scalarTensorTotal {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (P Q : CochainComplex (pbcModules W R) ℤ) :
    CochainComplex.mapBifunctor
      (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj P)
      (((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj Q) (proEtaleOrdinaryTensor W S) ⟶
        ((pbcExtend a).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor W R)) :=
  letI := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  letI := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} S
  letI := proEtaleTensorPreadditive W R
  letI := proEtaleTensorPreadditive W S
  tensorPullbackTotal (pbcExtend a) (scalarOrdinaryTensor a)
    (fun {_ _ _ _} v z ↦ by
      simpa only [proEtaleOrdinaryTensor, MonoidalCategory.curriedTensor,
        MonoidalCategory.tensorHom_def, Category.assoc] using
          scalarOrdinaryTensor_naturality a v z) P Q

def scalarTensor {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (r : ProEtaleTensorModel W R) (s : ProEtaleTensorModel W S) :
    r.tensor ⋙ pbcDerivedExtend a ≅
      ((pbcDerivedExtend a).prod (pbcDerivedExtend a)) ⋙ s.tensor :=
  (scalarTensor_existsUnique a r s).exists.choose
```

The `simpa only` argument converts curried tensor notation to the same tensor-hom
naturality equation. The explicitly supplied preadditivity instances are the canonical
instances already synthesized by the original construction. Result annotations expose
exactly the previously inferred types. Local reducibility and option changes do not
alter exported attributes. No target signature changes; the target interpretation is
unchanged. The independent review should check these definitional identifications.
Because these definitions occur below the targets, the target interpretation check
reopens for this elaboration repair. The existing theorem binders and conclusions
are unchanged; the old and new expressions define the same canonical objects.

Four proved public aliases specialize the existing canonical site instances to
the coefficient universe. They are installed only locally. They prevent ambiguous
universe search and keep private helpers out of public definitions. These aliases
are included in the item node.

The new proved aliases and their local instance registrations are:

```lean
-- Use the canonical concrete site instances throughout this proof context.
/-- Canonical smallness of the coefficient site.
Source: the existing integral coefficient site instances.
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
theorem coefficientSiteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _

attribute [local instance 100000] coefficientSiteSmall

/-- Canonical ring sheafification on the coefficient site.
Source: the existing integral coefficient site instances.
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
theorem coefficientRingSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, 0} W

attribute [local instance 100000] coefficientRingSheafify

/-- Canonical abelian sheafification on the coefficient site.
Source: the existing integral coefficient site instances.
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
theorem coefficientAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} W

attribute [local instance 100000] coefficientAbSheafify

/-- Canonical local bijectivity criterion on the coefficient site.
Source: the existing integral coefficient site instances.
(blueprint: lem-pur-compact-support-integral-coefficient-comparison). -/
theorem coefficientAbLocallyBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} W

attribute [local instance 100000] coefficientAbLocallyBijective
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | F8 | Same elaborated type and construction; no consumer changes. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Same elaborated type and construction; no consumer changes. |
| Sheaf.Paper.CompactSupportProjectionCoefficientChange | unclaimed | Same elaborated type and construction; no consumer changes. Direct importer, compiled against the changed module by the reviewer. |
| Sheaf.Paper.CompactSupportProjectionFormula | F4 | Same elaborated type and construction; no consumer changes. |
| Sheaf.Paper.CompactSupportScalarProjectionIdentification | K7 | Same elaborated type and construction; no consumer changes. |
| Sheaf.Paper.CompactificationCompletedRealizationData | unclaimed | Same elaborated type and construction; no consumer changes. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | unclaimed | Same elaborated type and construction; no consumer changes. |
| Sheaf.Paper.ConcreteProjectionCoefficientCoherence | unclaimed | Same elaborated type and construction; no consumer changes. Direct importer, compiled against the changed module by the reviewer. |
| Sheaf.Paper.ConcreteProjectionReductionData | unclaimed | Same elaborated type and construction; no consumer changes. |
| Sheaf.Paper.ConcreteProjectionReductionSquare | unclaimed | Same elaborated type and construction; no consumer changes. |
| Sheaf.Paper.ConcreteProperScalarTensorSquare | unclaimed | Same elaborated type and construction; no consumer changes. |
| Sheaf.Paper.PfReductionProperOpenIdentities | unclaimed | Same elaborated type and construction; no consumer changes. |
| Sheaf.Paper.ProjectionFiniteReduction | H8 | Same elaborated type and construction; no consumer changes. |
| Sheaf.Paper.RelativeProductFactors | unclaimed | Same elaborated type and construction; no consumer changes. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | T8 | Same elaborated type and construction; no consumer changes. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels | unclaimed | Same elaborated type and construction; no consumer changes. Direct importer, compiled against the changed module by the reviewer. |

## Status

landed 20261025T204549-L-2975547 2026-10-25 (merge of deliver/F8/Sheaf.Paper.IntegralCompactSupportCoefficientComparison)
