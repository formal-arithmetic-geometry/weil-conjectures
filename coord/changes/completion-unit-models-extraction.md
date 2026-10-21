# WeilConjectures.CompletionUnit.OrdinaryModel and DerivedModel

## Reason

The original theorem combines construction of compatible ordinary/derived adjunction
models with the subsequent cone, unit and two-resolution formulas. The construction
needs an independent statement module. Extract the existing model definitions into
`Sheaf.Paper.CompletionUnitModels`, publicly re-exported from the original module, to
avoid an import cycle. No declaration is renamed, no signature or body is changed,
and no target statement changes. Blueprint docstrings now identify the definition node.
This is a module-layout change only; it adds no assumptions or chosen data.

## Old

The following declarations were defined in
`lean/Sheaf/Paper/CompletionUnitStrictQuotientModel.lean`:

```lean
/-- Exact restriction of a system complex to its completed-coefficient tower.
Source: Stacks 0941 (blueprint: lem-trf-completion-unit-strict-quotient-model). -/
abbrev tower := (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)

/-- The ordinary sequence direct image: restriction of rings followed by inverse limit.
Source: Stacks 07A6, 0941 (blueprint: lem-trf-completion-unit-strict-quotient-model). -/
abbrev ordinaryLimit := coefficientSequenceRestriction l E W ⋙
  (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)

/-- The quotient-system tensor functor with its ordinary adjunction and actual tensor
unit. The evaluation isomorphisms identify its components with the recorded scalar
extension, and `transition` fixes the strict quotient maps, including all levels.
`unit_tensor` fixes the adjunction itself on sections, rather than only its functors.
Source: Stacks 03EK, 07A6, 0941 and item proof step 2
(blueprint: lem-trf-completion-unit-strict-quotient-model). -/
structure OrdinaryModel where
  tensor : scalarReductionSource l E W ⥤ coefficientSequenceModules l E W
  [additive : tensor.Additive]
  evaluation : ∀ n : ℕ, tensor ⋙ coefficientSequenceEvaluation l E W n ≅
    scalarReductionExtension l E W n
  transition : ∀ (M : scalarReductionSource l E W) {m n : ℕ} (h : n ≤ m),
    (coefficientSequenceTransition l E W h).app (tensor.obj M) ≫
        (normalizedDVRModuleRes l E W h).map ((evaluation n).hom.app M) =
      (evaluation m).hom.app M ≫ (coefficientOrdinaryQuotient l E W h).app M
  adjunction : tensor ⊣ ordinaryLimit l E W
  unit_tensor : ∀ (M : scalarReductionSource l E W) (n : ℕ) (V : W.ProEtᵒᵖ)
    (x : M.val.obj V),
    ((adjunction.unit.app M ≫
        limit.π ((coefficientSequenceRestriction l E W).obj (tensor.obj M)) (op n) ≫
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
          (tensor.obj M) ≫
        (scalarReductionRestriction l E W n).map ((evaluation n).hom.app M)).val.app V) x =
      unrestrictedIntegralTensorSection l E W n M V 1 x
  limitComparison : (ordinaryLimit l E W).mapHomologicalComplex (.up ℤ) ≅
    tower l E W ⋙ roosLimitFunctor
  limitComparison_projection : ∀ (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (n : ℕ) (p : ℤ),
    ((limitComparison.hom.app I) ≫
        limit.π ((tower l E W).obj I).asFunctor (op n)).f p =
      limit.π ((coefficientSequenceRestriction l E W).obj (I.X p)) (op n)

attribute [instance] OrdinaryModel.additive

/-- The strict quotient system of a complex is the termwise ordinary tensor functor.
Source: Stacks 06YY, 0941 (blueprint: lem-trf-completion-unit-strict-quotient-model). -/
abbrev OrdinaryModel.quotient (M : OrdinaryModel l E W) :=
  M.tensor.mapHomologicalComplex (.up ℤ)

/-- The ordinary-adjunction transpose, in the canonical termwise-limit coordinates.
Source: Stacks 07A6 and item proof step 2
(blueprint: lem-trf-completion-unit-strict-quotient-model). -/
def OrdinaryModel.transpose (M : OrdinaryModel l E W)
    {Q : CochainComplex (scalarReductionSource l E W) ℤ}
    {I : CochainComplex (coefficientSequenceModules l E W) ℤ}
    (a : (M.quotient l E W).obj Q ⟶ I) :
    Q ⟶ limit ((tower l E W).obj I).asFunctor :=
  (M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I a ≫
    M.limitComparison.hom.app I

/-- The strict quotient augmentation to the ordinary limit; its level maps are z tensor 1.
Source: Stacks 07A6, 0941 and item proof steps 2, 5
(blueprint: lem-trf-completion-unit-strict-quotient-model). -/
def OrdinaryModel.augmentation (M : OrdinaryModel l E W)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    Q ⟶ limit ((tower l E W).obj ((M.quotient l E W).obj Q)).asFunctor :=
  M.transpose l E W (𝟙 _)

/-- Canonical derived comparisons for the actual ordinary quotient adjunction.
The limit unit is pinned on every K-injective tower by the existing right-derived
functor comparison. The Roos isomorphism is normalized on the ordinary inclusion.
The system unit is the composition comparison for exact restriction and projection.
Finally `hom_normalization` derives the ordinary Hom correspondence on chain maps.
These conditions specify comparisons, rather than postulating arbitrary isomorphisms.
Source: Stacks 09T5, 0D6E, 0941 and item proof steps 3--4, 6
(blueprint: lem-trf-completion-unit-strict-quotient-model). -/
structure DerivedModel (S : CoefficientDerivedSystemCalculus l E W)
    (M : OrdinaryModel l E W) where
  towerLimitComparison :
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ) ≅ roosLimitFunctor
  towerLimitComparison_projection :
    ∀ (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ) (p : ℤ),
      (towerLimitComparison.hom.app Z ≫ limit.π Z.asFunctor (op n)).f p =
        limit.π (Z.X p) (op n)
  limitUnit : roosLimitFunctor ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W
  limitUnit_normalization :
    ∀ (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective],
      limitUnit.app J ≫
          ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
            scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom =
        DerivedCategory.Q.map (towerLimitComparison.inv.app J)
  roos : roosF ⋙ DerivedCategory.Q ≅
    DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W
  roos_normalization : ∀ Z,
    DerivedCategory.Q.map (roosι Z) ≫ roos.hom.app Z = limitUnit.app Z
  systemUnit : (ordinaryLimit l E W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ coefficientSequenceLimit l E W
  system_isIso : ∀ (I : CochainComplex (coefficientSequenceModules l E W) ℤ),
    I.IsKInjective → IsIso (systemUnit.app I)
  systemUnit_composition : ∀ I,
    systemUnit.app I = DerivedCategory.Q.map (M.limitComparison.hom.app I) ≫
      limitUnit.app ((tower l E W).obj I) ≫
      (coefficientConstantTowerLimit l E W).map
        ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app I)
  reductionComparison : DerivedCategory.Q ⋙ S.reduction ⟶
    M.quotient l E W ⋙ DerivedCategory.Q
  reduction_isLeftDerived : S.reduction.IsLeftDerivedFunctor reductionComparison
    (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ))
  reduction_isIso : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ),
    Q.IsKFlatIndependentCoefficients → (∀ p : ℤ, (Q.X p).IsFlatOnSite) →
      IsIso (reductionComparison.app Q)
  reduction_evaluation : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : Q.IsKFlatIndependentCoefficients) (_hflat : ∀ p : ℤ, (Q.X p).IsFlatOnSite) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E W n).map (reductionComparison.app Q) ≫
        (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
          ((M.quotient l E W).obj Q) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q) =
      (S.reductionEvaluation n).hom.app (DerivedCategory.Q.obj Q) ≫
        (coefficientFiniteReductionModel l E W Q hQ n).hom
  hom_normalization : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (a : (M.quotient l E W).obj Q ⟶ I),
    S.adjunction.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
        (reductionComparison.app Q ≫ DerivedCategory.Q.map a) =
      DerivedCategory.Q.map ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I a) ≫
        systemUnit.app I

/-- The strict cone augmentation is the ordinary-limit lift followed by the existing
zero-shifted-coordinate Roos inclusion. Thus this is a real chain map by construction.
Source: Stacks 08TC, 0941 and item proof step 5
(blueprint: lem-trf-completion-unit-strict-quotient-model). -/
def OrdinaryModel.coneAugmentation (M : OrdinaryModel l E W)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    Q ⟶ roosF.obj ((tower l E W).obj ((M.quotient l E W).obj Q)) :=
  M.augmentation l E W Q ≫ roosι _

/-- The normalized Roos comparison to the simultaneous reduction/limit object.
Both transports are the recorded localization comparison for exact restriction and
the universal left-derived comparison on the specified K-flat complex.
Source: Stacks 09T5, 0941 and item proof steps 3, 6
(blueprint: lem-trf-completion-unit-strict-quotient-model). -/
def DerivedModel.completionComparison
    {S : CoefficientDerivedSystemCalculus l E W} {M : OrdinaryModel l E W}
    (D : DerivedModel l E W S M) (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : Q.IsKFlatIndependentCoefficients) (hflat : ∀ p : ℤ, (Q.X p).IsFlatOnSite) :
    DerivedCategory.Q.obj (roosF.obj ((tower l E W).obj ((M.quotient l E W).obj Q))) ≅
      (coefficientSequenceLimit l E W).obj (S.reduction.obj (DerivedCategory.Q.obj Q)) :=
  D.roos.app _ ≪≫
    (coefficientConstantTowerLimit l E W).mapIso
      ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app
        ((M.quotient l E W).obj Q)).symm ≪≫
    (coefficientSequenceLimit l E W).mapIso
      (@asIso _ _ _ _ (D.reductionComparison.app Q) (D.reduction_isIso Q hQ hflat)).symm
```

## New

The exact declarations quoted above, including every field and composite, are now
defined in `lean/Sheaf/Paper/CompletionUnitModels.lean`. The sole textual changes within
that block are the docstrings' blueprint identifiers, now
`def-trf-completion-unit-models`. The original module publicly re-exports them with:

```lean
public import Sheaf.Paper.CompletionUnitModels
```

Their old qualified names, universes, visibility, reducibility, instance attribute and
bodies are retained. In particular OrdinaryModel, DerivedModel and the definitions used
by the original theorem still mean exactly what they meant before. The new construction
statement asserts existence of these original structures; it adds no premise to the
item theorem. The item's new statement dependency records only this relocation.

## Users

`tools/downstream.py Sheaf.Paper.CompletionUnitStrictQuotientModel --uses OrdinaryModel
DerivedModel` reports zero downstream Lean modules and only the item itself as a user.
The DAG parents are retained: this delivery does not withdraw the item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletionUnitStrictQuotientModel | J7 | Publicly re-exports definitions; its theorem statement is unchanged. |
| Sheaf.Paper.CompletionUnitModels | new, J7 | Defines the extracted declarations verbatim. |
| Sheaf.Paper.CompletionUnitCanonicalModels | new, J7 | States the independent compatible-model construction using those definitions. |

The two direct DAG parents, `lem-trf-effective-comparison-realization-models` and
`lem-weil-isomorphism-derived-pullback-comparison-normalization`, continue to use the
same unchanged completion-unit theorem. Their argument and statements still hold.

No external consumer needs adaptation. Since this is a verbatim relocation, it changes
no target's meaning and does not require a new semantic statement approval.

## Status

landed 20261021T140827-L-2759165 2026-10-21 (merge of deliver/J7/Sheaf.Paper.CompletionUnitStrictQuotientModel)
