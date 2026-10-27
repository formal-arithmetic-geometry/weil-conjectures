# closed_test_scalar_model_coherence supporting proof steps

## Reason

Expose the independent universal, section and scalar-model comparison arguments as
separate proof steps. Prove the computation-unit clause and assemble actual derived-map
naturality and the ordinary scalar-unit specialization. The original theorem signature,
all original definitions and every target statement are preserved.

## Old

The five new modules and their public supporting theorems did not exist.
The item module has one public theorem with its entire proof postponed.

## New

The original theorem signature is unchanged. All added imports in the item are private.
The new public declarations have the following signatures (namespace
`AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence`, with the coefficient-ring
variables and instances declared in their modules):

`Sheaf.Paper.ClosedTestChainModelMapNaturality`:

```lean
theorem closed_test_chain_model_map_naturality
    (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ a)))
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ((liftedTest A a V).left, ⊤)]
    {K N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    (α : K ⟶ N) (M : TestModel Λ h K) (P : TestModel Λ h N) :
    chainRestriction Λ A a w V M.I M.J M.j ≫
        modelMap Λ (testFibre fZ (closedTest A a V)) M.J P.J M.pullIso P.pullIso
          ((CondensedRing.upperStar Λ h).mapDerivedCategory.map α) =
      modelMap Λ (testFibre f (liftedTest A a V)) M.I P.I M.e P.e α ≫
        chainRestriction Λ A a w V P.I P.J P.j
```

`Sheaf.Paper.ClosedTestModelMapNaturality`:

```lean
theorem closed_test_model_map_naturality
    (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ a)))
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ((liftedTest A a V).left, ⊤)]
    {K N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    (α : K ⟶ N) (M : TestModel Λ h K) (P : TestModel Λ h N) :
    ModelMapCoherence A a f h fZ w V α M P
```

`Sheaf.Paper.ClosedTestScalarModelSquares`:

```lean
theorem closed_test_scalar_model_squares (hc : UniversalCoherence c) (hs : SectionCoherence c)
    (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ a)))
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ((liftedTest A a V).left, ⊤)]
    (N : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X)))
    (M : TestModel S h N.obj) (P : TestModel Λ h ((restrict c X).obj N.obj)) :
    ModelCoherence c A a f h fZ w V N.obj M P
```

`Sheaf.Paper.ClosedTestScalarSectionCoherence`:

```lean
theorem closed_test_scalar_section_coherence : SectionCoherence c
```

`Sheaf.Paper.ClosedTestScalarSectionSquares`:

```lean
theorem closed_test_scalar_section_squares :
(∀ {X Y : Scheme.{u}} (b : X ⟶ Y) (W : Y.ProEt) (W' : X.ProEt)
      (t : W' ⟶ testFibre b W)
      (F : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj S Y)),
    (sectionArrow S b W W' t).app F ≫
        (evaluation Λ W').map ((CondensedRing.comapUpperStarIso c b).hom.app F) =
      (sectionArrow Λ b W W' t).app ((restriction c Y).obj F)) ∧
  (∀ {X Y : Scheme.{u}} (b : X ⟶ Y) (W : Y.ProEt) (W' : X.ProEt)
      (t : W' ⟶ testFibre b W)
      (N : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj S Y))),
    (derivedSectionArrow S b W W' t).app N ≫
        (gamma c W').app ((CondensedRing.upperStar S b).mapDerivedCategory.obj N) ≫
        (evaluation Λ W').rightDerivedFunctor.map
          ((CondensedRing.derivedComapUpperStarIso c b).hom.app N) =
      (gamma c W).app N ≫
        (derivedSectionArrow Λ b W W' t).app ((restrict c Y).obj N)) ∧
  (∀ {X Y : Scheme.{u}} (b : X ⟶ Y) (W : Y.ProEt)
      (N : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X))),
    (derivedPushEvaluation S b W).hom.app N ≫ (gamma c (testFibre b W)).app N =
      (gamma c W).app ((CondensedRing.moduleObjectDerivedPushforward S b).obj N) ≫
        (evaluation Λ W).rightDerivedFunctor.map ((restrictPush c b).app N) ≫
        (derivedPushEvaluation Λ b W).hom.app ((restrict c X).obj N))
```

`Sheaf.Paper.ClosedTestScalarUniversalCoherence`:

```lean
theorem closed_test_scalar_universal_coherence : UniversalCoherence c
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ClosedTestScalarModelCoherence | S9 | Uses the new proof steps; signature preserved. |
| Sheaf.Paper.ClosedTestModelMapNaturality | new, S9 | Uses ClosedTestChainModelMapNaturality for the chain square. |
| Sheaf.Paper.ClosedTestScalarSectionCoherence | new, S9 | Uses ClosedTestScalarSectionSquares. |
| Sheaf.Paper.ClosedTestScalarModelSquares | new, S9 | Assumes the unchanged UniversalCoherence and SectionCoherence predicates. |

The source-only downstream scan of the original item reports zero Lean importers.
The unfinished parent DAG node lem-sfb-closed-test-derived-exchange-model still uses it;
that dependency and its Lean attachment are retained. No consumer adaptation is needed.

## Status

landed 20261025T101407-L-3688871 2026-10-25 (merge of deliver/S9/Sheaf.Paper.ClosedTestScalarModelCoherence)
