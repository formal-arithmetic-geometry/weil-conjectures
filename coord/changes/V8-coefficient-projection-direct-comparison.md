# coefficientProjectionSquare private comparison calculations

## Reason

The private conjugation calculation can identify the specified coefficient comparison
directly using the already proved exact-postcomposition comparison equality. This removes
its dependence on the ringed-square normalization theorem. Only private signatures and
proofs, a private proof import, and the public theorem proof change. All public signatures,
definitions, public imports and exported attributes stay verbatim.

## Old

```lean
private theorem derived_square_conjugate
    (e : U₂ ⋙ U₁ ≅ V₂ ⋙ V₁) (t : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂)
    (ht : e.hom = conjugateEquiv (a₁.comp a₂) (b₁.comp b₂) t.hom) :
    conjugateEquiv
      (a₁.derivedAdjunction.comp (a₂.derivedAdjunction.ofNatIsoRight
        U₂.rightDerivedFunctorIsoMapDerivedCategory))
      ((b₁.derivedAdjunction.ofNatIsoRight V₁.rightDerivedFunctorIsoMapDerivedCategory).comp
        b₂.derivedAdjunction)
      ((G₁.leftDerivedFunctorCompIso G₂).symm ≪≫
        (G₁ ⋙ G₂).leftDerivedFunctorNatIso t ≪≫ F₁.leftDerivedFunctorCompIso F₂).hom =
      (isoWhiskerRight U₂.rightDerivedFunctorIsoMapDerivedCategory.symm U₁.rightDerivedFunctor ≪≫
        (rightDerivedFunctorCompIso U₂ U₁).symm ≪≫ rightDerivedFunctorNatIso e ≪≫
        rightDerivedFunctorCompMapDerivedCategoryIsoViaRightDerived V₂ V₁).hom

private theorem path_conjugate :
    conjugateEquiv
      ((derivedUpperStarLowerStarAdjunction R f).comp
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)))
      ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)).comp
        (derivedUpperStarLowerStarAdjunction S f))
      (coefficientScalarPathIso a f).hom =
        (coefficientRingedDirectImageComparison a f).hom
```

## New

```lean
private theorem derived_square_conjugate
    (e : U₂ ⋙ U₁ ≅ V₂ ⋙ V₁) (t : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂)
    (ht : e.hom = conjugateEquiv (a₁.comp a₂) (b₁.comp b₂) t.hom) :
    conjugateEquiv
      (a₁.derivedAdjunction.comp (a₂.derivedAdjunction.ofNatIsoRight
        U₂.rightDerivedFunctorIsoMapDerivedCategory))
      ((b₁.derivedAdjunction.ofNatIsoRight V₁.rightDerivedFunctorIsoMapDerivedCategory).comp
        b₂.derivedAdjunction)
      ((G₁.leftDerivedFunctorCompIso G₂).symm ≪≫
        (G₁ ⋙ G₂).leftDerivedFunctorNatIso t ≪≫ F₁.leftDerivedFunctorCompIso F₂).hom =
      (isoWhiskerRight U₂.rightDerivedFunctorIsoMapDerivedCategory.symm U₁.rightDerivedFunctor ≪≫
        (rightDerivedFunctorCompIso U₂ U₁).symm ≪≫ rightDerivedFunctorNatIso e ≪≫
        rightDerivedFunctorCompMapDerivedCategoryIso V₂ V₁).hom

private theorem path_conjugate :
    conjugateEquiv
      ((derivedUpperStarLowerStarAdjunction R f).comp
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)))
      ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)).comp
        (derivedUpperStarLowerStarAdjunction S f))
      (coefficientScalarPathIso a f).hom =
        (derivedComapLowerStarIso a f).inv
```

The abstract conclusion now uses the direct exact-postcomposition comparison. The concrete
conclusion is the inverse of the specified `derivedComapLowerStarIso`, so the public proof
no longer needs `coefficient_ringed_square_normalization`.

## Users

`tools/downstream.py Sheaf.Paper.CoefficientProjectionSquare --uses coefficientProjectionSquare`
reported zero downstream modules. The two changed helpers are private to this module and
have no external users. The public theorem and all target meanings stay identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientProjectionSquare | V8 | Private direct-comparison proof; API unchanged. |

## Status

landed 20261024T191524-L-419747 2026-10-24 (merge of deliver/V8/Sheaf.Paper.CoefficientProjectionSquare)
