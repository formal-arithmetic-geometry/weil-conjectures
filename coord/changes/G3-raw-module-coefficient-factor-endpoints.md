# AlgebraicGeometry.Etale.moduleCoefficientFactor

## Reason

The raw class and the raw coefficient morphism use the named
`higherDirectImageRawOverComplex`. The module scalar coefficient factor repeated its
single-complex expansion in its endpoint type. Kernel checking the assigned factorization
then repeatedly compared the expanded derived objects with the named ones: the complete
proof compiled in 58.2 seconds, leaving too little room for the required axiom probe, and
other equivalent expansions exceeded the 60-second limit.

Name the already existing coefficient complexes in the endpoint type too. These are
definitionally the same endpoints (`higherDirectImageRawOverComplex_eq` is `rfl`). The
definition body is byte-for-byte unchanged: the same shift comparison at the same complex,
followed by the same shifted coefficient morphism. No object or isomorphism is chosen.
The abelian factor, imports, attributes and every adopted source-library file are unchanged.
No target changes meaning. The assigned module then compiled in 44.3 seconds.

## Old

```lean
noncomputable def moduleCoefficientFactor
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G))⟦q⟧) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) A.hom).obj G))⟦q⟧ :=
  ((moduleUpperStar Λ f.left).mapDerivedCategoryPlus.commShiftIso q).hom.app
    (higherDirectImageRawOverComplex Λ G B) ≫
    (shiftFunctor _ q).map (higherDirectImageRawOverCoefficient Λ G f)
```

## New

```lean
noncomputable def moduleCoefficientFactor
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.obj
        ((higherDirectImageRawOverComplex Λ G B)⟦q⟧) ⟶
      (higherDirectImageRawOverComplex Λ G A)⟦q⟧ :=
  ((moduleUpperStar Λ f.left).mapDerivedCategoryPlus.commShiftIso q).hom.app
    (higherDirectImageRawOverComplex Λ G B) ≫
    (shiftFunctor _ q).map (higherDirectImageRawOverCoefficient Λ G f)
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientFactors --uses
AlgebraicGeometry.Etale.moduleCoefficientFactor` lists six downstream modules, four of which
(including the definition module itself) contain direct uses of this name. The entire six
module set is checked unchanged against the delivered overlay. A search of quarantined Lean
sources finds only the assigned restored module. None of the six consumers or the definition
module is held by another group. No consumer statement changes, and no forced adaptation is
needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientFactors | unclaimed | Only the module factor's endpoint type is folded to the named complexes; its body and the abelian factor are unchanged. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomSourceFormula | unclaimed | Same coefficient map and definitionally equal endpoints; checked unchanged against the overlay. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomTargetFormula | unclaimed | Same coefficient map and definitionally equal endpoints; checked unchanged against the overlay. |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare | unclaimed | Same coefficient map and definitionally equal endpoints; checked unchanged against the overlay. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula | unclaimed | Same coefficient map and definitionally equal endpoints; checked unchanged against the overlay. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomEvaluation | unclaimed | Same coefficient map and definitionally equal endpoints; checked unchanged against the overlay. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula | unclaimed | Same coefficient map and definitionally equal endpoints; checked unchanged against the overlay. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas | G3 | Its proof uses the same coefficient map with the shared endpoints; its mathematical statement is unchanged. |

## Status

landed 20261020T221157-L-4153838 2026-10-20 (merge of deliver/G3/Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas)
