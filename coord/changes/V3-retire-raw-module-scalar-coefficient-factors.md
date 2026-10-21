# AlgebraicGeometry.Etale.moduleCoefficientFactor

## Reason

Retire the duplicate Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientFactors under the
human-approved coord/retire-items.tsv assignment. Both coefficient-map bodies are identical
to the adopted upstream definitions. The upstream module factor writes out the single-complex
endpoints named higherDirectImageRawOverComplex by the old copy. These endpoints are
definitionally equal. The abelian factor's signature is identical. Scratch Lean compatibility
proofs identify both old maps with the upstream maps by rfl, with only propext,
Classical.choice and Quot.sound reported by #print axioms.

Both modules now have the same upstream-only public imports. The square is the sole current
direct importer. Migrating it therefore adds no public import closure and creates no collision
between twins. No WeilConjectures file or Challenge target is edited. All original maps,
coefficient objects, choices and target meanings are retained.

The old square already times out against the current published library. Its proof now builds
checked HEq congruences around the same generic shift calculation and the existing raw-complex
endpoint equations, with local abbreviations and universe expressions handled explicitly. Heterogeneous
symmetry and transitivity use direct Lean proof constructors to avoid repeated elaborator
unification of the same derived endpoints.
The redundant private restatement of the unshifted identity is removed; the proof uses its
existing public theorem directly. The old private import of HigherDirectImageOverMapCoefficient
is removed: the small equality/congruence helper is local to the proof file.

The combined pullback statement also times out when its proof is replaced by sorry in a
scratch diagnostic. This is caused by repeated conversion of represented additive-group values
to their derived Hom types. The real identity constructions and the six equivalent statement
presentations that address this are recorded completely in
coord/changes/V3-native-raw-class-morphisms.md. The mathematical statements stay unchanged.

## Old

```lean
/-- The last two module pullback factors.
Source: Stacks Project, Tag 03Q8.
(blueprint: def-sbc-raw-scalar-coefficient-factors). -/
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

/-- The last two abelian pullback factors.
Source: Stacks Project, Tag 03Q8.
(blueprint: def-sbc-raw-scalar-coefficient-factors). -/
noncomputable def abelianCoefficientFactor
    {W : Scheme.{u}} (G : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar AddCommGrpCat.{u + 1} B.hom).obj G))⟦q⟧) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} A.hom).obj G))⟦q⟧ :=
  ((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.commShiftIso q).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} B.hom).obj G)) ≫
    (shiftFunctor _ q).map
      (((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
            (Over.w f).symm).inv.app G))
```

The square publicly imported Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientFactors.

## New

Withdraw the copy via deleted.txt. The square publicly imports
WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientFactors, whose existing definitions
remain verbatim:

```lean
/-- The last two module pullback factors.
Source: Stacks Project, Tag 03Q8.
(blueprint: def-sbc-raw-scalar-coefficient-factors). -/
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

/-- The last two abelian pullback factors.
Source: Stacks Project, Tag 03Q8.
(blueprint: def-sbc-raw-scalar-coefficient-factors). -/
noncomputable def abelianCoefficientFactor
    {W : Scheme.{u}} (G : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar AddCommGrpCat.{u + 1} B.hom).obj G))⟦q⟧) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} A.hom).obj G))⟦q⟧ :=
  ((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.commShiftIso q).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} B.hom).obj G)) ≫
    (shiftFunctor _ q).map
      (((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
            (Over.w f).symm).inv.app G))
```

The mathematical node def-sbc-raw-scalar-coefficient-factors is retained, with its Lean
attachment moved to the two upstream declarations. Every dependency and parent is retained.
The two pullback-formula modules now import the canonical factor module directly instead
of importing the coefficient square merely to obtain those definitions. Their node statement
dependencies likewise name the factor definition. The source-library boundary is respected
throughout. The raw coefficient square's public
statements and scalarCoefficientFactor construction stay unchanged; only its private proof
machinery changes.

## Users

This is the complete tools/downstream.py list for the two retired definitions. Every affected
module is unclaimed according to the current claim records. No quarantined Lean file imports
the retired module. The old listed Sheaf.RawModuleScalarPullbackModuleFormula consumer is
already absent with no rework row or archive. The three DAG parents continue to refer to the
same factor definitions, now canonically attached upstream. No unit route is bypassed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomSourceFormula | unclaimed | Use explicit identity views of raw class values in the same derived Hom equations; preserve all binders and mathematical content. |
| Sheaf.AlgebraicGeometry.RawModuleAbelianHomTargetFormula | unclaimed | Use explicit identity views of raw class values in the same derived Hom equations; preserve all binders and mathematical content. |
| Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare | unclaimed | Publicly import the upstream factor module; keep the scalar factor and public square statements; use checked endpoint congruences. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomCompositeFormula | unclaimed | Use explicit identity views of raw class values in the same derived Hom equations; preserve all binders and mathematical content. |
| Sheaf.AlgebraicGeometry.RawModuleScalarHomEvaluation | unclaimed | Use explicit identity views of raw class values in the same derived Hom equations; preserve all binders and mathematical content. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula | unclaimed | Use explicit identity views of raw class values in the same derived Hom equations; preserve all binders and mathematical content. |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackFormulas | unclaimed | Use explicit identity views of raw class values in the same derived Hom equations; preserve all binders and mathematical content. |

The six explicit raw-class presentations are definitionally the same equations, not new
hypotheses or weaker conclusions. Their old and new signatures and all user checks are in the
companion change record. No source declaration is removed, restated or weakened.

## Status

landed 20261021T061739-L-1825145 2026-10-21 (merge of deliver/V3/Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientFactors)
