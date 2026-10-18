# WeilConjectures.scalarReductionDerivedExistence

## Reason

The inferred type of this proof-valued definition retained the dependency's raw module
categories and locally selected standard localizations. Applying a generic derived-adjunction
lemma repeatedly compared these with the public scalar-reduction aliases, expanding constant
sheafification and localization data. The complete file exceeded 60 seconds. Giving the
existing witness its explicit canonical type makes the complete proof compile in 34.3 seconds.

This is a normalization of the interface: the old projection body is unchanged and Lean
checks it against the new type. The existential functor, comparison, left-derived universal
property, triangulatedness and K-flat comparison are all retained. No hypothesis or conclusion
is changed. The chosen derived extension and counit have unchanged bodies, and proof
irrelevance preserves their data under this definitionally equal presentation. No target
statement or mathematical definition changes meaning.

## Old

```lean
noncomputable def scalarReductionDerivedExistence :=
  (scalarReductionExistence l E Y n).choose_spec.choose_spec.choose_spec.choose_spec.2.2
```

## New

```lean
noncomputable def scalarReductionDerivedExistence :
    ∃ (LF : DerivedCategory (scalarReductionSource l E Y) ⥤
        DerivedCategory (scalarReductionTarget l E Y n))
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (scalarReductionExtension l E Y n).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (scalarReductionSource l E Y) (.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ P : CochainComplex (scalarReductionSource l E Y) ℤ,
          P.IsKFlatIndependentCoefficients →
            IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
  (scalarReductionExistence l E Y n).choose_spec.choose_spec.choose_spec.choose_spec.2.2
```

## Users

`tools/downstream.py Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction --uses
scalarReductionDerivedExistence` found 80 transitive importers and only one module mentioning
the declaration: the item itself. Its three textual occurrences are the declaration and the
bodies of `scalarReductionDerivedExtension` and `scalarReductionCounit`. Those bodies are
unchanged. Thus all downstream statements retain definitionally equal types and data; no
consumer adaptation is required. The complete item compiles against the normalized witness.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction` | G2 | Explicit type on the existing proof witness; unchanged constructions and theorem statements; all three proof holes closed. |

## Status

landed 20261018T091402-L-3254673 2026-10-18 (merge of deliver/G2/Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction)
