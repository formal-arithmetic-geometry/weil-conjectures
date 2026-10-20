# AlgebraicGeometry.Scheme.Modules.single_field_fibre_homology

## Reason

Restore the quarantined Sheaf module by re-exporting the existing upstream theorem.
The public theorem signatures are byte-for-byte identical. Both original modules
have exactly the same eight imports, including the same public imports. Therefore
re-exporting upstream introduces no mixture of dependency twins; the warning in
coord/changes/retire-sheaf-twins-kept-20261020.tsv describes an older import graph.
The upstream proof already qualifies AlgebraicGeometry.derivedPullback and compiles
as part of the published library. No upstream declaration or source file is changed.

## Old

The following declaration was defined in Sheaf.AlgebraicGeometry.FieldFibreHomology:

```lean
theorem single_field_fibre_homology
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (i r : ℕ) (hzero : ∀ q : ℕ, q ≠ i → IsZero (P.homology q))
    (hrank : (P.homology i).IsFiniteLocallyFreeOfRank r)
    {R : CommRingCat.{u}} (hR : IsField R) (f : Spec R ⟶ Y) :
      let Q := ((Modules.pullback f).mapHomologicalComplex _).obj P
      (∀ q : ℕ, q ≠ i → IsZero (Q.homology q)) ∧
        (Q.homology i).IsFiniteLocallyFreeOfRank r
```

## New

The identical declaration is imported from
WeilConjectures.AlgebraicGeometry.FieldFibreHomology:

```lean
theorem single_field_fibre_homology
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (i r : ℕ) (hzero : ∀ q : ℕ, q ≠ i → IsZero (P.homology q))
    (hrank : (P.homology i).IsFiniteLocallyFreeOfRank r)
    {R : CommRingCat.{u}} (hR : IsField R) (f : Spec R ⟶ Y) :
      let Q := ((Modules.pullback f).mapHomologicalComplex _).obj P
      (∀ q : ℕ, q ≠ i → IsZero (Q.homology q)) ∧
        (Q.homology i).IsFiniteLocallyFreeOfRank r
```

The Sheaf module keeps its two original public imports and adds a public import of
that upstream module. Its duplicate theorem and three private proof helpers are
removed. The DAG attachment points to the existing upstream declaration. The proof
and proof dependencies of the node still describe the same upstream argument.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FieldFibreHomology | Q5 | Restored as a re-export. |
| WeilConjectures.AlgebraicGeometry.FiniteFreeSingleFieldFibre | unclaimed | Already imports upstream; unchanged. |

No live or quarantined module imports the Sheaf item (checked by rg and downstream.py).
No target signature or definition changes. Imported instances and declarations are
those already supplied by exactly the same dependency modules. No consumer needs
an adaptation. The downstream script output is recorded in report.md.

## Status

landed 20261020T155435-L-3242650 2026-10-20 (merge of deliver/Q5/Sheaf.AlgebraicGeometry.FieldFibreHomology)
