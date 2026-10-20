# CategoryTheory.flatFilteredComplex_comparison

## Reason

Restore the quarantined module named in `coord/rework.tsv`. Its duplicate-filtration
import failure is already resolved by the current dependency migrations. The restored
archive compiles unchanged. This record documents restoration; no definition or
statement is repaired by weakening or changing it.

## Old

The active library has no file at
`lean/Sheaf/Paper/FlatFilteredComplexComparison.lean`. The preserved archive is
`quarantine/Sheaf/Paper/FlatFilteredComplexComparison.lean`; its theorem signature is:

```lean
theorem flatFilteredComplex_comparison
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Flat)
    (C : FilteredObject (CochainComplex (ModuleCat.{max u v w} A) ℤ))
    (D : FilteredObject (CochainComplex (ModuleCat.{max u v w} B) ℤ))
    (hCfin : C.filtration.IsFinite) (hDfin : D.filtration.IsFinite)
    (hC : ∃ N : ℤ, ∀ i : ℤ, i < N → IsZero (C.obj.X i))
    (hD : ∃ N : ℤ, ∀ i : ℤ, i < N → IsZero (D.obj.X i))
    (f : ModuleCat.filteredScalarObject.{u, v, w} φ C ⟶ D)
    (MA : FilteredPageTwoModel (ModuleCat.{max u v w} A))
    (MB : FilteredPageTwoModel (ModuleCat.{max u v w} B)) :
    ∃ (s : ∀ p : ℤ,
        (ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).obj
            (C.filtration.step p : CochainComplex (ModuleCat.{max u v w} A) ℤ) ≅
          ((ModuleCat.filteredScalarObject.{u, v, w} φ C).filtration.step p :
            CochainComplex (ModuleCat.{max u v w} B) ℤ))
      (g : ∀ (a b : ℤ) (hab : a ≤ b),
        (ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).obj
            (C.filtration.complexQuotient a b hab) ≅
          (ModuleCat.filteredScalarObject.{u, v, w} φ C).filtration.complexQuotient a b hab)
      (e : ∀ (r : ℤ) (hr : 2 ≤ r),
        (ModuleCat.filteredScalarComplex.{u, v, w} φ
            (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ))).obj ((MA.S.obj C).page r hr) ≅
          (MB.S.obj (ModuleCat.filteredScalarObject.{u, v, w} φ C)).page r hr),
      (∀ p : ℤ, (s p).hom ≫
          ((ModuleCat.filteredScalarObject.{u, v, w} φ C).filtration.step p).arrow =
        (ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).map
          (C.filtration.step p).arrow) ∧
      (∀ (a b : ℤ) (hab : a ≤ b), (ModuleCat.filteredScalarComplex.{u, v, w} φ (.up ℤ)).map
          (C.filtration.complexQuotientπ a b hab) ≫ (g a b hab).hom =
        (s a).hom ≫
          (ModuleCat.filteredScalarObject.{u, v, w} φ C).filtration.complexQuotientπ
            a b hab) ∧
      (∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (e r hr).hom.f (p, q) ≫
          (MB.pageIso (ModuleCat.filteredScalarObject.{u, v, w} φ C) p q r hr).hom ≫
          image.ι (HomologicalComplex.homologyMap
            (MB.φ (ModuleCat.filteredScalarObject.{u, v, w} φ C) p r hr) (p + q)) =
        (ModuleCat.filteredScalarFunctor.{u, v, w} φ).map
            ((MA.pageIso C p q r hr).hom ≫
              image.ι (HomologicalComplex.homologyMap (MA.φ C p r hr) (p + q))) ≫
          (ModuleCat.flatFilteredHomologyIso.{u, v, w} φ hφ
            (C.filtration.complexQuotient (p - r + 1) (p + 1) (by omega)) (p + q)).hom ≫
          HomologicalComplex.homologyMap (g (p - r + 1) (p + 1) (by omega)).hom (p + q)) ∧
      ((∀ p q : ℤ, IsIso ((e 2 le_rfl).hom.f (p, q) ≫ ((MB.S.map f).hom 2).f (p, q))) →
        ∀ n : ℤ, IsIso
          ((ModuleCat.flatFilteredHomologyIso.{u, v, w} φ hφ C.obj n).hom ≫
            HomologicalComplex.homologyMap f.hom n))
```

## New

Restore the archived module verbatim at its recorded Lean path. The signature above,
all imports, definitions, docstrings, and its one named theorem hole are identical.
The DAG attachment and mathematical dependencies remain unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FlatFilteredComplexComparison | H1 | Restored; compiles in 1.5 seconds. |
| No current direct or transitive Lean importers | none | No consumer needs adaptation. |
| WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar | not adapted | Its DAG node lem-pc-flat-base-change-cohom keeps this dependency; no Lean import to adapt. |

`tools/downstream.py` reports this absent active module as unknown. Searching both active
and quarantined sources for the module and declaration names finds no consumers. The
restored transitive import closure contains only the upstream filtration modules and no
`Sheaf.CategoryTheory.Filtration`.

No target statement or definition is changed, so no target statement review is reopened.

## Status

landed 20261020T174759-L-796003 2026-10-20 (merge of deliver/H1/Sheaf.Paper.FlatFilteredComplexComparison)
