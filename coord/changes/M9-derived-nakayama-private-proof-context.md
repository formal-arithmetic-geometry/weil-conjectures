# AlgebraicGeometry.ProEtale.DerivedNakayama.reduction_and_derived_nakayama

## Reason

The proof uses universe-polymorphic private helpers and a section of private
coefficient comparisons. The static interface check records universe declarations,
namespace openings and section variables as changed commands. Record their exact
scope and check the downstream users. No existing declaration signature, definition,
visibility or public import changes, and no target statement changes.

## Old

```lean
universe u
```

There was no `open HomologicalComplex` command and no `ReductionComparison` section
or section variables. The theorem's existing signature is unchanged verbatim.

## New

```lean
universe u v w w₁

open HomologicalComplex

section ReductionComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

-- Private coefficient-comparison definitions only.

end ReductionComparison
```

The extra universes parameterize only private generic helpers. The opening resolves
names in the explicit double-complex proof. The section variables parameterize only
private definitions and end before the existing public theorem. All private data are
constructed explicitly; none is chosen from an unproved existence statement.
The public theorem still binds exactly its original universe `u` and original
hypotheses and conclusion. These commands do not export new instances or attributes.

## Users

`tools/downstream.py Sheaf.Paper.DerivedNakayama --uses
AlgebraicGeometry.ProEtale.DerivedNakayama.reduction_and_derived_nakayama` lists
exactly the two downstream modules below. Neither mentions the theorem in Lean code;
their references are proof-dependency imports. The new helpers are private and cannot
enter either consumer's public signatures or definitions.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DerivedNakayama | M9 | Its original theorem is proved; original signature and public imports unchanged. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | No adaptation: no use of the changed private proof context; existing declarations unchanged. |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | P3 | No adaptation: no use of the changed private proof context; existing declarations unchanged. |

## Status

landed 20261019T231247-L-566916 2026-10-19 (merge of deliver/M9/Sheaf.Paper.DerivedNakayama)
