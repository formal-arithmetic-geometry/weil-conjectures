# AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck.isIso_colimit_comparison_positive

## Reason

The completed proof adds private helpers and commands scoping their parameters:
an extra `open CategoryTheory.Preadditive`, a `section Staircase` with
`variable {A}`, and `omit ... in` commands on individual private lemmas. The
interface checker records non-declaration commands textually, including these
commands affecting only the new proofs, and requires this record. The public
theorem's name, signature, visibility, coefficient category, and meaning are
unchanged. No public definition is changed and no target review is reopened.

The additional AB5 instance is a `let` inside the private colimit-monicity proof.
The two new isomorphism/quasi-isomorphism helpers are private lemmas, with their
instances introduced inside the definitions and proofs that need them.

## Old

The existing public signature, verbatim:

```lean
theorem isIso_colimit_comparison_positive (F : Sheaf X.smallEtaleTopology A) (q : ℕ) :
    IsIso (colimit.desc (homotopyCohomologyDiagram A F (q + 1))
      (comparisonCocone A F (q + 1)))
```

The file opened these namespaces:

```lean
open CategoryTheory CategoryTheory.Limits Opposite
```

It had no private staircase helper section or private-lemma `omit` scopes.

## New

The public signature remains, verbatim:

```lean
theorem isIso_colimit_comparison_positive (F : Sheaf X.smallEtaleTopology A) (q : ℕ) :
    IsIso (colimit.desc (homotopyCohomologyDiagram A F (q + 1))
      (comparisonCocone A F (q + 1)))
```

The namespace-opening command is now:

```lean
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Preadditive
```

The private helper section starts with these commands:

```lean
section Staircase
variable {A}
```

It ends before `mono_homology_one`; the original explicit `A` binding is
therefore in force at the public theorem. Individual `omit` commands remove
unused class parameters only from private helper signatures. These scopes do
not change any existing declaration's signature or any exported definition.

## Users

The read-only command
`tools/downstream.py Sheaf.AlgebraicGeometry.GrothendieckHypercoverBottomColimit --uses isIso_colimit_comparison_positive`
found the following two textual users of the declaration, including its own
module. None needs adaptation. The 165 modules in the transitive import closure
continue to see the identical public theorem and public imports.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GrothendieckHypercoverBottomColimit | C2 | Own proof completed; public signature unchanged. |
| Sheaf.AlgebraicGeometry.GrothendieckHypercoverComparison | unclaimed | Existing application has the identical type; no adaptation. |

The earlier preflight also mentioned
`WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic` because it
contains a similarly spelled local AB5 instance. That additional file-local
instance was removed from the delivery in favor of a proof-local `let`; this
module is not adapted.

## Status

landed 20261016T062622-L-449034 2026-10-16 (merge of deliver/C2/Sheaf.AlgebraicGeometry.GrothendieckHypercoverBottomColimit)
