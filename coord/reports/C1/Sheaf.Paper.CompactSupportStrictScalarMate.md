## What changed

Reduced WeilConjectures.PurStrictScalar.compactSupportStrictScalarMate to its exact
finite-evaluation identity. Its proof now obtains the strict and finite proper/open
isomorphisms from factors_isIso, composes and whiskers them to prove strict arrow
invertibility, proves finiteTensorMap invertibility by its two factors, and uses
pbcTowerTransition.naturality for every quotient-transition square. The remaining
finite-evaluation equation is stated independently as strictScalarMate_finiteEvaluation.

Relocated the already proved constructions from subsequence_preservesKInjective through
targetEvaluation into Sheaf.Paper.StrictScalarMateEvaluationData, preserving their names,
signatures, universes, visibility, instances and bodies exactly (apart from blueprint tags).
The original module publicly reexports the data. This extraction prevents an import cycle
between the independent finite-evaluation item and the final conjunction; it is not a
compile-time split. The new theorem is in Sheaf.Paper.StrictScalarMateFiniteEvaluation.
Change record: coord/changes/C1-strict-scalar-mate-evaluation-data.md.

All three modules compiled through lcompile.py --all. The final proof no longer uses
its automatically included geometric hypotheses; they remain in the theorem signature
unchanged. A declaration-scoped linter.unusedSectionVars option suppresses this warning
without omitting any binder. The delivered Lean contains no profiling options.

The final theorem's signature and its conclusion abbreviation are unchanged. The new
lemma asserts only Step 7; it has no invertibility or transition conclusion and is strictly
part of the original conjunction. Its argument applies to every derived input. Edge cases
were checked in the source argument: e=1, n=0 (both exponents positive), the zero input,
and identity or empty open compactifications. No equality in the strict derived diagram
category is inferred from equality of evaluations.

## Proved and sorry left

Closed one of the four original holes:
WeilConjectures.PurStrictScalar.compactSupportStrictScalarMate
(node lem-pur-compact-support-strict-scalar-mate). This is a decomposition, not a net
proof: one strictly smaller hole is added, so the delivery's net hole reduction is zero.
The new data module has zero holes and introduces no hollow definitions.

The three unchanged original holes, all on lem-pur-compact-support-strict-scalar-mate:

- WeilConjectures.PurStrictScalar.pulledBasis_existsUnique.
- WeilConjectures.PurStrictScalar.proper_biproduct.
- WeilConjectures.PurStrictScalar.strictProper_biproduct.

The single added hole:
WeilConjectures.PurStrictScalar.strictScalarMate_finiteEvaluation
(node lem-pur-strict-scalar-mate-finite-evaluation). It has a complete source argument in
its docstring and node. It asks only for evaluation of the prescribed arrow, with every
endpoint comparison fixed by the unchanged data constructions.

## No longer needed

No mathematical dependency or existing module is pruned. The original unit route and all
three basis/biproduct obligations remain. The data extraction does not remove any theorem
or definition. Removed the original module's private imports of
Sheaf.Paper.FiniteQuotientModuleBalancing and
WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp: their only uses
were in the constructions now owned by the data module, which retains those imports.
Removed three unused private imports from the new data module:
Sheaf.Paper.CompletedIntegralFiniteFree,
Sheaf.CategoryTheory.ConstantFiniteFreeSectionBasis, and
Sheaf.CategoryTheory.AdicBasisLimit. They remain in the original module for its finite
basis invertibility proof. No module or DAG dependency is declared unnecessary on this
basis, since those constructions are still used elsewhere in the delivery.

## Where the brief, the DAG or earlier work was wrong

The remaining final sorry bundled an already available invertibility argument and a pure
naturality argument with the outstanding finite-arrow normalization. These can be proved
and separated without changing any statement. An independent Step-7 module cannot import
the original module containing its own consumer, hence the shared data extraction.
No false statement, tool workaround or source-library alteration is involved.

## New nodes

- def-pur-strict-scalar-mate-evaluation-data records the unchanged canonical arrow and
  source/target evaluation constructions, with their existing proved normalization lemmas.
  Their Lean attachments move here; no new assertion or hole is introduced.
- lem-pur-strict-scalar-mate-finite-evaluation is exactly Step 7: evaluation of the actual
  strict scalar arrow, under the prescribed comparisons, equals the finite proper/open
  mate. Invertibility and quotient-transition clauses are proved in the consumer.

Change record: coord/changes/C1-strict-scalar-mate-evaluation-data.md.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
