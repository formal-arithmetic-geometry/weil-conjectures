## What changed

Proved `AlgebraicGeometry.finite_hypercover_descent_morphisms` and
`AlgebraicGeometry.finite_hypercover_descent_equalities` in the item module, with unchanged
signatures. Private proved helpers establish qcqs simplicial terms from their finite cofans,
lift a finite family of maps, and descend a finite family of equalities over a general
filtered index category. The final morphism comparison is checked by both pullback projections.
Updated the two corresponding DAG proof plans and dependencies.

Validation: the final single-file compile succeeded without warnings;
`deliver3.py K4 Sheaf.Paper.FiniteHypercoverDescentParts --no-push` printed OK,
including the preflight and declaration-axiom probe. Nothing was pushed. The second
reading is reserved for the independent reader.

## Proved and sorry left

Closed two original holes:
- `AlgebraicGeometry.finite_hypercover_descent_morphisms`
  (`lemma-weil-pbc-finite-hypercover-descent-morphisms`).
- `AlgebraicGeometry.finite_hypercover_descent_equalities`
  (`lemma-weil-pbc-finite-hypercover-descent-equalities`).

The original hole `AlgebraicGeometry.finite_hypercover_descent_objects`
(`lemma-weil-pbc-finite-hypercover-descent-objects`) remains unchanged. No holes were added;
no decomposition is claimed. No public statement or definition changed.

## No longer needed

Removed the proof import `Sheaf.Paper.EtaleFiniteDataDescent`. The two completed clauses use
01ZM directly and finite coproduct qcqs permanence, rather than its larger five-clause theorem.
For these clauses `lem-weil-pbc-etale-finite-data-descent` is no longer a proof dependency.
Its object/covering theory is still part of the unfinished object's plan; no claim is made
that it is globally unnecessary. No other original imports or nodes were pruned.

## Where the brief, the DAG or earlier work was wrong

The planned dependency `etale_finite_data_descent` currently assumes a directed preorder,
whereas the item allows an arbitrary small filtered category. The finite common-stage helpers
here work directly for that more general category, using `IsCofiltered.wideCospan` and the
existing general-category 01ZM declarations. No hypothesis was changed.

There is also an upstream `WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts`
module with the same three declaration names and three unproved statements. It supplies no
proved shortcut and was not imported or modified. This overlap should be reconciled by the
maintainer's upstream process.

Searches: LeanFinder found the general affine-transition-limit map/equality descent API;
Loogle did not know the project-specific 01ZM declaration; the repository and Mathlib searches
found the finite-cofan and pullback APIs used here. The unit record `sk-prop-h2` has no realized
statement or proof step assigned to these nodes; the unit route is unchanged.

## Second reading by K4

1. **Signatures and accidental changes.** Compared the delivered module with the repository
version. The three public theorem signatures are byte-for-byte unchanged; only proof bodies,
proof-only imports, and the two DAG proof plans/dependency lists changed. Verdict: pass.

2. **Proof and axioms.** Compiled the delivered module with `lcompile.py`; it succeeds without
errors or warnings. The two completed declarations contain no `sorry`, and the only remaining
`sorry` is `finite_hypercover_descent_objects`, the original named hole. The proof uses the
existing 01ZM limit descent declarations and categorical pullback extensionality; no forbidden
axioms, definitions with `sorry`, `axiom`, `unsafe`, `opaque`, or `extern` were introduced.
Verdict: pass.

3. **Statements and split claims.** No new public statement was split off. The two existing
node statements are realized exactly by the unchanged theorem types, and the finite-family
helpers are private proof reductions rather than alternate restatements. Searches recorded in
the nodes found no prior declaration of either theorem. Verdict: pass.

4. **Route and pruning.** The proof keeps the finite-hypercover unit route: finite coproduct
qcqs permanence followed by 01ZM (2)/(3) finite morphism and equality descent, with canonical
pullback comparison. The former `Sheaf.Paper.EtaleFiniteDataDescent` import and its node are no
longer used by these two clauses; all remaining imports are used by the proof. Verdict: pass.

5. **DAG agreement.** The morphism and equality node `proof`, `proof_deps`, and
`proof_origin` fields now describe the implemented finite-presentation and common-stage route;
the unit record and theorem statements were not changed. Verdict: pass.

I changed only the report after this reading; no Lean proof or public interface required repair.
