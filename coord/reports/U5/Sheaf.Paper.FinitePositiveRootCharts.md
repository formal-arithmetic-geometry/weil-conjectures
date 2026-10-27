## What changed

Proved `WeilConjectures.PurityFiniteSetting.existsUnique_finiteTensorFirstSheafChart`
in `Sheaf.Paper.FinitePositiveRootCharts`. A proved private helper lifts an arbitrary
single-to-derived-unit isomorphism through the fully faithful degree-zero single
functor. It first cancels the native unit comparison, uses `Functor.preimageIso`,
and then proves normalization and uniqueness using `Functor.mapIso_injective`.
Added the proof-only import `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`.
The existing statements, definitions, public imports and docstrings are unchanged.

The source plan already calls for exactly this full-faithfulness argument; there
is no new route, statement or node. LeanFinder found `Functor.preimageIso` and
`Functor.FullyFaithful.isoEquiv`; the source of Mathlib's derived fully faithful
instances and functor isomorphism API was read. Loogle did not recognize the
short name `Functor.mapIso_injective`; the installed source contains it.

Validation: lcompile.py compiled the changed module successfully in 33.7 seconds.

## Proved and sorry left

Closed one of the original two holes:
`WeilConjectures.PurityFiniteSetting.existsUnique_finiteTensorFirstSheafChart`.
The new private theorem `singleUnitChart_existsUnique` is completely proved.
No holes were added or split off.

One original hole remains unchanged:
`WeilConjectures.PurityFiniteSetting.existsUnique_finiteTensorSheafCharts`
(node `def-pur-finite-positive-root-charts`). Its ordinary positive-power
construction and local basis normalization still need proof. In particular,
faithfulness of the single functor alone does not prove the local section
normalization or uniqueness of this family. This is a partial proof delivery,
not a decomposition of that remaining theorem.

## No longer needed

None. No imports, nodes or modules are pruned. The local ordered-basis machinery
is still used in the statement of the remaining positive-family theorem.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The node has no numbered proof steps, but
the first theorem's docstring supplies the fully faithful lifting argument;
the Lean proof implements that argument without adding any assumptions.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
