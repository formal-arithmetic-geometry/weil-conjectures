## What changed

Proved `WeilConjectures.sfConstructibleIntegralScalarExtension_smul` in
`Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`. The proof specializes the
integer-linearity clause of `integralScalarExtensionWellDefined` to the underlying
objects and morphism of the full subcategory. The restricted object and morphism maps
reduce definitionally to the ambient maps. All existing signatures, definitions,
docstrings and imports match the current source. Six proof-dependency imports added
to the shared source during this session were restored to the retained sandbox.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.sfConstructibleIntegralScalarExtension_smul`
(node `lem-weil-integral-scalar-extension-constructible`).

One original hole remains, unchanged:
`WeilConjectures.sfIntegralScalarExtension_constructible`
(node `lem-weil-integral-scalar-extension-constructible`). Its complete existing
docstring records the residue-field, quotient-filtration and normalized-effectivity
argument. No new holes or split-off statements are added. The closed linearity proof
still transitively depends on the original constructibility theorem through the
restricted functor and on the ambient well-definedness theorem; it is not claimed
axiom-free independently of those dependencies.

## No longer needed

None. The ambient well-definedness import is used by the linearity proof. The other
imports still record the unfinished constructibility argument and are retained.
The exploratory private good-model helper and its extra tensor-comparison import
from the retained sandbox are not part of this delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt reported an exploratory good-model helper with unresolved
essentially-small universe constraints; it was already absent from the retained
sandbox at this restart. This delivery retains the compiled direct linearity proof.
The main constructibility hole is left in place, as permitted for a module with
several holes. No claim is made to have formalized its normalization or filtration
steps. The three dependencies extracted by the current DAG now have source modules:
`Sheaf.Paper.FiniteFieldSheafScalarExtension`,
`Sheaf.Paper.FilteredCoefficientTensorBounds`, and
`Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison`. None directly states the
missing normalized-tower construction or the comparison from effectivity's
`IsDerivedComplete` to `IsSfDerivedComplete`. The existing main theorem remains
unchanged. The searched first-reduction criterion in
`Sheaf.Paper.IntegralCriterionReductions` requires a Noetherian scheme; this
item permits arbitrary schemes, so that criterion was not imported. The
finite-free completed scalar comparison supplies completeness in a different
presentation, leaving a comparison of the canonical augmented reduction towers.

Revalidation in this resumed session: the first `lcompile.py` call returned no
answer from the compile server within 193 seconds (exit 124, not a Lean timeout).
The required retry compiled the retained module successfully in 3.2 seconds with
exit code 0. After restoring the six current proof-dependency imports, the exact
delivery module compiled again in 2.7 seconds, exit code 0. A source diff confirms
that the only Lean change is the completed linearity proof. The first resumed
dry run waited for worktree capacity and shared fetch, then exited with code 137
without producing preflight results. The second dry run waited for worktree
capacity and then crashed before preflight:
`sharedrepo.py:202` raised `subprocess.TimeoutExpired` because its internal
`git checkout -q --detach origin/sheaf-dag` exceeded 600 seconds. A third required
dry-run attempt is being made. No launcher script, shared cache or lock file was
modified.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
