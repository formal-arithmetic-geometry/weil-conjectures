## What changed

Replaced the proof of `WeilConjectures.completedTensor_map_smul_left` in
`Sheaf.Paper.CompletedTensorScalarLinearity`. Its signature and public imports are
unchanged. Private helpers construct the sectionwise scalar action, prove finite
reduction and sheaf tensor linearity, pass through total complexes and the Roos
construction, identify derived localization with the published scalar action,
and transport the normalized descent comparison along K-flat representatives.
The final argument factors a general pair of maps through a scalar identity.

Added private proof imports for independent-universe tensor functoriality,
bifunctor linearity, global-section actions, concrete limits and functor-category
linearity. Updated the existing node's proof and dependencies to describe these
steps, citing the current constant-scalar construction ownership node.
No other library module is changed. Added change record
`coord/changes/E7-completed-tensor-proof-scopes.md` for proof-local commands and
local scalar instances, as required by preflight.

## Proved and sorry left

Closed `WeilConjectures.completedTensor_map_smul_left`
(blueprint `lem-coef-completed-tensor-scalar-linearity`), the item's only hole,
from the existing library declarations. Holes closed: 1; holes added: 0; holes
left in the item: 0. No split-off statements are added. The existing dependency
statements retain their existing proof status. An earlier complete version passed
`lcompile.py` with exit code 0 in 37.2 seconds and no warnings. A subsequent
delivery compile saw the synchronized equality-characterized derived scalar
action; the localization helper now explicitly uses its equality specification.
The required delivery tool validates the final version and performs axiom checks
and preflight.

## No longer needed

None of the original declared dependencies is pruned. All three are used by the
proof. No existing module or declaration is withdrawn. Exploratory private
imports of `Sheaf.Paper.ResolvingRepresentativeWhiskering`,
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Linear` and
`Mathlib.CategoryTheory.Center.Linear` were removed from the working draft;
they were not imports of the original module and imply no DAG pruning.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or definition was changed or disputed. The proof
requires explicit compatibility with the chosen constant-section action on the
derived category; it cannot assume an arbitrary inferred linear structure is
that action. The finite total tensor is an uncurried bifunctor, whose map is a
composite. The resolution theorem's flatness clause uses monoidal tensor, so
its comparison with site tensor is needed to inhabit the good-complex
subcategory. The proof handles zero scalars and arbitrary torsion objects
without cancellation of scalars or any extra hypothesis. During validation the
shared scalar-action definition changed to a choice from its equality
characterization. The proof explicitly identifies that choice with the canonical
localization lift and makes no definition change.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
