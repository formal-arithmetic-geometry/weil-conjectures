## What changed

Proved `WeilConjectures.PurCompactSupport.scalarPull_coefficient_total_tensor` in
`Sheaf.Paper.ScalarPullCoefficientTotalTensor`. Its statement and public imports
are unchanged. Its only new proof import is
`Sheaf.Paper.ScalarPullCoefficientModuleTensor`, containing the proved ordinary
module square `scalarPull_coefficient_module_tensor`.

The module square is proved by transposing through scalar extension and geometric
pullback. The adjunction uniqueness identity shows that `scalarPullModule` takes
iterated unit sections to the units in the other order. The normalized scalar and
geometric tensor formulas then give the same tensor on both routes. The total
cochain equality follows by testing every total summand, using the inverse total
comparison formulas and naturality of the module comparison. Neither proof uses
flatness or boundedness, and neither permutes degrees. Identity changes and zero
rings, modules, or complexes require no separate nonzero assumption.

The new module privately imports the existing generator extensionality and
naturality proofs from `Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison`.
Concrete coefficient-site instances and reducibility attributes are local only.
No shared definition or existing public interface was changed.

The complete combined proof initially checked but exceeded 60 seconds. Profiling
identified large scalar-extension elaboration and generated reassociation helpers.
After making the relevant definitions locally irreducible and removing unused
reassociation declarations, the combined file still took 73 seconds. The ordinary
module argument was therefore extracted into its own proved module; no new hole
was introduced. Profiling the remaining total file identified repeated searches
for total-complex existence through unrelated single-complex instances. A proved
local tensor-total instance avoids those searches without changing any shared
definition or transparency setting. The final total file compiled in 46.4 seconds,
with no errors or warnings. Updated the DAG proof to match the two-module argument.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.PurCompactSupport.scalarPull_coefficient_total_tensor`
(node `lem-sf-scalar-pull-coefficient-total-tensor`).

Also proved the extracted ordinary module theorem
`WeilConjectures.PurCompactSupport.scalarPull_coefficient_module_tensor`
(node `lem-sf-scalar-pull-coefficient-module-tensor`).

Holes added: zero. Holes left in either delivered module: zero. All private helpers
are proved. This is a proof from existing declarations, not a decomposition into
new obligations; the existing dependencies retain their own proof status.

## No longer needed

No existing imports were removed. The proof does not use the generic coherence
result `lem-pur-cochain-pullback-tensor-coherence`
(`Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`) or the existential ordinary
comparison `lem-weil-pbc-ringed-topoi-module-pullback-tensor`
(`Sheaf.CategoryTheory.ModulePullbackTensorIso`) as direct proof dependencies.
Their planned uses are replaced by the normalized canonical tensor comparisons
already stated for the actual pro-etale functors, and the explicit total summand
calculation. Removed these two entries from this node's proof dependencies; no
claim is made that their modules have become globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The planned generator and summand argument is valid. The generic coherence API uses
a different scalar-extension presentation, so applying it here would additionally
require identifying that presentation and its comparison. The direct adjunction-unit
argument avoids that extra interface work and leaves the unit route intact.

## New nodes

`lem-sf-scalar-pull-coefficient-module-tensor` is the ordinary module step of the
original proof, now proved in `Sheaf.Paper.ScalarPullCoefficientModuleTensor`.
It has no cochain degrees, total coproducts or localization. Its complete proof
uses the adjunction unit identity and the two normalized ordinary tensor formulas.
This is a proved intermediate theorem, not a split-off sorry. No change record is
needed: only the assigned existing module, its node, and a new module/node change.

## Second reading by W8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
