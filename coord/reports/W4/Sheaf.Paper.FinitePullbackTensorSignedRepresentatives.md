## What changed

Proved `WeilConjectures.finitePullbackTensor_signed_representatives` without changing
its statement. Its sole new proof import is
`Sheaf.Paper.ProEtaleSignedTensorPullbackTotal`, which proves the ordinary signed
chain square for arbitrary commutative-ring sheaves and arbitrary unbounded complexes.
The ordinary square is checked on adjunction-unit tensor sections, then on total
summands using the existing native Koszul braiding formula. The item applies the
canonical representative normalization on both orderings, cancels the representative
and factorization isomorphisms, and transports the result through the specified
finite tensor-model and realization isomorphisms. All helper definitions in the item
are private and explicit constructions; no shared interface was changed.

Validation: the new chain module compiled cleanly in 52.0 seconds. The final item
compiled cleanly in 49.1 seconds, with profiling removed and strict transparency
retained. The existing theorem signature is textually identical to the current
source. Both node proof-dependency lists equal the unions of their proof-step uses.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.finitePullbackTensor_signed_representatives`
(`lem-pur-finite-pullback-tensor-signed-representatives`).

Also proved `WeilConjectures.proEtaleSignedTensorPullbackTotal`
(`lem-pur-proetale-signed-tensor-pullback-total`). No holes added, no split-off
obligations, and no `sorry` left in either delivered module. The proof uses the
existing canonical tensor-pullback theorem as intended by stage 3.

## No longer needed

No original imports removed and no modules withdrawn. The direct use of
`lem-sf-ringed-tensor-complex-constraints` in the old plan is replaced by the proved
ordinary signed-total calculation: the native summand formula
`CochainComplex.Monoidal.ι_braiding_hom` and the existing module pure-tensor braiding
formula suffice. The constraints module remains a transitive dependency of the
unchanged braiding construction, so no whole-library pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The item and construction were initially absent from the live Lean tree but preserved
in quarantine and listed in `coord/rework.tsv`. The live tree restored both while the
session was reading dependencies; this delivery preserves their current statements,
Lean attachments and mathematical route. The old representative proof was a correct
plan. No mathematical statement or unit route required repair. Integer degrees,
including negative degrees, are handled by the native integer sign formula; the
chain calculation needs neither flatness nor K-flatness. Those hypotheses are used
only when applying the existing derived representative normalization. Zero complexes
and the identity pullback introduce no exceptional case.

## New nodes

`lem-pur-proetale-signed-tensor-pullback-total` records the ordinary chain-square
calculation before localization. Source: Stacks 07A4, its final total comparison,
03EL ordinary tensor pullback, and 0FNG Koszul exchange. LeanSearch, LeanFinder and
grep found generic categorical braiding results but no theorem for the selected
normalized pro-etale total comparison. The new module proves the result, with no
remaining proof obligation. The blueprint source is inherited from the item's
explicit `blueprint.from` record because the ancestor helper cannot resolve its
module-valued historical `created.item`. No change record is needed: the only
existing module changed is the item and its exported signatures are identical.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
