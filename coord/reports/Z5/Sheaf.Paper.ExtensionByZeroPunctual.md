## What changed

Proved `WeilConjectures.zlOpenWeilPull_isRightAdjoint` with its signature unchanged.
The proof uses the existing exact common-stage open-heart adjunction, the existing
Frobenius heart square, and invertibility of its inverse mate under Frobenius
autoequivalences. Explicit private functors identify the existing Weil heart with
invertible algebras over the Frobenius functor of the underlying heart. Transporting
the lifted adjunction across this equivalence gives the specified `zlWeilPull`.
The Frobenius autoequivalence argument uses the existing isomorphism-field-transport
and constructible-pullback declarations. No public definition or signature changes.
All added imports are private proof imports. A complete sandbox compile passed
in 45.9 seconds; the delivery checks compile the final cleaned version again. The local irreducibility annotation
for the two large pullback definitions is moved before the new proof, avoiding
expensive unfolding while preserving the existing annotation for later proofs.
The private Frobenius-equivalence proof follows the already proved private
`zlHeartFrobenius_equiv` in `Sheaf.Paper.WeilIndSheafCategory`.
The node gains an auxiliary-proof step and the six existing nodes used by it;
its six main-theorem steps and their dependencies are preserved.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.zlOpenWeilPull_isRightAdjoint`.
No holes added and no split-off statements.
The remaining original hole is `WeilConjectures.extensionByZero_punctual`
(node `lem-zl-extension-by-zero-punctual`), unchanged.
The private constructors and private Frobenius-equivalence lemma have complete proofs.

## No longer needed

No original imports, nodes or modules are pruned in this partial delivery.
The remaining main theorem retains its original proof plan and dependencies.
For the adjunction hole specifically, the exact common-stage heart adjunction is
sufficient: the coefficient-stage t-exactness package and open-Weil-unit package
are not imported by this proof. Their work remains needed by the main theorem.

## Where the brief, the DAG or earlier work was wrong

`ZlOpenUnit.openWeilUnitAndEmptyFibre` takes its coefficient closure in `Type u`,
whereas this item's closure is in independently quantified `Type v`. Thus that
interface cannot directly supply the adjunction at the item's full generality.
The existing common-stage heart adjunction has the required independent universes;
we lift it using the recorded Frobenius square instead. No statement is weakened.
The newly referenced adjunction-lifting, inverse-mate, isomorphism-transport and
pullback-heart results are general tools: they prove the equivariant-adjunction
part of blueprint proof (1), rather than substituting a different unit's theorem
for the unit's own route. None of their DAG dependency closures reaches this item.
The empty open, identity immersion and zero objects require no separate argument:
the equivalence of Weil-heart presentations and the adjunction transport apply to
them without nonemptiness assumptions.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
