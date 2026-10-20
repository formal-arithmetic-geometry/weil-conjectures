## What changed

Retired the duplicate Sheaf.RingTheory.CyclicExtensionFlatDescent under its row in
coord/retire-items.tsv and the human authorization of 2026-10-20. Its sole direct
consumer, Sheaf.RingTheory.TorsionExtensionFlatDescent, now privately imports
WeilConjectures.RingTheory.CyclicExtensionFlatDescent at line 11. No proof changes
are necessary: the cyclic theorem is applied positionally. The old and official
signatures agree exactly after removing underscore prefixes on six hypothesis
binder names. Universes, hypotheses and both commuting identities are identical.

Updated only the lean attachment of lem-weil-pbc-cyclic-extension-flat-descent to
the official module and its verbatim signature. The node's proof, proof dependencies,
source, statement and unit route are unchanged. No source-library file is edited.
Change record: coord/changes/B4-retire-cyclic-extension-flat-descent.md.

Validation: the adapted consumer compiles cleanly through lcompile.py (6.3 s).
The upstream theorem's axiom probe reports exactly propext, Classical.choice and
Quot.sound. A recursive source-import comparison shows that the consumer closure
loses exactly Sheaf.RingTheory.CyclicExtensionFlatDescent and gains exactly its
WeilConjectures twin. The resulting closure contains no Sheaf/upstream twin pair.
Searches through msearch.py (LeanFinder, Loogle, grep) were recorded; direct source
search found the existing complete official theorem, which is used unchanged.

## Proved and sorry left

The assigned module has zero textual sorry before this delivery and is withdrawn.
No holes closed; no holes added; no holes split off. The official replacement
LinearMap.exists_cyclic_extension_flat_descent is fully proved with only the three
allowed axioms. Its consumer LinearMap.exists_torsion_extension_flat_descent stays
fully proved and has zero sorry. This delivery is retirement, not new proof progress.

## No longer needed

Withdraw lean/Sheaf/RingTheory/CyclicExtensionFlatDescent.lean via deleted.txt.
Remove its private import from Sheaf.RingTheory.TorsionExtensionFlatDescent and
replace it with the official module import. No DAG node or mathematical dependency
is pruned: the existing cyclic-descent node and all its uses remain, now attached
to the official proof. No other module is withdrawn and no other import is removed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an unfinished theorem, but the current assigned
item is a zero-hole retirement in coord/retire-items.tsv. The DIFFERENT API label
only reflects underscore prefixes on hypothesis names; the sole consumer does not
use named hypothesis arguments. The prerequisite IdealPowerHomLift retirement
has already landed, so its official dependency is consistently used on both routes.
No mathematical statement, proof plan or unit step was wrong or changed.

## Forced adaptations

Sheaf.RingTheory.TorsionExtensionFlatDescent is held by C2. Its only changed line
is line 11, replacing the private import of the withdrawn copy with its official
replacement. All signatures, public imports and proof text remain identical.
The original consumer was compiled with an empty retired module in an isolated
scratch overlay: at line 150:8 it reports
`error(lean.unknownIdentifier): Unknown identifier exists_cyclic_extension_flat_descent`.
The adapted consumer compiles cleanly. The retirement thus forces this import edit.

## Forced adaptations

### Sheaf.RingTheory.TorsionExtensionFlatDescent
Original imports module(s) explicitly withdrawn in deleted.txt: Sheaf.RingTheory.CyclicExtensionFlatDescent. Those imports must be migrated in this delivery; the baseline's compiled copies are not valid counterfactual dependencies. Adapted module compiled in the delivered set. CODEX verifies the migration and every accompanying API adaptation is needed.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
