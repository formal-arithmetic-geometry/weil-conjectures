## What changed

Completed the listed retirement of
`Sheaf.AlgebraicGeometry.EtaleGlobalSectionsGaloisImage` in favor of the existing
`WeilConjectures.AlgebraicGeometry.EtaleGlobalSectionsGaloisImage` theorem
`AlgebraicGeometry.Scheme.etaleGlobalSections_galoisInvariants_image`.
The duplicate module is withdrawn using deleted.txt. Its sole direct consumer,
`Sheaf.AlgebraicGeometry.EtaleGlobalSectionsGaloisInvariants`, changes only its
private import on line 13. Its declaration signature, proof, and public imports
remain unchanged. No adopted source module is edited.

Updated only the Lean attachment of `aux-etale-global-sections-image`: it now
records the existing upstream module, path, and verbatim signature. The old and
upstream types differ only in whether the nondependent action-compatibility proof
binders are named or written as implications. A scratch example with the exact
old signature compiles by applying the upstream theorem directly. Its axiom probe
reports only `propext`, `Classical.choice`, and `Quot.sound`.

The original item and the adapted consumer both compile without errors or warnings
using lcompile.py. import_direction.py confirms that the replacement import creates
no cycle. The change record is
`coord/changes/S2-retire-etale-global-sections-galois-image.md`.

## Proved and sorry left

This is a retirement, with zero original holes. Closed 0 of 0 holes; added 0 holes;
split off 0 statements. No sorry remains or is introduced in any delivered module.
The preserved upstream theorem is fully proved with only the three permitted
axioms, as checked by `#print axioms`.

## No longer needed

Pruned the duplicate module
`Sheaf.AlgebraicGeometry.EtaleGlobalSectionsGaloisImage` and replaced its sole
consumer import by the upstream theorem's module. No dependency node is pruned:
`aux-etale-global-sections-image` is still needed by its parent and retains its
mathematical statement, proof, and proof dependencies. Its theorem is supplied by
the adopted upstream module. The selected-lift reconstruction and Galois
extension dependencies remain used by that proof and are not claimed as pruned.

All five transitive consumers are enumerated in the change record. The parent
node keeps its dependency on this node; no unfinished or quarantined parent is
left without a declaration. No unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item with holes, but coord/queue.tsv and
coord/retire-items.tsv specifically classify this item as a retirement. The current
Sheaf theorem was already proved by F1 and its adopted upstream twin proves the
same statement. The required work is duplicate removal and consumer migration,
not closing a further hole or handing off another reconstruction obligation.

Read the Stacks source at lemma-global-sections-point (Tag 04JM), the item node,
its selected-lift dependency, and unit sk-thm-br. The mathematical proof route
remains unchanged. LeanFinder returned related Galois and structure-sheaf lemmas;
Loogle returned the invariants API. Direct rg searches found the exact adopted
upstream theorem and its unique direct Sheaf consumer. No new lemma or node was
needed. The source-library boundary is respected: no upstream declaration,
public import, proof, or non-theorem body is changed.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
