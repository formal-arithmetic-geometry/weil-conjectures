## What changed

Retired lean/Sheaf/Algebra/Homology/FlatTruncationSuccessor.lean in favor of the
proved upstream WeilConjectures.Algebra.Homology.FlatTruncationSuccessor.
Reattached lem-pc-flat-truncation-successor to the existing upstream declaration,
recorded its verbatim stronger signature, and updated the proof description to
reflect internally supplied flat covers. The source theorem and all target
statements remain unchanged. Change record:
coord/changes/W3-retire-flat-truncation-successor.md.

The retirement row's former consumer Sheaf.Algebra.Homology.FlatTruncationTower
is already absent. Its retained upstream version already imports and applies the
upstream successor, so no consumer adaptations are needed. Searches of lean/
and coord/rework.tsv found no remaining importer or quarantined consumer.

## Proved and sorry left

The original item has zero sorry holes. Closed: 0; added: 0; split off: 0.
No sorry remains in the retired item and no declaration is left unfinished.
CochainComplex.exists_flat_truncation_successor remains proved in the upstream
library. A scratch theorem with the original conditional signature proves it from
the upstream theorem, and the successor and tower are checked with #print axioms.
This is a module retirement, not a newly closed proof hole.

## No longer needed

Pruned Sheaf.Algebra.Homology.FlatTruncationSuccessor (the duplicate module).
Its five public imports and three private proof imports disappear with the
retired file. Their upstream equivalents remain in the official source module.
No mathematical node or proof dependency is pruned: bounded flat replacement,
relative flat extension, and flat augmentation epicification are all used by the
preserved source proof. The successor node and the tower parent's dependency on
it remain, so the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief described an open proof obligation, but the current
item has zero holes and is explicitly listed for retirement. The upstream twin
already proves a stronger theorem, omitting hcover, hquasi, and hepi. The
retirement inventory's consumer column predates the tower's retirement: the
current tower already uses the official source theorem. The DAG attachment and
its third proof step still described the duplicate's redundant hypotheses;
this packet reconciles those records with the actual source proof.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
