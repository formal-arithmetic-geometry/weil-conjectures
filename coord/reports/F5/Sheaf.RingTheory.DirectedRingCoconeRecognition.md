## What changed

Proved `CommRingCat.directed_cocone_recognition` in
`Sheaf.RingTheory.DirectedRingCoconeRecognition`, without changing its statement,
public imports, or visibility. Added the private proof import
`Mathlib.Algebra.Category.Ring.FilteredColimits`.

A proved private construction applies
`Types.FilteredColimit.isColimitOf'` to the underlying set cocone and reflects
that colimit back to commutative rings. The forgetful functors preserve filtered
colimits, giving the additive and set claims. A proved private lemma establishes
comparison-map naturality in any category by coprojection extensionality; the
main proof applies it in all three categories. The DAG node's proof and
proof_origin now record this route, with the same proof_deps.

Validation: the server single-file compile passed cleanly (9.3 seconds).
The argument permits zero rings and noninjective transitions; it uses precisely
the stated nonempty directed preorder assumptions and also applies to singleton
indices. There are no new public declarations or changed definitions.

## Proved and sorry left

Closed: `CommRingCat.directed_cocone_recognition` (1 of 1 original holes).
Added: none. Remaining: none. Split off: none.
Both private helpers are completely proved from Mathlib.

## No longer needed

No imports removed, and no dependency nodes or modules withdrawn.
`def-weil-pbc-category-colimit` remains the only DAG proof dependency.
The explicit representative-choice construction and separate checks of addition,
multiplication, zero, and one in the old plan are supplied by Mathlib's set
recognition and filtered-colimit reflection/preservation results. They require
no additional Sheaf modules or new nodes. The blueprint unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or definition was found. The earlier search correctly
identified the set recognition criterion but did not exploit reflection and
preservation to obtain the ring and additive claims immediately. Those Mathlib
results give a shorter implementation of the same universal properties.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
