## What changed

Proved `WeilConjectures.compactSupportQuotient_raw_input` with its original
signature and public import unchanged. Private reflexivity lemmas identify the
native wrappers with the original constructions. Private lemmas proved by
equality induction transport functor objects, comparison components and
composites using heterogeneous equality, including the category structures and
intermediate objects. Equality of the resulting equation propositions transports
`hi.1` and `hi.2` to precisely the required identity and composition laws.

The heterogeneous transport avoids expensive kernel reduction of the equality
casts inside the quotient comparison isomorphisms. Local reducibility attributes
help elaborate the existing coefficient aliases; no exported attributes change.
No definitions or dependency modules change, and no objects or witnesses are
introduced. The item node records this proof route. The final module compiles without
warnings in 5.7 seconds against the published library.

## Proved and sorry left

Closed `WeilConjectures.compactSupportQuotient_raw_input`
(node `lem-coef-compact-support-quotient-raw-input`): 1 of 1 holes.
No holes remain in the item and no holes are added. Every private helper is
proved. This is a proof, with no split-off obligations or new modules.

## No longer needed

Removed `lem-coef-compact-support-quotient-input-laws`
(module `Sheaf.Paper.CompactSupportQuotientInputLaws`) from this item's proof
dependencies: its equations are already the hypothesis `hi`. That module is
still needed by the parent cocycle proof and is not withdrawn.

No Lean imports are removed and no module is pruned. The native wrappers and
coefficient restriction presentation remain needed. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof listed the input-laws theorem as a proof dependency,
although this presentation transport already assumes those laws. It needs the
hypothesis, not another application of that theorem.

A direct definitional conversion is mathematically sufficient, but kernel
comparison of components evaluated at definitionally equal objects unfolds large
quotient casts. Equality induction with heterogeneous hom types avoids that cost
without changing any construction or statement. The argument also applies at
level zero and at equality of indices: it changes only the presentation of the
same data and uses exactly the supplied inequalities.

The shared snapshot listed a proof item with one hole and no repair or quarantine
row. Library searches found the wrapper definitions and the parent cocycle use.
LeanFinder returned generic functor equality transport lemmas; Loogle found the
core identity function; Mathlib grep found no project-specific declaration.
No external lemma from these searches is needed by the final proof.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CompactSupportQuotientRawInput": "56498c0470bc88b7cce92f4686879e730985b806"}, "results": {"Sheaf.Paper.CompactSupportQuotientCocycle": {"hash": "d968efa467527c3363d5eea4cc1e0a1110430787", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T00:49:49+0800", "transitive": 0, "version": 1}
```

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
