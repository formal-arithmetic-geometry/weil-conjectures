## What changed

Added and compiled a private categorical lemma showing that postcomposition with an
isomorphism is bijective on every hom-set. This makes the automorphism obstruction in the
existing `STATEMENT-DISPUTED` diagnosis explicit while preserving the assigned theorem's
signature and its proof hole.

## Proved and sorry left

The private lemma `postcomp_bijective_of_iso` is proved. No original sorry was closed:
`AlgebraicGeometry.ProEtale.CondensedRing.existsUnique_smoothTrace` remains one disputed
sorry because the displayed uniqueness claim is false without a normalization. No new
sorry was added.

## No longer needed

None. The statement imports remain necessary for the public signature. No DAG dependency was
pruned.

## Where the brief, the DAG or earlier work was wrong

The `∃!` clause cannot follow from bijectivity of postcomposition alone. If `e : B ≅ D`,
postcomposition by `e.hom` is bijective, and the same phenomenon supplies distinct candidate
traces after composing with automorphisms of the representing object. The identity smooth map
in relative dimension zero gives the stated edge case. The target statement is preserved and
remains marked `STATEMENT-DISPUTED`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SmoothPurity.TraceExistence": "678120b12ce66314e984a9cde42495dc942809e0"}, "results": {"WeilConjectures.SmoothPurity.Defs": {"hash": "bf5789f90d911ab0a7e6484aa9e6fa239ca04954", "status": "OK"}}, "seconds": 111, "time": "2026-10-28T09:37:51+0800", "transitive": 0, "version": 1}
```

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
