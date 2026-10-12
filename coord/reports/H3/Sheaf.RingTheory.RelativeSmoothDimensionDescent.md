## What changed

Replaced the sorry proof in `Sheaf.RingTheory.RelativeSmoothDimensionDescent` with a complete
proof. The proof uses Mathlib's faithfully-flat smooth descent, smooth standard-open charts,
Kähler differential base change, and rank-at-stalk base change. It introduces private helpers
for smoothness from a local cover, rank transport across localization, rank computation on a
relative-dimension chart, and reconstruction of the local cover from constant rank.

## Proved and sorry left

The declaration `RingHom.locally_standardSmoothOfRelativeDimension_codescendsAlong_faithfullyFlat`
is proved. No `sorry` remains in the delivered module, and no new holes were added.

## No longer needed

No imports or DAG dependencies were removed. The proof directly uses all four stated dependency
nodes: smoothness from local standard-smoothness, the standard-smooth cotangent rank theorem,
Kähler differential base change, and faithful-flatness descent/base change.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan was correct but substantially more detailed than needed in Lean. Mathlib's
`Module.rankAtStalk_baseChange` and `KaehlerDifferential.tensorKaehlerEquiv` provide the fibre
transport and dimension invariance directly, so no new intermediate node was necessary.


## Second reading by H3

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are unchanged byte for byte; only proof imports, private proof helpers, and the target proof were added.
2. Compiled the module with `lcompile.py`; it compiles cleanly with no warnings or `sorry`. The proof contains no forbidden declarations or hollow definitions. The delivery probe checks declaration axioms.
3. The target proof is a genuine reduction through smooth faithfully-flat descent, Kähler differential base change, localization, and stalk-rank transport. No statement was split off, and no new statement or node was added.
4. The proof uses all four recorded proof dependencies and all added imports are proof-only plain imports. No old dependency or import is unused. The unit route is retained through the recorded target node; no unit-level bypass was introduced.
5. The DAG node statement and Lean theorem statement agree, and the node proof/proof_deps/proof_origin remain consistent with the implemented route. No statement change or definition change was made.

Changed during second reading: no source proof changes were necessary; added this review section only.
