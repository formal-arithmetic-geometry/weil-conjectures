# CategoryTheory.DecreasingFiltration.cohomologyImage_graded_presentation

## Reason

The assigned item is a listed retirement in `coord/retire-items.tsv` and
`coord/queue.tsv`. The current Sheaf module contains zero holes and duplicates
the proved theorem in `WeilConjectures.CategoryTheory.FilteredCohomologyImagePresentation`.
The full theorem signature and complete proof agree modulo whitespace.
The earlier PROOFDIFF_UNSAFE inventory predates the retirement of the parallel
filtration, subquotient, cycle-map, and normalized-presentation providers.
The current consumer already imports those providers from WeilConjectures.

## Old

`Sheaf.CategoryTheory.FilteredCohomologyImagePresentation` supplied this theorem:

```lean
theorem cohomologyImage_graded_presentation
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (L : DecreasingFiltration K) (p n : ℤ) :
  let A := L.complexStep p n
  let A' := L.complexStep (p + 1) n
  let Z := (Subobject.pullback (K.d n (n + 1))).obj ⊥
  let B := imageSubobject (K.d (n - 1) n)
  Nonempty ((L.homologyFiltration n).gradedPiece p ≅
    cokernel ((Subobject.pullback (A ⊓ Z).arrow).obj
      ((A ⊓ B) ⊔ (A' ⊓ Z))).arrow)
```

The sole direct consumer used this proof import:

```lean
import Sheaf.CategoryTheory.FilteredCohomologyImagePresentation
```

## New

Withdraw `lean/Sheaf/CategoryTheory/FilteredCohomologyImagePresentation.lean`
using `deleted.txt`. The adopted upstream theorem supplies the exact same
signature above with its complete, unchanged proof. Replace the consumer's
proof import with:

```lean
import WeilConjectures.CategoryTheory.FilteredCohomologyImagePresentation
```

Reattach `lem-sp-filtered-cohomology-image-presentation` to that upstream
module and file, preserving its declaration, verbatim statement, proof steps,
proof dependencies, and all parent edges. No mathematical result or unit step
is withdrawn. No source-library declaration, signature, attribute, public
import, definition, or proof changes. No target statement or definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FilteredStableSubquotient | unclaimed | Replace one private proof import; every declaration and proof stays verbatim. |

`tools/downstream.py --names --uses cohomologyImage_graded_presentation` and
its `--direct --names` variant both list only this consumer. Searches in active
and quarantined Lean sources found no additional direct importers. The DAG
parent `lem-sp-filtered-stable-subquotient-at-bounds` continues to use the same
node and therefore the same theorem, now supplied upstream. The normalized
quotient node's blueprint provenance still references this node and is retained.
The unit `sk-prop-av-pqf-finite` has no realized slot for this node, and none
of its statement or proof steps changes.

## Status

landed 20261021T021904-L-2789105 2026-10-21 (merge of deliver/B6/Sheaf.CategoryTheory.FilteredCohomologyImagePresentation)

The upstream theorem is checked against the original Sheaf signature by an
explicit server-compiled example and `#print axioms`. The adapted consumer is
server-compiled. Delivery preflight and the maintainer's independent review
and global build verify the retirement packet.
