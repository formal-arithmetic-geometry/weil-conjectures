## What changed

Filled the seven proof bodies in
`Sheaf.Algebra.Homology.LocalizedBoundedHomComparison`, retaining every public
signature and every public definition body. Private helpers prove precomposition
preserves zero and addition, lift degreewise splittings through the Hom products,
and construct the signed single-source shift from the product projections.

The source differential vanishes in the single-source case. The explicit
factor identifications therefore construct the signed shift with the exact
normalization `(-1)^(r*q)` and prove its naturality in every target chain map.
The existing canonical SES triangle construction supplies both connecting squares.
The final proof installs the canonical coefficient action, uses the supplied
triangulated scalar localization, and applies downward induction to the canonical
stupid tails. It transports back along the tail inclusion and treats empty support
intervals through the zero-source calculation.

Reused the proved generic zero-map and degreewise-splitting helpers from
`StupidTailHomShortExact` through a private `import all`; its source file is
unchanged. Removed the proof import of `HomComplexShiftLeft`.
The existing node's proof steps and dependencies record the direct projection
argument. Private categorical helpers keep the product splitting and signed projection
calculations abstract, so they can be applied without repeatedly expanding the
sheaf constructions. Removed the unused public import
`Sheaf.CategoryTheory.SiteCoveringAxioms`.
No adopted-source files were changed.

Repaired the return at `e908b74bc06`: removed the duplicate private theorem
`CategoryTheory.LocalizedBoundedHom.fan_projection_isIso`. The single-source
argument now applies the existing proved `CategoryTheory.fan_projection_isIso`
from `WeilConjectures.Algebra.Homology.SingleDegreeExactTermHomQuasiIso`,
accessed by a private `import all`. The DAG records this helper dependency;
no projectivity or quasi-isomorphism hypotheses from that module are used.
The repaired module compiled through `lcompile.py` in 40.9 seconds with no
errors or warnings.

## Proved and sorry left

Closed seven original holes, all attached to
`lem-sf-localized-bounded-hom-comparison`:

- `CategoryTheory.LocalizedBoundedHom.row_zero`;
- `CategoryTheory.LocalizedBoundedHom.row_shortExact`;
- `CategoryTheory.LocalizedBoundedHom.row_comm`;
- `CategoryTheory.LocalizedBoundedHom.signed_single_shift`;
- `CategoryTheory.LocalizedBoundedHom.triangles`;
- `CategoryTheory.LocalizedBoundedHom.localized_triangles`;
- `CategoryTheory.LocalizedBoundedHom.isIso_comparison`.

No holes remain in the item and no holes were added. No intermediate theorem
was split off. Every private helper has a complete proof.

## No longer needed

Removed the unused public import `Sheaf.CategoryTheory.SiteCoveringAxioms`;
the proof uses no declarations from that module.

This item's proof no longer needs the following dependency:

- `lem-pur-hom-complex-shift-left`, module
  `WeilConjectures.Algebra.Homology.HomComplexShiftLeft`: the required normalized
  single-source shift is constructed directly, including its component formula.

That private import and its proof-dependency/tool-use entries were removed.
Both adopted-source modules and all their declarations remain in the library;
this delivery makes no claim that other consumers no longer need them.
No unit statement or step is bypassed and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The declared dependency `homComplex_shift_left` gives a natural source-shift
isomorphism but does not state the component normalization required by this
item. The direct single-source projection calculation proves that extra clause.
Likewise, the existential short-exact Hom-row theorem does not on its own
identify all maps with this item's specified canonical row; using the canonical
source splittings directly avoids that identification issue.

The returned delivery had duplicated an existing product-projection helper;
this repair removes that duplicate and reuses the adopted-source proof.

No statement was disputed or changed. The proof explicitly handles zero source
terms, zero complexes, negative shifts and empty support intervals. There are
no projectivity or quasi-isomorphism assumptions on the input map.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
