## What changed

Proved `WeilConjectures.sfRationalHeart_properties` and
`WeilConjectures.sfCommonStageHeart_properties` in
`lean/Sheaf/Paper/SfConstructibleHeart.lean`, with unchanged signatures and definitions.
Each proof reads the prescribed aisle and coaisle equations from the existing unique
existence theorem, identifies their intersection with the heart, applies Mathlib's
truncation-vanishing criteria at (0,1) and (-1,0), and transports abelianity along the
heart-property equality. A private proof import of
`WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.Heart` supplies the
already proved general `TStructure.abelianHeart` construction. No new theorem or
object is assumed or chosen.

Verification: the whole item compiled cleanly through `lcompile.py` in 3.9 s on
this resumption (2026-10-19), confirming the earlier successful compiles. The retained file was
compared against the current shared source: the only changes remain the private
proof import and the two proof bodies; all signatures and definitions match.
Searches through msearch.py (Lean Finder, Loogle and grep) and the source library
located the general heart and truncation APIs. The source signatures were read.

## Proved and sorry left

Closed 2 of the item's 4 original holes:

- `WeilConjectures.sfRationalHeart_properties`.
- `WeilConjectures.sfCommonStageHeart_properties`.

Added 0 holes; split off 0 statements. The 2 unchanged holes are:

- `WeilConjectures.sfRationalStandardTStructure_existsUnique`
  (`def-weil-constructible-heart`). It still needs construction of the standard
  bounded t-structure on the intrinsic integral category, rational localization,
  and identification of all prescribed classes. The stated PBC integral and
  localized t-structure results concern another coefficient presentation; their
  comparison is not a definitional equality.
- `WeilConjectures.sfCommonStageStandardTStructure_existsUnique`
  (`def-weil-constructible-heart`). It still needs finite-stage t-exact scalar
  extension and common-stage descent of the truncation triangles and bounds.

The two proved properties depend on the corresponding original existence theorem,
which is intentional: their general heart and truncation arguments are now complete,
while the geometric existence obligations remain explicitly named.

## No longer needed

No existing imports, modules, or nodes were removed. No new proof imports besides
upstream's general abelian-heart implementation were retained. The supplementary
idempotent kernel decomposition in `prop-weil-heart-abelian` is unnecessary for
these two proofs; the already proved upstream abelian-heart construction suffices.
That node remains reachable through the unchanged public legacy import, so this
is not a claim that its module has been pruned from the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The shared checkout initially lacked the assigned source file, then supplied it
in its refresh. Work proceeded from that supplied version.

The heart node is a definition node with an empty proof and empty proof_deps;
there are no numbered theorem proof steps in that node to translate. Its Lean
existence theorems contain the construction plans in their docstrings.

`WeilConjectures.constructibleTruncations_exists` supplies the
common-stage bounded t-structure with exactly these classes, but its module
already imports this item. `tools/import_direction.py may` confirms that using it
here directly would close a cycle. Extracting the three standard-class definitions
into a separate module would make that dependency direction possible, but would
also require changing `Sheaf.Paper.ConstructibleTruncations`, held by Z8. This
delivery leaves that module and all interfaces untouched.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
