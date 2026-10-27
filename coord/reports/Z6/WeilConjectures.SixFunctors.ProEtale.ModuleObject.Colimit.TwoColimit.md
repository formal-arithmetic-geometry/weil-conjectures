## What changed

Restored the five theorem proofs from the preferred upstream file recovered at
81303983ee8, applying them to the current source rather than replacing the source
wholesale. Existing public signatures, docstrings, public imports and non-theorem
bodies are preserved. Hom surjectivity precedes object descent because the latter
uses it. All added helpers are private and proved; the added imports are private
proof imports, including `import all` for the existing private proof APIs.

The proof follows the existing DAG: generic exact scalar extension preserves
bounded constructibility; faithful derived extension proves Hom injectivity;
filtered coefficient complex presentations, constructible-sheaf Hom continuity
and bounded devissage prove Hom surjectivity; finite coefficient sheaf descent
and triangulated essential-image devissage prove object descent. No route change,
new node, or consumer adaptation is required. Local elaboration settings restore
the construction sharing documented in earlier landed change records. Explicit
factorization types and a subtype carrying a morphism with its defining equation
avoid repeated unfolding; the single-sheaf comparison is typed before composition. The new
change record is `coord/changes/Z6-two-colimit-recovered-proofs.md`.

Compilation: the complete module passed `lcompile.py` with no errors or warnings
in 58.6 seconds. Delivery validation runs below. Textual checks confirm all nine
existing non-theorem declarations and all six theorem signatures are byte-identical.
Every added proof import was checked for cycles back to the item; none occurs.

## Proved and sorry left

Closed five existing holes (names in namespace `AlgebraicGeometry.ProEtale`):

- `boundedConstructible_derivedExtendScalarsSubfield_obj`
  (`lem-sfb-extend-subfield-constructible`).
- `boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj`
  (`lem-sfb-extend-to-qlbar-constructible`).
- `constructibleCocone_homSurj` (`lem-sfb-constructible-cocone-hom-surj`).
- `constructibleCocone_essSurjObj` (`lem-sfb-constructible-cocone-obj`).
- `constructibleCocone_homInj` (`lem-sfb-constructible-cocone-hom-inj`).

The unchanged assembly `constructibleCocone_isFilteredTwoColimit` uses these
three descent results. Zero holes remain in the item; zero holes are added and
zero results are split off. This does not assert that every transitive dependency
has already been proved.

## No longer needed

None. No current public import is removed, no module is withdrawn, and the
existing DAG proof dependencies and unit route are retained. The restored
private imports supply the declarations used by the existing proof plans.

## Where the brief, the DAG or earlier work was wrong

The sync lost all five proofs currently missing, although the recovery brief
specifically highlighted object descent and Hom surjectivity. The recovered
file also provides both scalar-extension preservation proofs and Hom injectivity.
All five are restored.

Maintainer action needed for future sync preservation: this upstream module
requires its added `Sheaf.*` proof imports and proved private helpers. Please
record the necessary exception in `coord/upstream-statement-exceptions.tsv`;
this delivery does not modify that maintainer-owned file. The helper families
are Hom continuity closure, exact-derived shift/triangulated transport, Hom
factorization and tensor-comparison component formulas, and the ambient
constructible cocone used for object descent.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
