## What changed

Restored the assigned quarantined module from its recorded archive and proved
`AlgebraicGeometry.Etale.etaleOpenExtensionNormalization` by a categorical mate calculation.
The theorem's signature, docstring and public import are unchanged. Added proof imports for
the existing derived-factor API and four new, completely proved comparison lemmas.

The scalar representative is the inverse mate of the scalar restriction localization factor.
The exact open localization factor's mate is the inverse open restriction localization factor,
by the published derived-unit formula. The ordinary cochain open/scalar comparison is conjugate
to the ordinary restriction/scalar square, degree by degree. The canonical derived comparison
is conjugate to the derived restriction/scalar square by its defining left-adjoint uniqueness. Composition and conjugation of
mates, together with compatibility of the exact localization factors, then prove normalization
for every complex, hence for the K-flat complexes in the original predicate.

The first version checked these components inside the item. Profiling found expensive kernel
conversions through the large concrete adjunction definitions: the ordinary-conjugate helper
alone took about 57 seconds. Passing the comparison explicitly to the generic cochain lemma
reduced that check to about 21 seconds. Local opacity annotations avoid expanding the chosen
derived-category instances. The whole file still exceeded 60 seconds. Isolating the derived conjugation conversion
also avoids repeatedly comparing its large composite adjunctions inside the final proof, so the independent
proved comparisons now occupy their own modules. The remaining composition is checked in a generic private diagram lemma before
specializing to sheaves. The generic lemma constructs the scalar squares as inverse
mates and substitutes the published representative identities; the item supplies only those
identities and the open factors. This avoids repeated expansion of the concrete adjunctions
and associator comparisons. A private typed restriction-factor lemma keeps that square
opaque in the final application. Explicit ordinary and derived functor arguments prevent
inference from expanding the concrete adjunction projections; this reduced checking the
final theorem from about 46 seconds to 4.3 seconds. No shared definition, public statement, consumer, or other existing
module is changed.

Updated the item's node proof and dependencies to record the actual argument and the four
proved helper nodes.

## Proved and sorry left

Closed the one existing hole in
`AlgebraicGeometry.Etale.etaleOpenExtensionNormalization`
(node `lem-coef-etale-open-extension-normalization`).

Holes closed: 1. Holes added: 0. Holes remaining in all delivered modules: 0.
The four new public comparison theorems and all private helpers have complete proofs.
No unproved statement is split off.

Validation: all four helper modules compiled in dependency order. The item compiled in
28.9 seconds (4.3 seconds checking the main theorem and 12.8 seconds checking the typed
restriction-factor lemma), within the 60-second file limit. An earlier delivery attempt
stopped without pushing when its compile exceeded 60 seconds; the explicit functor
arguments provide the substantial timing margin in this final version.
All profiling options were then removed. The existing derived-factor proof import passes
`tools/import_direction.py may`. The delivery tool performs the final compile, axiom and
packet checks.

## No longer needed

No modules or mathematical dependencies are pruned. The original public import is retained.
The original homotopy-adjunction and change-of-rings proof dependencies now occur through
the new proved comparison nodes. The argument needs neither a K-flat resolution nor
invertibility of the scalar representative; the normalization equality itself holds on
arbitrary complexes. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item was absent from `lean/` because of the quarantine recorded in `coord/rework.tsv`;
its original declaration was preserved and restored from the specified archive.
The current A7 return entry concerns another item and imposes no repair on this theorem.

The mathematical statement and original proof plan are correct. The previously split
normalization obligation can be closed using the existing scalar unit transpose and exact
open adjunction's localization formula. No additional hypothesis or further hole is necessary.

## New nodes

- `lem-coef-etale-open-derived-conjugate`: the canonical derived comparison is conjugate
  to the derived restriction/scalar square; proved.
- `lem-coef-etale-open-cochain-conjugate`: ordinary uniqueness of left adjoints remains
  conjugate to the restriction square after passing to cochain complexes; proved.
- `lem-coef-etale-open-localization-mate`: the exact open localization factor has the
  inverse restriction localization factor as its right mate; proved.
- `lem-coef-etale-scalar-representative-mate`: the published scalar representative is
  the inverse mate of the exact scalar restriction localization factor; proved.

Each is strictly one step of the original argument. All apply to arbitrary complexes and
allow empty schemes and zero rings. Mathlib and blueprint searches found generic mate and
localization formulas but no duplicate for these fixed étale comparisons. The blueprint
ancestor tool reports `None` for this item's creation chain; the new nodes record that value
and identify the precise parent proof step.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
