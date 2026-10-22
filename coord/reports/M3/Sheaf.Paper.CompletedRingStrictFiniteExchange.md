## What changed

Filled the proof of `AlgebraicGeometry.Scheme.completedRingStrictFiniteExchange`
without changing its statement or the existing public definitions. The proof first
compares inverse exchanges on ordinary complexes, uses the actual strict and finite
model maps and their counit equations, and descends the resulting square by K-flat
resolutions and localization extensionality. Inverse cancellation gives the forward
square in the statement.

A generic counit-naturality API supports the normalization descent. Private helpers reuse the proved objectwise K-flat tower-resolution theorem,
extend strict counit normalization to arbitrary tower complexes, and perform the
model-map and degreewise comparisons. The existing tower resolution
uses the independent-coefficient functorial flat-resolution machinery;
it does not assume finite reductions are K-flat over the completed ring.

Private categorical APIs keep the chosen isomorphisms intact during equality
transport and inverse cancellation. The complex comparison is proved degree by
degree from a separate ordinary scalar compatibility statement.

Added the proof-only import `Sheaf.Paper.CompletedFiniteScalarExchange` and use
`import all Sheaf.Paper.CompletedStrictOpenExchange` to reuse its proved private
tower-resolution theorem. All existing public imports remain. Updated the item's
DAG proof and direct proof dependencies to match the argument.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.completedRingStrictFiniteExchange`
(node `lem-cbc-completed-ring-strict-finite-exchange`), the item's one original hole.
The uniqueness proof of `cbcFiniteComparisons_existsUnique` combines its two
heterogeneous normalization equations before converting their result to equality.

Added and left with `sorry`:
`AlgebraicGeometry.Scheme.cbcFiniteScalarExchange_inverse`
(node `lem-cbc-completed-finite-scalar-exchange`), the ordinary module-level
coefficient compatibility part of Step 8. It contains no derived categories,
complexes, K-flatness, tower resolutions, model counits, or derived reduction of
arbitrary objects. The original theorem combines this ordinary result with the
separate termwise, strict-model, K-flat and localization arguments in complete Lean.

This is a decomposition: one original hole closed, one hole added, net zero holes
closed. The item module has zero holes; the new scalar module has exactly one,
in the named public theorem above. No definition contains a hole.

The scalar proof attempt established the generic mate calculation, the normalized
compositor and inverse formulas, the open-unit generator coverage, and the
cartesian site-arrow identity in diagnostic compilations. It did not complete the
native sectionwise compositor and generator formulas: the final conversions expand
pullback limit cones and sheaf constructions. None of that unfinished proof code is
included in the delivery; the new declaration has its complete proof in words.

Validation: the combined server compile passed for both actual delivery files:
`CompletedFiniteScalarExchange` in 3.0 seconds and
`CompletedRingStrictFiniteExchange` in 52.3 seconds. All seven existing public
declaration signatures and the four existing definition bodies are unchanged.
Both DAG proof-dependency lists equal the union of their proof-step uses.
The first preflight identified a missing LeanSearch kind (Loogle and LeanFinder
count together) and a required change record for local proof commands. An actual
LeanSearch query and the command-only change record repair those packet errors.

## No longer needed

No Lean module is withdrawn and no existing public import is removed. In particular,
none of the adopted `WeilConjectures` declarations or their imports is changed.

The direct proof dependencies below are replaced by the existing strict-normalization
and finite-comparison interfaces, or by the proved independent-coefficient functorial
resolution construction. They are not claimed globally unnecessary: the geometric
construction of the imported interfaces and other consumers can still need them.

- `lem-weil-proetale-weakly-etale-localization`.
- `def-weil-pbc-adic-coefficient-datum`.
- `def-weil-pbc-completed-pullback`.
- `lem-pur-site-restriction-module-adjunction-exact`.
- `lem-weil-pbc-ringed-topoi-module-adjunction`.
- `def-weil-pbc-composite-adjunction`.
- `def-weil-proetale-inverse-image`.
- `lem-weil-pbc-localize-ringed-site-morphism`.
- `def-cbc-open-immersion-square`.
- `lem-weil-pbc-conjugate-iso-unit-equation`.
- `lem-weil-pbc-diagram-kflat-replacements`.
- `lem-cbc-ringed-open-flat-resolution`.
- `lem-weil-tower-category-levelwise-abelian`.
- `lem-sf-exact-functor-derived-triangulated`.
- `lem-pur-left-derived-from-kflat-class`.
- `lem-cbc-ringed-open-strict-reduction`.
- `lem-weil-pbc-constant-completion-equivalence`.
- `prop-weil-pbc-proetale-constant-exact`.
- `lem-sf-open-tensor-normalization`.
- `lem-cbc-finite-open-exchange-scalars`.

The equal-universe `Sheaf.Algebra.Homology.DiagramKFlatReplacements` theorem is not
imported directly: the functorial resolution and transposition argument works at
the actual independent site and coefficient universes. The finite-to-finite scalar
exchange theorem is not applied to a completed ring. The item's unit route, finite
open exchange, and strict exchange construction are retained.

## Where the brief, the DAG or earlier work was wrong

Step 8's finite-to-finite scalar theorem does not directly state the completed-to-finite
ordinary scalar square: its source and target coefficients are finite constant rings.
The new node makes this distinct ordinary coefficient compatibility explicit.

Also, the strict normalization is stated only on objectwise K-flat towers, whereas
an ordinary reduction tower need not be objectwise K-flat over the completed ring.
The proof supplies the missing naturality/resolution extension before using the
normalization on that tower. No statement was weakened and no target was changed.

## New nodes

`lem-cbc-completed-finite-scalar-exchange`, in
`Sheaf.Paper.CompletedFiniteScalarExchange`, is precisely the ordinary mixed-coefficient
compatibility part of the original Step 8. Its proof plan transposes under the two
composite adjunctions, uses the normalized direct-image and open-restriction formulas
on unit generators, and identifies the cartesian site arrow by its projections.
For the open restriction, the unit-generator normalization and invertibility of the
comparison show that every section is a distinguished unit generator. This removes
the need for a separate tensor/sheafification generation lemma.
The edge cases of empty opens, identity maps, zero modules and the zero finite ring
require no extra hypotheses. The parent performs the separate degreewise, strict-model,
K-flat and derived-localization arguments. The command-only change record is
`coord/changes/completed-ring-finite-proof-commands.md`: the static interface index
records local proof attributes, opened namespaces and elaboration options. Existing
statements, public definitions and public imports are unchanged, and neither of
the two downstream modules needs adaptation.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
