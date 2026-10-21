## What changed

Completed the five theorem proofs in `Sheaf.Paper.LocalFrobeniusTrace`.
The two base-map equations use contravariant Spec composition and the specified
field-embedding equations. Closed-point degree positivity follows from the existing
closed-point residue-field theorem and `Module.finrank_pos`.

The two return equations use three proved private helpers: the positive-power formula
for the point Frobenius, the iterated geometric-Frobenius projection equations, and
pullback uniqueness for a lift of a fixed model map. The existing proved theorem
`FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_of_card_eq` supplies the
finite-field calculation for both cases. Added one private proof import,
`WeilConjectures.PointCount`, for the residue-field structure-map equation.
All public signatures, definitions, and public imports are preserved. Disabled only
the unused-section-variable linter, since proving the compatibility equation no longer
uses the finite-type assumptions retained in its existing signature.

Profiling located excessive unfolding under the original file-wide
`backward.isDefEq.respectTransparency false` setting. Restored the normal setting
for the file and retained the old setting only on the two private pullback lemmas.
No definition body or public declaration signature was changed for this adjustment.

The complete module compiled without diagnostics in 13.5 seconds through `lcompile.py`.
A source comparison also verified every original declaration signature is unchanged,
there are no remaining `sorry` tokens, and every Lean line is at most 100 characters.

Updated the existing definition node's proof, proof dependencies, and proof origin to
record these proofs. The unit route and mathematical construction are unchanged.
The settings and their eleven transitive consumers are documented in
`coord/changes/A8-local-frobenius-trace-elaboration.md`; no consumer adaptation is needed.

## Proved and sorry left

Closed all five original holes, attached to `def-weil-local-frobenius-trace`:

- `WeilConjectures.localExtensionPoint_compatible`.
- `WeilConjectures.localExtensionPoint_return`.
- `WeilConjectures.localClosedPointDegree_pos`.
- `WeilConjectures.localClosedPoint_compatible`.
- `WeilConjectures.localClosedPoint_return`.

Zero holes remain in the item. Zero holes added; zero statements split off.
The three new private helpers are proved in full.

## No longer needed

None. No existing import, declaration, dependency node, or module is removed.
The existing proved finite-field lemma avoids introducing new fixed-field theory.
The unique-subfield theorem remains needed for the existing extension-field construction
and its cardinality; the closed-point theorem remains needed for residue finiteness.

## Where the brief, the DAG or earlier work was wrong

The definition node had no proof steps despite the module's five theorem holes.
Its updated proof now records the arguments already described in the declaration
docstrings, using the existing finite-field lemma for the embedded fixed-point step.
No statement or definition repair was necessary. The positive-index edge cases n=1
and r=1 are covered by the zero branch of localPositivePower; no assertion that a
geometric point is literally fixed as a scheme map is used.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
