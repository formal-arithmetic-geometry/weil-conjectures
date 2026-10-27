## What changed

Proved the final assembly theorem `composition_compatible_dnc_charts` from the existing
normalization and pasting declarations and one smaller source-coordinate transport lemma.
The proof extracts `ChartEquation` from `diagonalSectionPasting` at the identity open
restriction, constructs the three centred-chart witnesses from the stated neighbourhood
lemma, and applies the three orientation and DNC coordinate normalization equations.
A proved private bifunctor composition helper combines the tensor inputs. Cancellation
of the coordinate isomorphisms and functoriality of pullback prove the final DNC equation.

Added the proof-only import `Sheaf.Paper.CentredDiagonalSourcePasting`. Its theorem assumes
the existing `ChartEquation` and only transports that equation to centred neighbourhoods
and the actual pro-etale presentation. It contains no normalization or DNC conclusion.
All existing signatures, definitions and public imports stay unchanged.

## Proved and sorry left

Closed: `WeilConjectures.PurityFiniteSetting.composition_compatible_dnc_charts`
(node `lem-pur-composition-compatible-dnc-charts`).

Untouched holes in the item:
- `WeilConjectures.PurityFiniteSetting.compatibleNu_etale_restriction`
  (node `lem-pur-composition-compatible-dnc-charts`).
- `WeilConjectures.PurityFiniteSetting.composition_compatible_tangent_normal`
  (node `lem-pur-composition-compatible-dnc-charts`).

Added: `WeilConjectures.PurityFiniteSetting.centred_diagonal_source_pasting`
(node `lem-pur-centred-diagonal-source-pasting`).

This is a decomposition: one of three original holes closed, one smaller hole added.
Two original holes remain in the item; three holes remain across the delivery.
The private bifunctor helper is fully proved. No definition contains a hole.

## No longer needed

None. No import or module was removed, and the existing geometric, tangent and
restriction routes remain. The new lemma isolates the transport implicit in the old
Step 6; it does not bypass the unit route or remove any existing dependency.

## Where the brief, the DAG or earlier work was wrong

The item contains three original holes, including the tangent and nu restriction
assertions. The earlier pasting coordinate clause uses full difference-map section
comparisons, whereas the final assembly uses arbitrary centred-neighbourhood
comparisons and canonical pro-etale site transport. These are not definitionally
identical maps. The new node records exactly this remaining bridge, with the existing
chart equation as its premise. It is strictly one part of the original argument.

The proof includes rank zero and empty schemes: the existing neighbourhood and
normalization declarations have those domains, and the combining argument is purely
categorical. No new hypothesis on the assembly theorem or orientation is introduced.

## New nodes

`lem-pur-centred-diagonal-source-pasting` in
`lean/Sheaf/Paper/CentredDiagonalSourcePasting.lean`: the assumed chart pasting equation
transports to arbitrary centred coordinate neighbourhoods. Its source is the current
composition-coherence proof Step 1, refined by the original node's Steps 5--6.
The proof in words specifies locality cancellation, the Cartesian g difference square,
and naturality of comparison-site tensor and pullback. No change record is needed:
existing interfaces and data are unchanged.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
