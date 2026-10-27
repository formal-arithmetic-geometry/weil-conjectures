## What changed

Proved `WeilConjectures.algebraic_extension_value_group_torsion` in
`Sheaf.RingTheory.ValuationValueGroupTorsion`, preserving its statement and public
imports. Added proof imports for the canonical valuation of a valuation subring,
finite maxima, and field simplification. The proved private helper
`equal_value_terms` shows that a zero sum of nonzero terms has two equal-valued
terms. Applying this to an algebraic polynomial relation gives a unit ratio;
cancelling the lower power gives the requested positive power and base scalar.
Updated the item's DAG proof to this implementation of the polynomial argument.

Read Stacks more-algebra.tex, Tag 0ASH (lemma-inequality-general) and Tag 0ASJ
(lemma-etale-extension-valuation-ring). LeanFinder found only finite-field,
discrete, or valuation-subring infrastructure, and Loogle found only polynomial
valuation lemmas requiring triviality on the coefficient ring. Local Mathlib,
WeilConjectures and Sheaf searches found no theorem with the required generality.
The new proof uses Mathlib's `Valuation.map_sum_eq_of_lt`,
`ValuationSubring.valuation_eq_iff`, and `Finset.exists_max_image`.

Validation: the final module compiled cleanly through `lcompile.py` in 2.8 seconds.
All Lean lines are at most 100 characters.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.algebraic_extension_value_group_torsion`
(node `lem-trf-valuation-value-group-torsion`). Added zero holes and split off
zero statements. No `sorry` remains in this delivery.

## No longer needed

No original imports, DAG dependencies, or modules were removed or pruned.
The algebraicity dependency `def-weil-algebraic-element` remains used.
The explicit nonunit calculations in original DAG steps 1--2 are supplied by
Mathlib's valuation API; they did not correspond to separate dependency nodes.
A tentative proof import `Mathlib.Tactic.Ring` was removed because field
simplification alone closes the final equality.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error was found. The direct polynomial plan is
valid for trivial valuations, equal base and extension fields, inseparable
extensions, arbitrary valuation rank, and infinite algebraic extensions: it uses
only one polynomial relation for the chosen nonzero element. The implementation
reorders the two indices before cancelling, covering both exponent orders in one
calculation. No shared definition, existing signature, or unit route changed.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
