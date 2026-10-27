## What changed

Proved `AlgebraicGeometry.Scheme.associatedPoints_eq_weaklyAssociatedPoints` with its
statement unchanged. Replaced the proof-only import of
`Sheaf.AlgebraicGeometry.AssociatedWeaklyAssociated` with
`Mathlib.RingTheory.Ideal.MinimalPrime.Colon`.

The proof unfolds `Ideal.WeakAss` pointwise. The forward implication uses that a
prime ideal is minimal over itself; the reverse implication applies
`Submodule.exists_eq_colon_of_mem_minimalPrimes` to the zero submodule of the
Noetherian stalk ring. The locally Noetherian hypothesis supplies Mathlib's
Noetherian stalk instance. Updated the item's DAG proof and proof dependencies to
record this direct Mathlib route; the unit's route is preserved.

Compiled the completed proof twice through lcompile.py (4.7 and 4.5 seconds).
An explicit `#print axioms` check reports exactly `propext`, `Classical.choice`,
and `Quot.sound`. The final module omits that diagnostic command.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.associatedPoints_eq_weaklyAssociatedPoints`
(node `lem-sc-ass-weakass-locally-noetherian`).

No holes remain in the item. No holes added and no statements split off.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.AssociatedWeaklyAssociated`.
The declared dependencies `lem-sc-ass-weakass-fg-stalk` and
`lem-sc-locnoeth-stalk-maxideal-fg` are not needed: the direct Noetherian
colon-ideal theorem avoids specializing a quasi-coherent sheaf and does not need
a separate finite-generation assertion for the stalk maximal ideal.

Consequently this item's proof no longer needs the following modules formerly
reachable only through the removed proof import:

- `Sheaf.AlgebraicGeometry.AssociatedWeaklyAssociated`
  (`lem-sc-ass-weakass-fg-stalk`).
- `Sheaf.RingTheory.AnnihilatorEqIffMinimalPrimeOfFG`
  (`lem-sc-ass-weakass-fg-prime`).
- `Sheaf.RingTheory.AssociatedLocalizationFg`
  (`lem-sc-associated-localization-fg`).
- `Sheaf.RingTheory.WeakAssLocalization`
  (`lem-sc-weakass-localization`).
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor` and
  `WeilConjectures.Topology.PresheafModuleStalkFunctor`
  (the general module-stalk construction, `def-weil-pbc-module-stalk`).

These are dependency removals for this proof; no declarations or modules are
withdrawn, and other consumers can still need them. The public imports
`Mathlib.AlgebraicGeometry.Noetherian` and `Sheaf.RingTheory.WeaklyAssociated`
remain necessary for the statement.

## Where the brief, the DAG or earlier work was wrong

The planned argument is valid but unnecessarily general for the structure sheaf
on a locally Noetherian scheme. Mathlib already supplies the needed implication
in `Submodule.exists_eq_colon_of_mem_minimalPrimes`
(`Mathlib/RingTheory/Ideal/MinimalPrime/Colon.lean`, line 31).
No mathematical statement or definition changed. The empty scheme is covered
by set extensionality; zero elements cause no exceptional case since minimality
over their annihilator is handled by the Mathlib theorem.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
