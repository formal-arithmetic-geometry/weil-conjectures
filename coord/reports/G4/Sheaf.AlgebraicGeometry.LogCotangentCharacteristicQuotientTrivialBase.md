## What changed

Proved `AlgebraicGeometry.EtaleLogHom.existsUnique_logCotangent_characteristicQuotient_of_trivialBase`
in the assigned module, with its statement unchanged. Private helpers construct the pointed
pullback cocone for the map of log stalks and prove that every relative base log germ is a unit.
The proof sends ordinary symbols to zero and log symbols to characteristic classes, checks all
six families of differential relations, descends to the quotient, and extends scalars.
Surjectivity uses the fraction presentation of the Grothendieck group and tensor induction;
uniqueness uses quotient, Finsupp and tensor induction. No new imports or public declarations.
Added `coord/changes/log-cotangent-characteristic-quotient-proof-options.md` for the
expanded open command and the elaboration options required by the proof; the consumer
check reports zero downstream modules.
Updated the existing node to match this proof.
Single-file verification with lcompile.py: clean compilation in 16.1 seconds.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.EtaleLogHom.existsUnique_logCotangent_characteristicQuotient_of_trivialBase`
(node `lem-sfb-log-cotangent-characteristic-quotient`). Added 0 holes; split off 0.
No sorry remains in any delivered Lean declaration.

## No longer needed

No existing imports removed; all five original public imports are preserved.
The proof does not need these originally declared dependencies:

- `lemma-weil-pbc-affine-neighbourhood-cofinal`
  (`WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization`).
- `def-weil-pbc-strict-henselization-limit`
  (`WeilConjectures.AlgebraicGeometry.StrictHenselization`).
- `lem-weil-pbc-strict-henselization-local-structure`
  (`Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility`).
- `lem-weil-pbc-local-ring-unit-criterion` (Mathlib's local ring unit criterion).

The residue quotient is already by the ideal spanned by nonunits. Its nonunit-vanishing
property is therefore immediate from Ideal.subset_span and the quotient equation.
The first three obsolete top-level tool-use approvals were removed from the node.
No module is withdrawn: these dependencies can still be needed by other consumers.

## Where the brief, the DAG or earlier work was wrong

The original Step 1 was stronger than necessary: no locality or strict-henselization comparison
is needed for this map into the given quotient. Step 5 is implemented at stalks, rather than
asserting that the section monoid itself consists of units. Pointed pullbacks and naturality
supply the actual stalk map and handle every relative neighbourhood relation.
The statement agrees with ILO X Proposition 1.2 proof, printed pp.136–137, map (1), read from
the local PDF. In a trivial log structure the target characteristic group is zero; for a
standard log point the construction sends each dlog generator to its characteristic basis
element. Nonunit and unit structural relations are both checked explicitly in Lean.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
