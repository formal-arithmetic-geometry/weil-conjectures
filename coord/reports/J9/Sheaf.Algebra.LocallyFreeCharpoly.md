## What changed

Filled both remaining proofs in `Sheaf.Algebra.LocallyFreeCharpoly`, preserving every
existing declaration signature, definition body, and public import. Added private proof
imports for localization/tensor comparison, characteristic-polynomial base change,
ULift rings, and ideal quotients, plus a proved private scalar-tower comparison helper.

`Algebra.locallyFreeCharpoly_spec` applies the existing existence/uniqueness theorem
in the requested universe. ULift and scalar-tower compatibility descend its property
to the definition's universe, where uniqueness identifies the two polynomials.
`Algebra.locallyFree_constantRank_eq` transports one basis from each cover to the
same residue-field tensor product and compares their finite dimensions. The existing
cover-and-rank independence theorem now uses these completed proofs.

Updated the item's DAG proof to match these arguments. No other existing module or
node is changed. No new public statement, definition, or axiom is introduced.

## Proved and sorry left

Closed 2 of the module's 2 original holes:

- `Algebra.locallyFreeCharpoly_spec`.
- `Algebra.locallyFree_constantRank_eq`.

Both belong to `def-weil-pbc-charpoly-locally-free`. Added 0 holes; 0 holes remain.
`Algebra.locallyFreeCharpoly_eq` keeps its existing complete proof. No decomposition
or split-off statement is used.

The constructions cover rank zero; an empty cover over a nonzero ring is ruled out
by the span argument. The characteristic-polynomial specification also permits the
zero ring; the existing independence proof explicitly handles that case. Universe
lifting preserves the original full statement.

## No longer needed

No imports, modules, or DAG dependencies are pruned. The rank proof avoids the
intermediate product localization by passing directly to a common residue field;
it still uses all three existing localization and scalar-extension dependencies.
All declared proof dependencies remain needed.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The upstream existence theorem
is now proved. The original rank plan can be shortened: each cover localization
maps directly to the same residue field, so a preliminary common product
localization is unnecessary. This is below the unit level and changes no unit step.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
