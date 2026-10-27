## What changed

Proved `WeilConjectures.IntegralSystemRealization.completedShriekUnits` for both
canonical unit triangles. The proof stays in the derived system category and
uses the existing proper/open coherence interface.

Private helpers derive the left proper-image unit from compositor associativity
and the two-identity normalization, identify inverse-image units by adjunction
mates, and deduce the open-extension units by uniqueness of left adjoints.
The canonical bridge transports the intrinsic identity-square equations to the
specified operations. Naturality then combines these equations with the two
compositors to give the displayed compactification unit laws.

The public statements, definitions, imports, and the other proofs are retained.
There are no source-library changes or new public declarations.

Validation: the complete module compiled through `lcompile.py` in 56.6 seconds,
within the 60-second file limit, with no warnings.

## Proved and sorry left

Initial holes: 5. Closed: 1. Added: 0. Remaining: 4.

Closed:

- `WeilConjectures.IntegralSystemRealization.completedShriekUnits`.

The following original theorem holes remain unchanged:

- `WeilConjectures.IntegralSystemRealization.completedShriekAssociativity`.
- `WeilConjectures.IntegralSystemRealization.completedShriekFiniteEvaluation`.
- `WeilConjectures.IntegralSystemRealization.completedShriekIntegralComposition`.
- `WeilConjectures.IntegralSystemRealization.completedShriekSpecifiedIntegral`.

Every new private helper has a complete proof. No statements were split off.

## No longer needed

None. No imports, nodes, or modules are pruned. This implements the unit-law
part of proof step 5, using the compositor associativity and identity-pair
normalization already present in the node's proof dependencies. The finite-stage
part of step 5 and the other open obligations still need their recorded routes.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or proof route was changed. Expanding the canonical
identity comparisons can mix two definitionally equal presentations of the
coefficient category and leave expressions that the simplifier cannot normalize
at its implicit transparency level. Private comparisons with explicit
`System l E X` endpoints keep these presentations folded during the unit proof.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
