## What changed

Filled the proof of `AlgebraicGeometry.isIso_structure_of_integral_zero_dim` in
`Sheaf.AlgebraicGeometry.ZeroDimIntegralPoint`, preserving its signature, docstring,
and imports. The proof implements the existing four-step DAG argument directly
from Mathlib. Dimension zero makes every irreducible closed subset maximal, so
all point closures equal the whole space; the scheme's T0 property then makes
its carrier a subsingleton. Mathlib supplies affineness and the field property
of its global sections. The structure ring homomorphism is of finite type,
hence finite and integral by Zariski's lemma, and therefore bijective over the
algebraically closed base field. Naturality of the affine scheme isomorphisms
then makes the structure morphism an isomorphism.

The module compiled without warnings through lcompile.py (2.5 seconds).

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.isIso_structure_of_integral_zero_dim`
(node `lem-weil-pbc-zero-dim-integral-point`).

Holes closed: 1. Holes added: 0. Sorries remaining in the delivered module: none.
No decomposition or auxiliary theorem is needed.

## No longer needed

None. No imports were added or removed, and no dependency nodes or modules were
pruned. All existing imports support the unchanged statement. The declared
proof dependencies are Mathlib leaves or conventions, and their mathematical
roles are retained. The proof uses T0 uniqueness directly after proving that
all point closures agree, without choosing a generic point.

## Where the brief, the DAG or earlier work was wrong

No statement or definition error was found. The existing proof plan is realizable
entirely using Mathlib, without any project theorem containing sorry. Empty
schemes are excluded by integrality, and nonreduced one-point schemes are
excluded by the same hypothesis; thus the field-of-sections lemma applies.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
