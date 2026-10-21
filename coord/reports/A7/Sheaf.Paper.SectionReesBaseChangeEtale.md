## What changed

Filled the six theorem bodies and updated their proof docstrings in
`Sheaf.Paper.SectionReesBaseChangeEtale`. Public definitions, theorem signatures,
public imports and target statements are unchanged. Added proved private helpers
for coefficientwise Laurent and zero-fibre comparisons, augmentation and unit-fibre
naturality, quotient pushouts, and the equal-rank conormal argument.

The affine proofs reuse the proved upstream extended-Rees pushout theorems.
The arbitrary-base-change proof uses the upstream covering theorem and relative
spectrum comparison. The etale proof uses flatness and the Cartesian centre square.
Both proofs use the same explicitly constructed zero and Laurent maps in Compatible.
The normal comparison is obtained by cancellation of pullback squares. Section geometry
and centred coordinates supply the normalized bundle identification and equal ranks.
Updated the existing node's proof, proof_deps and proof_origin accordingly.

The final module compiled with lcompile.py in 14.6 seconds, with no errors or warnings.
The public signatures, definitions and imports were compared with the assigned source.
The updated proof dependencies have no path back to the item node.

## Proved and sorry left

Closed all six original holes:

- `AlgebraicGeometry.SectionReesBaseChange.base_change`
- `AlgebraicGeometry.SectionReesBaseChange.base_change_geometry`
- `AlgebraicGeometry.SectionReesBaseChange.etale`
- `AlgebraicGeometry.SectionReesBaseChange.affine_base_change`
- `AlgebraicGeometry.SectionReesBaseChange.affine_etale`
- `AlgebraicGeometry.SectionReesBaseChange.normal_bundle`

Holes closed: 6. Holes added: 0. Holes left in the item: 0. Statements split off: 0.
The existing centred-coordinate and section-geometry statements remain dependencies;
this delivery does not claim to prove them.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.EtaleReesChart`,
`Sheaf.RingTheory.ReesAssociatedGradedChart`,
`WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec`,
`Mathlib.AlgebraicGeometry.Gluing`, `Mathlib.RingTheory.Flat.Basic`,
`Mathlib.RingTheory.OrzechProperty`, `Mathlib.AlgebraicGeometry.Pullbacks`,
`Mathlib.RingTheory.Etale.Basic`, `Mathlib.RingTheory.TensorProduct.Maps`, and
`Mathlib.AlgebraicGeometry.Morphisms.Flat`.

The node no longer directly invokes `lem-pur-dnc-etale-rees-chart` or
`lem-pur-rees-associated-graded-chart`, and removes their obsolete top-level
`tool_uses` entries. Their modules remain indirect dependencies through
`SectionReesNoetherianGeometry`; no whole-module pruning or withdrawal is claimed.
All adopted upstream declarations and proofs are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned algebra and gluing arguments already
have proved source-library implementations in DeformationSpace.ReesBaseChange,
DeformationSpace.BaseChange and RelativeGluing.BaseChange. Reusing these avoids
rebuilding their proofs from the larger standalone chart statements. The existing
node's reviewed_lean note already observes that these source declarations have no
owning DAG node. The updated proof text names the actual source declarations.

Conormal surjectivity under arbitrary Cartesian base change, followed by the equal-rank
stalk argument, implements the original rank step without choosing bases globally.
For the etale normal-cone isomorphism, quotient pushouts and cancellation of the
Cartesian centre square suffice; no new associated-graded base-change theorem is needed.

The four extra source-library nodes for canonical conormal flat base change, stalk
exactness, finite free stalks and stalk finrank are used as general proved tools.
Their role is only the equal-rank module argument, preserving the unit's geometric route.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
