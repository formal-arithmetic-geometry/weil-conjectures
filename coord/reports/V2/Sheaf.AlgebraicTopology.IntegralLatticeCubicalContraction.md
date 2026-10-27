## What changed

Proved `IntegralLatticeCubical.contraction` from the existing, now proved DAG lemmas
`boundary_coordinate_projections` and `signedCoordinateHomotopy`. The explicit total
homotopy is the recursive finite sum H(i::L)=H_i+p_i H(L). List induction proves
its identity with 1-P(L), and the full coordinate product is the origin projection.
The contraction gives kernel equals image in positive degree and at the augmentation;
the section gives augmentation surjectivity. Rank zero uses the empty list.

Moved the ten unchanged chain definitions to the new shared module
`Sheaf.AlgebraicTopology.IntegralLatticeCubicalDefs`, publicly reexported by the item.
Changed the public definition import in the two coordinate modules to that module.
All their declarations, complete proofs and other imports remain verbatim. This removes
the import cycles that otherwise prevent applying the two planned lemmas.
The item theorem's signature and all ten moved definition bodies are unchanged.
See `coord/changes/V2-integral-lattice-cubical-definitions.md`.

## Proved and sorry left

Closed one of one assigned holes: `IntegralLatticeCubical.contraction`
(node `lem-sfb-integral-lattice-cubical-contraction`). Added zero holes and split off
zero proof statements. No delivered module contains a remaining sorry.
The two coordinate lemmas were already completely proved in the current shared source;
this delivery preserves their proofs and changes only their definition import.

## No longer needed

No mathematical dependency module is pruned: both planned coordinate lemmas are used.
`def-weil-pbc-module-chain-complex-homology` is no longer a proof dependency:
the theorem already states exactness as range equals kernel, proved directly.
It remains a statement dependency. Both coordinate modules no longer import the
contraction theorem, using its unchanged definitions through the shared module instead.
No declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The correct two coordinate lemmas were stated in modules importing the parent theorem's
module for its definitions. This prevented the intended reverse proof imports.
Extracting and reexporting the definitions repairs that interface without changing
any construction or theorem signature. The two coordinate projections have different
names but definitionally identical bodies. Equality induction handles the integer-degree
transports; no new axiom or intermediate theorem is needed.
The list recurrence is the planned finite telescoping sum. The unit route is preserved.
The new definition node records only relocation of existing explicit constructions.

## New nodes

`def-sfb-integral-lattice-cubical-chains` records the ten existing chain definitions
relocated verbatim to `IntegralLatticeCubicalDefs`; it introduces no proof hole.
The parent Lean attachment now records only the contraction theorem. Change record:
`coord/changes/V2-integral-lattice-cubical-definitions.md`.

The current blueprint direct-images proof, paragraph (3), and the unit realization
record were read; this algebraic input retains that route. Fresh LeanFinder, LeanSearch,
Loogle and source searches found only abstract simplicial or homotopy machinery,
not a shorter result for these cubical chain objects. The blueprint duplicate search
found no node for the extracted definitions; its inherited blueprint ancestor is null.

Validation: the four-module import repair compiled as an acyclic set during development;
the completed contraction compiled in 3.8 seconds. Text comparisons confirm the theorem
signature and all moved definition bodies/docstrings are unchanged. Both dependency
sources differ from current shared source only in their single public import line.
All four delivered modules contain zero sorry tokens and respect the 100-character limit.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
