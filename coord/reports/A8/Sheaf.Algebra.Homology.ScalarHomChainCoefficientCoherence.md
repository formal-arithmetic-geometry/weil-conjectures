## What changed

Proved `SheafOfModules.StrictScalarHom.exists_scalarHomChainCoefficientCoherence`
in `Sheaf.Algebra.Homology.ScalarHomChainCoefficientCoherence`.

The proof first shows that the supplied generator normalizations determine the
coefficient maps uniquely. It transfers the already proved coefficient-square
construction and its four compatibility equations to the supplied family.
Extension units and composition comparisons are constructed by uniqueness of
left adjoints, with their pure-section formulas deduced from the adjunction unit.
Restriction comparisons are componentwise identities. Tensor unit comparisons
are transported through nu. All identity, associativity, square-pasting and
Hom-iteration equations are proved on local tensor generators and every product
Hom coordinate, including arbitrary compatible target maps.

Proof-only imports provide the existing private normalized constructions and
Mathlib's uniqueness-of-adjoints API. The DAG records the reused normalized
coefficient-square theorem and the adjunction construction. Its eleven unit
steps are retained. No source-library file is changed, no new module is added,
and no consumer adaptation is required. To bring the complete proof under the
compiler limit, the definition repair shares the 24 large equation types as
transparent law definitions and derives the five redundant associator inverse
fields as proved theorems under their original getter names. Their mathematical
content is unchanged. The complete definition and local proof-command change record
is `coord/changes/scalar-hom-coefficient-proof-commands.md`.

Validation: the complete proof compiled cleanly in 49.8 seconds, with zero
holes and no warnings, after adjunction constructions were kept abstract behind
their unit API. The unused direct tower import was then removed. The delivery
tool checks the final packet, including its axioms and definition repair.

## Proved and sorry left

Closed the sole original hole:
`SheafOfModules.StrictScalarHom.exists_scalarHomChainCoefficientCoherence`
(node `lem-sfb-scalar-hom-chain-coefficient-coherence`).

Holes closed: 1 of 1. Holes added: 0. Sorries remaining in the item: 0.
No statements are split off and no definitions contain holes.

## No longer needed

Removed the original direct proof import
`Mathlib.LinearAlgebra.TensorProduct.Defs`; the public dependencies already
supply its notation. The construction does not need a direct import of
`Sheaf.Paper.ScalarExtensionDualTowerCore`, tried during development: its tower
isomorphism is replaced here by uniqueness of left adjoints. The existing
coefficient-square theorem internally retains its own proved tower dependency.
Consequently no upstream declaration, node, or module is withdrawn.

All eight original proof dependencies remain needed. The additional direct
proof dependency is the already proved
`lem-sfb-hom-scalar-chain-identification`. No unit statement or step is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The five stored inverse proof
fields duplicate consequences of the retained forward formulas. Turning them
into proved theorems preserves those consequences and reduces constructor
checking. The record repair is fully recorded for independent definition review.
No downstream Lean module imports the item; the DAG parents remain attached.

The existing proved normalized
coefficient-square theorem already supplies the four equations of steps 2--7;
uniqueness of the supplied normalizations makes them available for this input.
Step 8 can use uniqueness of the ordinary scalar left adjoints rather than
reconstructing their isomorphisms through sheafification. The prescribed
normalized formulas, unit laws and associativity laws are still proved.

Several earlier compile requests received no answer from the busy service, and
the earlier delivery attempt stopped before pushing for that reason. Some
complete-file versions exceeded 60 seconds. Prefix checks isolated repeated
large record types and an adapter conversion hidden by local irreducibility;
the adapter is now checked with that comparison definition opened locally.
No compiler limit, launcher file, or safety metadata was modified.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
