## What changed

Replaced the sorry in `AlgebraicGeometry.ProEtale.spRootBasisTowerComparison`
with an explicit natural transformation from the coefficient tower to the
integral twist tower on the prescribed slice. Its successor squares are proved
on every section: naturality restricts the root-generator compatibility from W,
the specified integral transition is the tensor of its coefficient and root
maps, and lax monoidal tensor naturality identifies the two composites.
`NatTrans.ofOpSequence` supplies all arrows; componentwise invertibility gives
the requested inverse natural isomorphism. The original signature, public
imports, definitions, target statements and unit route are unchanged.

Added the proof-only import `Sheaf.Paper.SpRootBasisLevel`. This new module states
the normalized coefficient-linear basis at a single finite level. It fixes just
one exponent, one root section and one basis; it has no family of roots, no
transition hypothesis and no assertion about diagrams. The original theorem's
entire transition and sequence-assembly argument is outside that remaining hole.
The normalization is needed to use the actual transition maps, rather than
arbitrary underlying abelian-sheaf isomorphisms.

Updated the item's DAG proof and dependencies and added the matching node for
the single-level calculation. No other existing module or node was changed.

Validation: `lcompile.py --all` compiled both modules successfully. The compile
service enforces its 60-second Lean acceptance limit separately from the
reported preparation-inclusive elapsed times. No profiling options remain.

## Proved and sorry left

The original hole in `AlgebraicGeometry.ProEtale.spRootBasisTowerComparison`
(node `lem-sp-root-basis-tower-comparison`) is replaced by a complete Lean proof
from `AlgebraicGeometry.ProEtale.spRootBasisLevel` and the existing declarations.
There are zero sorry bodies left in the item module.

One hole is added and remains:
`AlgebraicGeometry.ProEtale.spRootBasisLevel`, node `lem-sp-root-basis-level`,
in `Sheaf.Paper.SpRootBasisLevel`. Its docstring gives the construction, inverse,
balancing, sheafification and normalization arguments. The section formula
determines the chosen isomorphism uniquely, so this is not an arbitrary
existence witness used to define data.

Counts: one original hole removed, one strictly single-level hole added,
net zero. This is a decomposition, not a fully discharged proof of the item.
No holes are left in definitions and no new axioms are introduced.

## No longer needed

No existing import was removed and no whole module is pruned.
The route no longer uses `lem-route-sp-integral-twist-level-comparison`
(`spIntegralTwistLevel_comparison`): its unnormalized abelian-sheaf isomorphism
cannot supply the specified linear basis. The module containing it remains
needed for the actual finite-level definitions and transition formula, and its
existing theorem is preserved verbatim.

The original finite-discrete coefficient comparisons, integer-tensor argument
and slice-sheafification comparison are localized to the new single-level node.
They remain dependencies there and are not claimed as global pruning.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The old plan's underlying finite-level comparison
does not by itself yield a linear, normalized comparison on the prescribed
slice: its conclusion supplies only a nonempty abelian-sheaf isomorphism.
The normalization must be constructed and retained. The new lemma records that
missing calculation while the tower compatibility is now proved explicitly.

Checked edge cases of the new statement: n=0 still has positive exponent;
empty slices and zero coefficient modules make the formulas and inverse
identities trivial. No residue-characteristic hypothesis is required in this
single-level assertion once the supplied root-module basis exists. No inverse
limit, rational comparison or arbitrary basis-change compatibility is asserted.

## New nodes

`lem-sp-root-basis-level`, in
`dag/nodes/sec-six-functors-basics/lem-sp-root-basis-level.json`, realizes
`AlgebraicGeometry.ProEtale.spRootBasisLevel` in
`lean/Sheaf/Paper/SpRootBasisLevel.lean`. Source: latest blueprint,
`sec-smooth-purity/sk-prop-an/sk-def-sp-tate-twist-locally-free.proof.md`,
clause (3), the finite basis before its transition calculation. It retains the
same chapter, unit and ancestor route. Its three proof steps construct the
finite coefficient comparison, the normalized integer/residue tensor
comparison, and the induced basis on the slice. Searches for a pre-existing
normalized module-sheaf comparison found ordinary module tensor identities and
unnormalized abelian-sheaf comparisons, but no matching declaration.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
