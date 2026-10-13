## What changed

The unchanged target `AlgebraicGeometry.SingleComplexBaseChange.affineSpectrum_counit_square`
is now proved directly from `affineSpectrum_composition_counit_square`. The exact
iso-pullback complex counit components are normalized to the pinned derived counits by
unfolding the quotient identity comparisons. The resulting square is inverted by categorical
cancellation. The proof-only representative-map import is replaced by the composition-counit
import. The public imports, original declaration signature, definitions, and docstring remain
unchanged. Local reducibility attributes and a declaration-scoped heartbeat allowance support
normalization; see `coord/changes/affineSpectrumCounitSquare-proof-route.md`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.SingleComplexBaseChange.affineSpectrum_counit_square`
(node `lem-pc-affine-spectrum-counit-square`). Added no holes. No sorry remains in the module.
The first worker's `affineSpectrum_counit_square_postcomp` and its proposed node were removed.
The scratch-copy `#print axioms` audit reports exactly `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx`. This is one hole closed and zero added.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.AffineSpectrumRepresentativeMap` and proof
node dependency `lem-pc-affine-spectrum-representative-map`. All other old proof dependencies
remain used. Added the existing composition-counit node to the proof dependencies. Whether the
representative-map module becomes globally unreachable is for the maintainer's import closure
and ledger to decide.

## Where the brief, the DAG or earlier work was wrong

The first worker split off the same target equation after postcomposition by an isomorphism.
That was an equivalent obligation rather than a genuinely smaller mathematical step, and its
new node lacked valid metadata. The second reading removed the split and proved the actual
composition-counit reduction. The initial report also failed to list the removed
representative-map import. The DAG now records the implemented route.

## Second reading by A2

1. Compared the delivered module with the repository. The sole existing declaration's
signature is byte-for-byte unchanged. No definition, public import, or target statement changed.
2. Compiled through lcompile.py. The final proof contains no sorry or forbidden declaration.
The cancellation uses isomorphisms supplied by the two hypotheses and the canonical comparison;
no arbitrary data is chosen from an unproved existence theorem.
3. Removed the proposed equivalent split theorem and node. No new statement or hole remains.
The existing composition-counit theorem is precisely the available square needed here.
4. The proof uses the shorter existing composition-counit route. Both public imports are
needed for names in the target signature. The representative-map proof import is pruned.
The unit `sk-thm-picard-semicon` has `realized.statement = []` and `realized.steps = [[]]`;
this below-unit replacement does not change its statement or route.
5. Updated the original node's proof, proof_deps and proof_origin to the implemented
normalization and cancellation. All other fields and the unit record stay unchanged.

Changed the second-reader proof, removed the redundant split, repaired the report and DAG,
and scoped the heartbeat allowance. The change record is
`coord/changes/affineSpectrumCounitSquare-proof-route.md`.
