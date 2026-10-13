## What changed

Proved `AlgebraicGeometry.exists_tensorHomUncurry_descent_extension` in
`Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentExtension`, preserving its
signature and visibility. Added proved private transport and orbit-extension helpers.
The family chooses the unique transported normalized output when one exists and is
zero otherwise. Uniqueness is proved before making this choice; no data are chosen
from an unproved mere-existence theorem. Normalized comparison supplies precisely
the consistency needed. Updated the node proof to match this shorter route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_tensorHomUncurry_descent_extension`
(node `lem-pc-tensor-hom-uncurry-descent-extension`). No holes added or split off;
no `sorry` remains in the delivered module. The proof uses the existing
`AlgebraicGeometry.tensorHomUncurry_normalized_comparison`, whose imported proof
ultimately depends on the existing evaluation-naturality statement. This delivery
claims the extension proof, not closure of those transitive dependencies.

## No longer needed

Removed direct proof imports:
- `Sheaf.Algebra.Homology.HomComplexGlobalCochains`
  (`lem-pur-hom-complex-global-cochains`).
- `Sheaf.Algebra.Homology.KFlatResolution` (`lem-pc-kflat-resolution`).
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`
  (`lem-pur-hom-kflat-into-kinjective`).

The extension proof also no longer directly needs
`lem-weil-pbc-kinjective-hom-derived` or
`lem-pc-tensor-hom-uncurry-differential` as proof steps. The differential module
remains publicly imported because the statement uses its constructed chain map.
These are local dependency removals: no claim is made that these modules are
unreachable from every other target or from normalized comparison's dependencies.
Added only the proof import
`Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison`.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The old proof plan constructs representatives for every
input, but the conclusion only requires agreement on normalized inputs and
isomorphism compatibility. Extending over their isomorphism orbits, with zero on
the invariant complement, suffices. The unit record has no realized statement or
steps for this node, and its route is preserved. The original docstring describes
the representative plan; the delivered DAG and this report describe the actual
orbit construction. Identity and inverse transports are proved explicitly; the
empty index case and all inputs outside normalized orbits use zero, so no
nonemptiness, boundedness, or chain lifting assumption is hidden.

## Second reading by A3

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are unchanged byte for byte; only proof-local helpers, proof imports, and the theorem proof changed. Verdict: pass.
2. Compiled the module with `lcompile.py`; it is error-free and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The orbit construction is a genuine definition and chooses data only after proving uniqueness. `#print axioms AlgebraicGeometry.exists_tensorHomUncurry_descent_extension` reports exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the last is inherited from the existing open imported dependencies already disclosed above. Verdict: pass.
3. Checked the split-off DAG node and searched the library for duplicate declarations. No new split-off theorem was added; the existing node records the actual normalized-comparison and orbit-extension route. Verdict: pass.
4. Read the proof top-down. It uses normalized comparison, then a short transport-orbit construction, and removes the three obsolete proof-only imports. No shorter existing declaration was found. Verdict: pass.
5. The node proof, proof dependencies, and proof origin match the Lean proof; the unit route is preserved because the unit has no realized statement or step for this node. Verdict: pass.

Changed in this second reading: no mathematical or interface changes; this report section records the audit only.
