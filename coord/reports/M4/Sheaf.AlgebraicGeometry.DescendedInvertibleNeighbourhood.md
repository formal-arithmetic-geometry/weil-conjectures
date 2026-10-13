## What changed

Proved `AlgebraicGeometry.Scheme.exists_descendedInvertible_neighbourhood` with its
original signature and visibility. Added proof-only imports of
`WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine` (finite local frames)
and `Mathlib.AlgebraicGeometry.Properties` (nontrivial sections on nonempty opens).
All original public imports are retained for the existing statement interface.
Three fully proved private helpers compare the two pullbacks by uniqueness of left
adjoints, deduce nonempty source from an invertible structure adjunction unit, and
compare a finite local frame with an invertible pullback near a specified source point.
The comparison uses global sections on a nonempty trivializing open and the strong
rank condition; no stalk-base-change or fibre-rank comparison theorem is required.
Updated the existing node's proof, proof_deps and proof_origin to this argument.
The unit `sk-prop-av-cube` has no realized nodes in its statement or sole step;
its theorem-of-the-cube route is unchanged by this local argument.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.exists_descendedInvertible_neighbourhood`
(node `lem-sc-descended-invertible-neighbourhood`).
No `sorry` remains in the item. No holes or new modules were added.
The private helpers are proved in full, including the rank calculation and all
restriction and cartesian projection comparisons.

## No longer needed

`lem-sc-field-pullback-rank-one-trivial` and its module
`Sheaf.AlgebraicGeometry.FieldPullbackRankOneTrivial` are no longer dependencies of
this item's proof. We calculate rank directly on a nonempty open above w instead
of first descending to Spec kappa(w). The removed DAG proof dependency
`def-amb-finite-locally-free-module` is replaced by the correct variable-rank notion
`def-sc-finite-locally-free-sheaf`; the original declaration's finite-locally-free
public import remains needed for its unchanged signature.
No source imports were removed: the field lemma was not yet imported in the
original module. `Sheaf.AlgebraicGeometry.BaseChangeConventions` is not imported:
only the primitive pullback object, lift and its projection identities are needed.
The base-change definition node remains in proof_deps for this mathematical role.
No claim is made that these modules are unreachable from every other target route.

## Where the brief, the DAG or earlier work was wrong

The original step 2 required a residue-field pullback and a field-rank theorem.
Those comparisons are unnecessary: after restricting the finite free frame to an
invertible trivializing open, its nonzero global-sections ring has the strong rank
condition. The proof writes both section isomorphisms explicitly.
The original finite-locally-free dependency names the constant-rank predicate,
while the hypothesis uses variable-rank finite local freeness. The revised proof
dependency names the correct existing definition node; no statement was changed.
The literature payload is absent from this read-only clone, including the unit's
_section.md file. The unit record and the supplied proof sketches were available
and read; this delivery uses their rank-one local-frame argument.
Small cases: the residue-spectrum point excludes an empty base; an empty source
contradicts the adjunction-unit hypothesis; a rank-zero frame is excluded by the
rank comparison; and an empty subopen U is allowed in the final pullback composition.
No forced adaptations, changes to definitions or changes to theorem statements.

## Second reading by M4

1. Compared the delivered module with the repository version. The theorem signature and visibility are unchanged; only the author line, proof imports, private helpers, proof, and DAG proof metadata differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or warnings. The item contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition. Verdict: pass.
3. Checked the proof route and declarations against the imported library and searched for existing alternatives. The private helpers are fully proved and the route uses existing pullback, finite-local-free, invertibility, and global-sections declarations. No split-off statements or new nodes were added. Verdict: pass.
4. Checked pruning and imports. The residue-field rank-one lemma is no longer used; the remaining imports are required by the statement or proof. The unit route is retained and no unit step is bypassed. Verdict: pass.
5. Compared the DAG node with the Lean proof. The theorem statement remains byte-for-byte unchanged; proof steps, dependencies, origin, and realized-route note match the implementation. Verdict: pass.

Changed only the proof implementation and proof metadata as described above; no statement or definition was changed.
