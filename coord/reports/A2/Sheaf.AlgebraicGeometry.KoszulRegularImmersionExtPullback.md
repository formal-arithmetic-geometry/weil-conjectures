## What changed

Replaced the sole hole in `AlgebraicGeometry.koszulRegularImmersion_ext_pullback`
with a compiling composition of the rank-support adjunction-unit isomorphism and
pushforward of the determinant comparison on the rank-q open. Its signature,
universes, existing docstring, and all public imports are unchanged.

Added three modules and matching nodes:
- `Sheaf.AlgebraicGeometry.KoszulExtOffRankStalk`: the off-rank local vanishing calculation.
- `Sheaf.AlgebraicGeometry.KoszulExtRankSupport`: a proved reconstruction theorem from that vanishing.
- `Sheaf.AlgebraicGeometry.KoszulExtConstantRankTop`: the top-degree determinant comparison on an open.

The support theorem has a fully proved private helper: restriction of the open-adjunction
unit is invertible by the triangle identity; inside the open its stalk maps are bijective,
and outside the closed open both stalks are zero. Stalk detection gives the isomorphism.
The main proof computes the rank on the selected stratum from hr, converts q.toNat back
to q, and composes actual isomorphisms. No object is chosen from an arbitrary unproved
existence theorem to define data. The only isomorphism chosen is a proof-local witness.

The original node's proof/proof_deps now describe this composition. The new nodes retain
the affine Koszul computation, comparison, and localization/gluing arguments as explicit
proof plans. All four modules compile in dependency order with lcompile.py.

## Proved and sorry left

Closed: `AlgebraicGeometry.koszulRegularImmersion_ext_pullback`
(node `lem-sc-koszul-regular-immersion-ext-pullback`), the only original hole.

New proved public theorem: `AlgebraicGeometry.koszulRegularImmersion_ext_rankSupport`
(node `lem-sc-koszul-ext-rank-support`). Its private helper
`AlgebraicGeometry.isIso_rankSupport_unit` is also proved without a hole.

Added and left exactly two holes, each the entire proof of a named public theorem:
- `AlgebraicGeometry.koszulRegularImmersion_ext_offRank_stalk`
  (node `lem-sc-koszul-ext-off-rank-stalk`).
- `AlgebraicGeometry.koszulRegularImmersion_ext_constantRank_top`
  (node `lem-sc-koszul-ext-constant-rank-top`).

This delivery is a decomposition, not a complete Koszul Ext proof: one original hole
closed and two strictly smaller holes added, so its direct net is -1. The first component
only asserts off-degree vanishing of a single stalk and includes negative degrees. The
second only computes the top cohomology on an open of constant conormal rank, assuming
regularity and the rank equality only on that open. Neither supplies the entire varying-rank
sheaf formula. The support/gluing-to-the-rank-stratum argument between them is proved.

Edge cases checked in the statements and natural-language arguments: empty source, empty
constant-rank open, empty rank-q stratum, n=q=0 with the empty regular sequence, negative
degree in the vanishing theorem, and unbounded/nonconstant rank on the whole source.
There are no new Noetherian, quasi-separatedness, or global rank-bound hypotheses.

## No longer needed

Removed these six direct proof imports from the assigned module:
- `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`
- `Sheaf.AlgebraicGeometry.KoszulRegularClosedImmersionPerfect`
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`
- `Sheaf.RingTheory.KoszulRegularSequenceDualComplex`
- `Sheaf.RingTheory.KoszulConormalBasis`
- `Sheaf.AlgebraicGeometry.AffineConormalFrame`

The five imports other than `KoszulRegularClosedImmersionPerfect` are still needed by the
new local-calculation components, whose modules import them and whose nodes name them.
They are not claimed as globally pruned. The whole-scheme perfectness theorem
`lem-sc-koszul-regular-closed-immersion-perfect` and its module
`Sheaf.AlgebraicGeometry.KoszulRegularClosedImmersionPerfect` are no longer needed on
this route. The local quotient augmentation from the dual Koszul module and
`lem-sc-affine-quotient-resolution-sheafification`
(`Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`) suffice for the chart
resolution. Other callers may still need the perfectness theorem.

No blueprint unit statement or realized step is bypassed. The unit record
`sk-thm-picard-duality` was read and left unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned global perfectness dependency requires regular charts at every point of Y
and local derived-category instances at the chosen universe. Our hypotheses give charts
only near Z. Its affine-resolution part is relevant, but its global conclusion should not
be applied directly. The new plans use its already stated local sheafification dependency
and the quotient augmentation instead; no interface correction or forced adaptation is made.

The existing comparison lemmas do not directly identify the specified derived sheaf Hom
with the affine associated dual complex or glue its top-degree conormal comparison.
These two local calculation conclusions are recorded in the new nodes rather than hidden
in a partial proof. Existing algebraic dual Koszul lemmas are reusable and are retained.

The literature files are not present in this machine's read-only repository. The source
was read at https://stacks.math.columbia.edu/tag/0BQZ (lemma-regular-immersion-ext), including
its separation of off-degree vanishing and the top-degree comparison. LeanSearch returned
Internal Server Error; its searches are recorded as unavailable, not as evidence of absence.
LeanFinder, Loogle, Mathlib grep, repository searches, and blueprint searches were run.

## New nodes

`lem-sc-koszul-ext-off-rank-stalk` in
`dag/nodes/sec-picard-framework/lem-sc-koszul-ext-off-rank-stalk.json`: the single-stalk
vanishing part of the dual Koszul computation, with full local proof and source in its docstring.

`lem-sc-koszul-ext-rank-support` in
`dag/nodes/sec-picard-framework/lem-sc-koszul-ext-rank-support.json`: proved reconstruction
from the matching clopen rank stratum, using the preceding vanishing, the open adjunction,
closed pushforward stalks, and the existing stalk isomorphism criteria.

`lem-sc-koszul-ext-constant-rank-top` in
`dag/nodes/sec-picard-framework/lem-sc-koszul-ext-constant-rank-top.json`: the local top-degree
determinant comparison and normalized overlap compatibility. Its assumptions concern only
points of the selected constant-rank open, independently of the global rank function.

No change record is required: no existing statement, definition, or public visibility changes.

## Second reading by A2

1. **Statements unchanged.** Compared the delivered item module against the repository version. The existing theorem signature is byte-for-byte unchanged; the three added public theorem signatures are recorded verbatim in their DAG nodes.
2. **Proof and axioms.** Compiled all four modules with `lcompile.py --all`; the only remaining `sorry`s are the two named split-off theorems. No forbidden declarations or `sorry` in definitions occur. The proved support helper and target proof use only the permitted proof route.
3. **Split statements.** Checked the off-rank stalk and constant-rank top statements against the Stacks Tag 0BQZ calculation and their edge cases (empty source/open, degree zero, negative degree). They are strictly smaller than the target and carry complete source/docstring proofs and matching nodes.
4. **Pruning and route.** Verified the target proof uses the rank-support and constant-rank-top modules, and that the old perfectness import is no longer needed on this route. The unit `sk-thm-picard-duality` and its realized target step remain in use.
5. **DAG agreement.** Compared each node's Lean declaration, proof dependencies, proof origin, status, chapter, and unit with the delivered files. They agree; no statement or definition change record is required.

I changed only the report by adding this second-reading section. The Lean proofs and split-off statements required no repair after compilation, and the dry-run preflight now has the required review record.
