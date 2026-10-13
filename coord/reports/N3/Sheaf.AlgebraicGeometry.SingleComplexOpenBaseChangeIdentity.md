## What changed

Replaced the first worker's `singleComplexOpen_baseChange_identity_existence`,
which repeated the entire item, with a genuine decomposition. The item keeps its
original signature and docstring. Its proof supplies explicitly constructed a
and b and applies the fixed-data compatibility calculation.

New module `Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeComparisons`
constructs `AlgebraicGeometry.singleComplexOpenDirectImageIso` by the sectionwise
underived identification and the proved right-derived-functor comparison APIs,
using preservation of K-injectives by open restriction. This exposes the actual
construction used by the existing `schemeDerivedDirectImage_openRestriction`
existence proof; choosing an unspecified natural isomorphism would not suffice
for the mate calculation. It also constructs
`AlgebraicGeometry.singleComplexOpenBaseChangeSourceIso` from open pullback,
pinned pullback composition, the resLE square and that direct-image comparison.
No data comes from an unproved existence statement.

New module `Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeCalculation`
states only the residual equality for these fixed comparisons. Its import in
the item is private, since it is needed only by the proof. New definitions expose
the imports required by their actual bodies. No existing public import changed.

## Proved and sorry left

Upper hole closed: `AlgebraicGeometry.singleComplexOpen_baseChange_identity`.
Lower hole added: `AlgebraicGeometry.singleComplexOpen_baseChange_calculation`
(node `lem-pc-n3-open-base-change-calculation`), with its complete counit/mate
argument in the docstring. The two comparison definitions have complete Lean
bodies and contain no sorry. The false-progress restatement
`singleComplexOpen_baseChange_identity_existence` and its node were removed.

This is a decomposition, not a completed proof: one original hole closed, one
strictly lower hole added; the balance for delivered declarations is zero.
The pinned sorry ledger remains authoritative for the targets-import-closure net. The upper theorem still depends on sorryAx
through the residual calculation. No claim of a sorry-free target is made.

## No longer needed

No old import or module is pruned. All four old immediate proof dependencies
(`lem-pc-restrict-derived-direct-image-open`,
`lem-pc-ringed-spaces-derived-pullback-composition`,
`def-pc-single-complex-open-restriction-data`,
`def-pc-derived-base-change-map`) are replaced in the item's proof_deps by the
explicit comparison-data and residual-calculation nodes; these old dependencies
remain used by the lower construction/calculation except
`lem-pc-restrict-derived-direct-image-open`: its Nonempty conclusion is not
called by the new route; instead the sectionwise construction itself is exposed
and K-injective preservation is used directly. That node and its module
`Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction` are no longer needed
by this item's route (whether other targets reach them is for the queue to
compute). It was not an import of the original item, so no actual module-pruning
claim is made. The rejected sandbox-only
`SingleComplexOpenBaseChangeIdentityExistence` module and `new-open-bc-existence`
node are absent from the delivery.

## Where the brief, the DAG or earlier work was wrong

The first worker's split-off lemma had the same hypotheses and full conclusion
as the original item, including the base-change equality. Its report inaccurately
called this only existence of the comparison maps and said the target retained
a sorry. Its node omitted the equality from its statement and its proof did not
cover it; its Lean record used an ellipsis instead of the signature. Removing
that restatement was necessary even though the file compiled. The repaired
lower theorem pins both comparison maps to real constructions and records the
remaining compatibility argument.

## New nodes

`def-pc-n3-open-base-change-comparisons` records the two explicit comparison
constructions. They expose canonical data required by the residual equality;
the existing Nonempty theorem exposes no chosen map or factorization equation.

`lem-pc-n3-open-base-change-calculation` records the fixed-data mate equality,
strictly the calculation step of the old plan. There is no new change record:
all existing signatures, definitions and public imports are unchanged.

## Second reading by N3

1. Compared the item with the repository using diff and parsed its declarations.
The existing signature and docstring are byte-for-byte unchanged. There are no
existing definition changes, public-import changes, or forced adaptations.
Verdict: unchanged interface.

2. Read every proof and construction. The original restatement compiled, but
its sole hole was definitionally the whole original claim and was rejected.
The repaired item introduces explicit witnesses. Both new definitions are real
constructions, not arbitrary choices from an unproved existence assertion. The
only new sorry is the named residual calculation, with its source, full proof
in words, and matching node. Compilation and axiom checks are recorded below.

3. Read the new statements against Stacks Tags
[08FE](https://stacks.math.columbia.edu/tag/08FE),
[08HY](https://stacks.math.columbia.edu/tag/08HY), and
[0DJ9](https://stacks.math.columbia.edu/tag/0DJ9), together with
[08BS](https://stacks.math.columbia.edu/tag/08BS) and
[0D5S](https://stacks.math.columbia.edu/tag/0D5S), fetched during this reading
because the cited local tex files are absent on this machine. The explicit
comparison is the sectionwise identification of Tag 08FE; the residual equation
is its counit compatibility for the construction of Tag 08HY. Checked empty
opens, zero coefficients, identity maps, and unbounded complexes: no extra
hypothesis is needed. The residual statement has fixed comparison data and
contains no existential claim, so it is strictly the calculation portion of
the old argument. Three search kinds were attempted; LeanSearch was unavailable.
LeanFinder/Loogle found general mate/derived-adjunction APIs, and rg on the
project and upstream found no existing fixed-comparison identity. The existing
open direct-image theorem asserts Nonempty only and cannot pin a map by its type.
Verdict: sourced and genuine decomposition, one remaining lower hole.

4. Read the old dependencies and the unit record
`dag/units/sk-thm-picard-semicon.json`. The unit has empty realized arrays already;
this subordinate item is not its key node, and changes none of its route or
bindings. The old direct-image/open-pullback calculation is retained, with
explicit data and the residual equality separated. No public import was removed
and no module is pruned; the four replaced immediate DAG dependencies are listed
above; the Nonempty-only direct-image node is bypassed by exposing its actual
construction, and the other old dependencies remain lower dependencies.
Verdict: route retained below the unit level.

5. Checked the three delivered nodes against their declarations. The original
node changes only proof/proof_deps/proof_origin; its statement and lean signature
stay intact. New records have full verbatim signatures, sources, search results,
created/blueprint/unit/chapter data, and proof dependencies equal to the union
of their steps. The fixed equality is fully present in the new node, unlike the
first worker's node. Verdict: metadata agrees with the repaired decomposition.

Second reading changed: removed the whole-statement restatement and its node;
constructed the comparison maps explicitly; introduced the fixed-data residual
calculation; rewrote the item proof, new metadata, and the inaccurate report.

Validation: all three repaired modules compiled locally. The final dry run
passed preflight as CODEX (commit 2c9c965e2c, nothing pushed), with no compiler
warnings after adding the explanatory instance-budget comment. An independent
scratch-copy #print axioms check then compiled successfully: both comparison
definitions use only propext, Classical.choice and Quot.sound; the residual
calculation and the original item additionally use sorryAx, exactly through the
single documented remaining hole. Delivery's all-declaration axiom probe also
passed. No axiom/unsafe/opaque/implemented_by/extern escape was introduced.
