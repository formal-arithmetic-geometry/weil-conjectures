## What changed

Replaced the sole sorry in AlgebraicGeometry.exists_finite_smooth_modification_of_reduced_curve
with a complete reduction, preserving its signature and public imports. Three proved private
helpers construct the reduced integral component cover, normalize each integral component,
and assemble the finite smooth coproduct. Only dense-open gluing remains, in the new module
Sheaf.AlgebraicGeometry.DenseOpenComponentModifications. Updated the original DAG node to
match this route and added the matching node for the remaining theorem.

The component cover is constructed from vanishing ideals, using the source library's proved
isReduced_subscheme_vanishingIdeal and Mathlib's finite-component enumeration. The integral
normalization proof uses proved source finiteness, dimension preservation, normal stalks and
dense-open isomorphism, rather than importing the unproved bundled NormalizationProperties.
Regularity and smooth_of_isRegular handle dimension at most one directly, so zero-dimensional
components need no separate point-identification lemma. The coproduct finiteness instance
IsFinite.sigmaDesc, source-local smoothness and the dimension bound from its open cover are
all applied in real Lean proofs.

Validation: both final modules compile without warnings through lcompile.py. The delivery
dry run runs the axiom probes and server compile. No library build was run.

## Proved and sorry left

The original declaration AlgebraicGeometry.exists_finite_smooth_modification_of_reduced_curve
now has a complete Lean proof from the single remaining intermediate theorem. Its three
private helpers are proved and contain no sorry.

The only sorry left in this delivery is
AlgebraicGeometry.exists_dense_open_isIso_component_modifications, node
lem-weil-pbc-dense-open-component-modifications, in
lean/Sheaf/AlgebraicGeometry/DenseOpenComponentModifications.lean. Its entire proof is
`by sorry`; its docstring and node contain the full component-open and gluing argument.
The target consequently still depends on this sorry; this is a reduction, not an axiom-free
completion of the target closure.

## No longer needed

Removed imports:
- WeilConjectures.Mathlib.Topology.KrullDimension (second reader removed the redundant
  direct proof import; Regular publicly imports Normalization, which provides it).
- Sheaf.AlgebraicGeometry.FiniteDenseNormalOpen
- Sheaf.AlgebraicGeometry.NormalizationProperties
- Sheaf.AlgebraicGeometry.ZeroDimIntegralPoint
- WeilConjectures.Mathlib.AlgebraicGeometry.Normalization (redundant direct import;
  its proved declarations remain used through Regular's public import).

Pruned proof nodes for this item:
- lem-fin-dense-normal-open: normalization already has a proved nonempty iso-open theorem.
- lem-sc-normalization-properties: use the proved individual source declarations instead.
- lem-weil-pbc-zero-dim-integral-point: regularity handles dimension zero directly.
- lem-weil-pbc-isomorphism-finite: the explicit empty/zero-dimensional identity cases disappear.

The corresponding three Sheaf modules are unnecessary on this branch. This does not assert
that other targets or branches no longer reach them. Closed-immersion finiteness, finite
composition/coproduct, smooth coproduct and finite-over-separated-finite-type remain used.
Normalization, normal stalks and regularity remain used; their modules are not pruned.

## Where the brief, the DAG or earlier work was wrong

No existing statement was changed or disputed. The old plan unnecessarily separated
zero-dimensional components and used an unproved bundle despite the proved source
normalization results. The same normalization/regularity construction works for all integral
components of dimension at most one. No unit route is bypassed: the finite smooth modification
and dense-open reduction of the curve are retained.

Edge cases checked mathematically: the component cover includes n=0; exhaustivity then
forces X empty, and the empty open is dense. The remaining gluing lemma requires distinct
component images: otherwise duplicated summands would break the isomorphism. Intersecting
component opens with complements of other components handles intersecting components.
Dimension-zero components are normal integral points after normalization and the regularity
argument applies without a dimension-one equality. No arbitrary finite smooth cover is
assumed birational; the remaining lemma specifically requires componentwise dense iso-opens.

Searches: LeanFinder found only relative-normalization and scheme gluing APIs; Loogle's
IsClosedImmersion/IsIntegral query returned no match. LeanSearch was attempted twice but
returned Internal Server Error, recorded as unavailable without a verdict. Grep of Mathlib
and the source library located the proved vanishing-ideal reducedness and IsFinite.sigmaDesc,
which are used. Blueprint search found no existing blueprint node for the combined component
dense-open lemma. Local literature .tex files are absent; the supplied original node's proof
and the official [0BAJ](https://stacks.math.columbia.edu/tag/0BAJ) and
[0A3Q](https://stacks.math.columbia.edu/tag/0A3Q) web text were checked for the source route.

## New nodes

lem-weil-pbc-dense-open-component-modifications is the remaining topology/gluing part of
steps 5-6 of the original node. It accepts a finite enumeration of distinct integral component
closed immersions and arbitrary maps that are isomorphisms over dense component opens. It
concludes that their coproduct map is an isomorphism over a dense open of the reduced target.
It has no field, finite-type, smoothness, dimension or finiteness hypotheses. It supplies none
of the component construction, normalization, finite coproduct or smoothness proofs, so it is
strictly part of the target argument rather than a renamed target. No change records needed.


## Second reading by A3

1. Compared the delivered original module with the repository using diff and directly
compared the existing declaration signature before `:=`: byte-for-byte identical.
The public imports and every existing definition are unchanged. The added module contains
one new theorem, and the three new private helpers do not alter the public interface.
No change record is needed. Verdict: pass.

2. Compiled both modules in import order with lcompile.py, without errors or warnings.
Scanned both modules for sorry, axiom, unsafe, opaque, implemented_by, extern and options:
only the reported public dense-open theorem has sorry, as its complete proof.
Compiled scratch copies with #print axioms for all five declarations. Component construction
and integral normalization use only propext, Classical.choice and Quot.sound. Assembly,
the original theorem and the remaining dense-open theorem additionally use sorryAx,
exactly as expected for this open dependency. No data definition or private helper has sorry.
Verdict: a sound reduction; the original theorem's closure is still open.

3. Read the split theorem, its complete docstring argument and its node. Finite distinct
component images cover X. Removing the other components leaves a nonempty open in each
component; its intersection with the chosen dense iso-open is nonempty and contains the
generic point. The inclusion is a surjective closed immersion over that open and hence an
isomorphism because X is reduced. Disjointness excludes every other summand's preimage;
target-local isomorphism then glues. Checked empty X/n=0, n=1, dimension-zero components,
intersecting components, and arbitrary extra source points outside the chosen iso-opens.
Duplicate components are correctly excluded by hinj. There is no need for finite type or
finiteness of the component modifications in this lemma. It supplies only dense-open gluing,
not the normalization, finiteness, smoothness or dimension argument, so it is not a restatement.
Independent Loogle, LeanFinder and launcher grep searches used different queries. Loogle
found isIso_of_isClosedImmersion_of_surjective, an ingredient already cited; grep found
closure_sUnion_irreducibleComponents_sdiff_singleton. The proved library theorem
IsCurve.exists_dense_irreducible_opens supplies related topology under stronger curve
hypotheses, but not the scheme isomorphism assembly. No duplicate of the new statement found.
Checked source discussions at https://stacks.math.columbia.edu/tag/0BAJ and
https://stacks.math.columbia.edu/tag/0A3Q. Verdict: true and strictly part of the argument;
closing the remaining scheme restriction/coproduct gluing is beyond a short repair.

4. Followed the proof from the original theorem through all three helpers. The shortest
available normalization ingredients are used. Scheme.smooth_fromNormalization_comp was
checked but requires dimension exactly one, whereas this argument needs dimension at most
one; its underlying proved regularity theorem is therefore the appropriate route.
Compared all removed old proof_deps with the report. Restored def-weil-irreducible-components,
which the proof still uses and which should never have been pruned. The four actual pruned
nodes are all listed in No longer needed. Removed the redundant direct proof import of
WeilConjectures.Mathlib.Topology.KrullDimension and recompiled successfully. Read
sk-thm-p1.json, including realized: its curve calculation, normalization and dense-open
reduction route remains intact, and no realized node is bypassed. Verdict: pass after repair.

5. Checked the original node changes: only proof, proof_deps and proof_origin change.
The restored component dependency is included in the component-construction step's uses;
proof_deps agrees with the union of step uses. The new node has its matching Lean signature,
source, full proof plan, dependency lists, creation/blueprint/chapter/unit metadata and
search records. Added the independent Loogle search record. Verdict: pass after repair.

Second reading changed: restored the still-used irreducible-components DAG dependency,
removed one redundant proof import, recorded independent searches, and appended this review.
No Lean proof or statement required repair.
