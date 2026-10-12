## What changed

The item now uses strong induction on finite affine covers. Three strictly smaller argument
pieces are stated in separate modules: affine supported detection,
gluing across one affine chart, and triangulated closure of the supported quasi-coherent
property. The item's proof is a complete Lean reduction to these three statements and the
existing Koszul/open-support infrastructure; the three new statements remain named `sorry`
holes for subsequent workers. Proof-only imports were reduced to the modules used by this
reduction.

## Proved and sorry left

The declaration `AlgebraicGeometry.supported_perfect_generator` is reduced to the three
strictly simpler named statements below. The following declarations are intentionally left as
`sorry`, each with its own node:

- `AlgebraicGeometry.supported_perfect_detector_affine`
  (`lem-pc-supported-perfect-detector-affine`);
- `AlgebraicGeometry.supported_perfect_detector_gluing`
  (`lem-pc-supported-perfect-detector-gluing`);
- `AlgebraicGeometry.supported_qcoh_isTriangulated`
  (`lem-pc-supported-qcoh-triangulated`).

The main theorem's final implication from `IsZero` to subsingleton Hom groups is proved
explicitly with `IsZero.eq_of_tgt`; the reverse implication is supplied by the detector
reduction.

## No longer needed

The original module's direct imports of `PerfectSupportedMapLift`, `SupportedOpenPushforward`,
`KoszulOpenOrthogonality`, `DerivedDirectImageOpenRestriction`,
`RingedSpaceDerivedDirectImageComposition`, `OpenRestrictionAdjunctionExact`, and
`WeakTriangulatedGenerator` are no longer needed directly by the item's theorem body. The six geometric proof modules
remain dependencies of the affine/gluing split statements. `WeakTriangulatedGenerator`
is not used by this reduction; zero detection is expressed directly in the existing signature.

All eight old `proof_deps` entries are removed from the top node:
`lem-pc-perfect-generation-koszul-orthogonal`, `def-pc-generators`,
`lem-sc-perfect-support-map-lift`, `lem-pc-supported-open-pushforward`,
`lem-sc-derived-open-restriction-adjunction-exact`,
`lem-pc-ringed-spaces-derived-direct-image-composition`,
`lem-pc-restrict-derived-direct-image-open`, and `def-weil-triangulated-category`.
The six lemma nodes still occur below the affine/gluing nodes. The two definition nodes
remain statement dependencies, rather than proof dependencies. No globally unreachable
module is claimed as pruned.

The second reader also removed the unused public import
`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` from both new detector modules;
it is needed only in the main module's proof.

## Where the brief, the DAG or earlier work was wrong

The original item was too large to encode as one direct proof in the available interfaces:
its affine Koszul construction, finite-cover induction, and stalkwise triangulated closure
were not themselves available as proved declarations. The reduction makes these three
missing arguments explicit and keeps the target statement unchanged. The gluing node is
formulated with a strong induction hypothesis for strictly smaller covers, which handles the
empty and one-chart edge cases without assuming a generator for an unrelated category.

## New nodes

`lem-pc-supported-perfect-detector-affine` is stated in
`lean/Sheaf/AlgebraicGeometry/SupportedPerfectDetectorAffine.lean`. It handles only covers of
cardinality at most one, not general qcqs schemes. Its docstring constructs the Koszul object
rather than selecting arbitrary data from an unproved existence statement.

`lem-pc-supported-perfect-detector-gluing` is stated in
`lean/Sheaf/AlgebraicGeometry/SupportedPerfectDetectorGluing.lean`. It handles one induction
step under a hypothesis quantified over strictly smaller finite affine covers. Its proof
follows Tag 0A9A's supported lifting and Koszul pushforward argument.

`lem-pc-supported-qcoh-triangulated` is stated in
`lean/Sheaf/AlgebraicGeometry/SupportedQCohTriangulated.lean`. It is the independent closure
assertion, with no perfect generator and no compactness or closedness hypotheses.

All four modules compile together in import order. One upper hole was closed and three holes
were added, so this is a decomposition with net hole change +2, not a completed proof of the
supported-generator theorem. Edge cases checked against the source: empty X/empty cover,
zero ring affine charts, T empty, T = X, redundant charts, and unbounded cohomology. No data
definition or existing statement signature changed. LeanSearch was unavailable; LeanFinder
and source grep found no replacement for these three statements. Source read:
Stacks perfect.tex, label lemma-generator-with-support, from the local review copy.


## Second reading by P3

1. **Unchanged visible declarations: PASS.** Compared the main module by `diff` and
   checked the existing theorem signature byte for byte by extraction up to `:= by`.
   Only its proof and private imports change. No existing definition changes, no new data
   definition is introduced, and no change record is needed. Removed an unused public
   Mathlib import from each new detector module.
2. **Lean proof and axioms: PASS.** All four modules compile locally in import order.
   The main theorem has no `sorry`; exactly the three reported public named theorems
   retain `:= by sorry`. No forbidden declarations or implementation attributes occur.
   Explicit scratch `#print axioms` checks and the delivery axiom probe allow only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from the open dependencies.
   The induction really supplies the smaller-cover hypothesis; the final forward
   implication uses `IsZero.eq_of_tgt` and introduces no additional hole.
3. **Split statements: PASS as decomposition.** Read the three statements, their
   docstring proofs, the existing map-lift/Koszul/pushforward declarations, and the proof
   of `lemma-generator-with-support` in the local source `/tmp/perfect.tex`.
   Affine detection is confined to at most one chart; gluing assumes detection only for
   strictly fewer charts; closure states only the first conjunct and allows arbitrary T.
   None restates the full item. Empty cover/empty scheme, zero ring, empty/full T,
   redundant charts, negative shifts and unbounded complexes cause no counterexample.
   The remaining charts lie inside their union, so they stay affine on that open
   subscheme and give a strictly smaller cover even when some coincide after restriction.
   The Koszul object is an actual construction in the proposed proof, and no arbitrary
   witness of an unproved existence theorem is used in a data definition.
   Independent LeanFinder searches used “Serre subcategory sheaves zero stalks” and
   “finite generators common vanishing locus”; Loogle and grep also found no exact
   replacement. The upstream `homologyProperty_isTriangulated` requires closure instances
   for quasi-coherent supported module sheaves that are not currently available; it does
   not close this hole by immediate application. No split hole could be closed in a
   short bounded pass.
4. **Top-down route and pruning: PASS after report repair.** The main proof performs
   finite-cover strong induction and combines its detector with the separate closure
   assertion. It keeps the affine Koszul and one-chart supported lifting route of Tag
   0A9A. `dag/units/sk-thm-picard-duality.json` has empty `realized` entries; no unit
   realization or chapter route is bypassed. The report now lists every removed old
   proof dependency and distinguishes these from dependencies still needed below the
   split nodes. No globally pruned module is asserted.
5. **DAG agreement: PASS.** The top node's three proof dependencies match the three
   lemmas applied in Lean; its proof describes the actual induction and Hom implication.
   The new nodes have source, complete proof plan, dependency union, search records,
   creation metadata, blueprint ancestry, chapter/unit and Lean records. Their recorded
   Lean statements have been made verbatim copies of their multiline signatures.

Changes by the second reader: removed two unused public imports, made the three new node
signature records verbatim, completed the pruning/dependency report, and added this review.
The mathematical proof reduction is unchanged. This closes the upper syntactic hole
`AlgebraicGeometry.supported_perfect_generator` and adds the three holes listed above:
one closed, three added, net -2 holes closed; decomposition, not an axiom-free proof.
