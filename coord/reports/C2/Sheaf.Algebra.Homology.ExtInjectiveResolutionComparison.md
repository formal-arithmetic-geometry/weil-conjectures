## What changed

Proved `ModuleCat.nonempty_ext_iso_injectiveResolution_homology` with its original
statement and `homComplexDiagram` definition unchanged. Added one proof-only import,
`Sheaf.Algebra.Homology.ExtInjectiveEdgeQuasiIso`.

Added `Sheaf.Algebra.Homology.ExtResolutionDoubleComplex`: a concrete first-quadrant
Hom total complex, its two explicit edge maps, precomposition maps and their commuting
squares, and the proved projective-edge quasi-isomorphism. Added
`Sheaf.Algebra.Homology.ExtInjectiveEdgeQuasiIso`: the proved injective-edge
quasi-isomorphism. Both edge proofs use the existing
`HomologicalComplex₂.quasiIso_of_column_augmentation`. They transfer exactness of
representable functors to the linear Hom functors and apply it to Mathlib's proved
resolution augmentations. The projective proof uses total symmetry with sign
`(-1)^(ij)`, which is one on its degree-zero edge.

The original theorem composes Mathlib's `ProjectiveResolution.isoExt` with homology
of the two edges. Its private naturality lemma follows from
`isoLeftDerivedObj_inv_naturality` and `homologyOp_hom_naturality`; the rest is
cancellation in the two commuting squares. Updated the original DAG proof and added
nodes for the two proved edge statements. No existing interface was changed and no
other module was adapted.

All three modules compile without warnings, individually below 60 seconds (the final
full sandbox compile is also the delivery dry run). Explicit `#print axioms` checks
for the original theorem and both edge theorems returned exactly `propext`,
`Classical.choice`, and `Quot.sound`. The temporary print commands were removed.

## Proved and sorry left

Closed the original hole:
`ModuleCat.nonempty_ext_iso_injectiveResolution_homology`
(node `lem-sbc-ext-injective-resolution-comparison`).

Also proved, without adding holes:
`ModuleCat.resolutionHomProjectiveEdge_quasiIso`
(node `lem-sbc-ext-projective-edge-quasi-iso`) and
`ModuleCat.resolutionHomInjectiveEdge_quasiIso`
(node `lem-sbc-ext-injective-edge-quasi-iso`), together with the edge map laws and
precomposition squares. Sorries left in all delivered files: none. Holes closed: 1;
holes added: 0. This is a proof, not a decomposition into unproved statements.

## No longer needed

No original imports were removed and no original proof-dependency node was pruned:
the original node had no proof dependencies. Both parts of its double-complex route
are retained and proved. The proof needs no new double-complex spectral sequence,
no bridge to the newer derived-category Ext, and no separate homotopy-independence
node: Mathlib's naturality of the projective-resolution comparison supplies it.
These were considered routes, not existing dependencies that can be deleted.

The double-complex construction imports Mathlib's module colimits and the existing
natural-number signs directly. It does not itself import the large spectral-sequence
module `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex` just to obtain its
finite-diagonal existence instance. The proved augmentation criterion already has
that import in its own unchanged dependency closure; no global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The original node had two non-elementary steps with no named proof dependencies.
Its claimed plan could not simply be translated by applying recorded lemmas. The
existing `Sheaf.Algebra.Homology.FirstQuadrantAugmentation` supplies the missing
comparison criterion, and all Hom functor exactness, edge construction, symmetry,
and naturality glue is now proved.

The generic node `lem-sc-first-quadrant-column-augmentation`, in unit
`sk-thm-picard-duality`, is used as a tool for both edge proofs. No statement or step
of our unit `sk-prop-input-spreading` is bypassed (its realized lists are empty), and
there was no augmentation theorem recorded in our unit. The generic tool is already
proved with the permitted axioms. The reviewer/maintainer should record this tool use
according to the project rules; this delivery does not edit `tool_uses`.

Read Stacks Tag 0954 online: it invokes the injective Hom computation but does not
spell out the projective/injective comparison. This delivery makes that comparison
explicit using the established library augmentation theorem. No source or statement
error was found. Checked the low-degree signs and the zero-object cases directly:
the (0,n) vertical sign and the (n,0) symmetry sign are one; the single-source
comparison maps are identities in degree zero and isomorphisms between zero objects
in positive degrees. No boundedness, nonzero-module, or positive-degree hypothesis
is added.

## New nodes

`lem-sbc-ext-projective-edge-quasi-iso` records the concrete resolution Hom complex,
its canonical augmentations and precomposition squares, and the proved vertical edge
quasi-isomorphism. Module: `Sheaf.Algebra.Homology.ExtResolutionDoubleComplex`.

`lem-sbc-ext-injective-edge-quasi-iso` records the proved horizontal edge
quasi-isomorphism. Module: `Sheaf.Algebra.Homology.ExtInjectiveEdgeQuasiIso`.

Both are strictly parts of the original comparison, and both are proved here. Actual
LeanFinder, Loogle and grep searches are recorded; LeanSearch returned an internal
server error and is recorded as unavailable. Blueprint searches for the resolution
Hom comparison returned no matching imported node. No change record is needed.

## Second reading by C2

1. Compared every delivered module with the repository. The existing declaration signatures and `homComplexDiagram` definition are unchanged; the only existing-module interface change is the proof-only import. The two new modules and three new node records agree with their Lean declarations.

2. Compiled all three delivered modules with `lcompile.py --all`; they compile cleanly. Searched the sources for `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, and `implemented_by`; none occur. The delivered declarations are proved without additional axioms, as recorded in the first reading.

3. Checked the split-off statements against the concrete edge maps and the first-quadrant augmentation criterion. The projective-edge and injective-edge quasi-isomorphism statements are true, strictly simpler parts of the comparison, and are needed by the final theorem. They do not duplicate an existing declaration; the recorded Mathlib and repository searches found no matching theorem.

4. Read the proofs from the target downward. They use the existing first-quadrant augmentation tool, explicit Hom double-complex constructions, and Mathlib resolution naturality. The unit route remains represented by the comparison and both edge nodes. No unused proof dependency or import was identified; the proof-only import is private to the original theorem.

5. Checked the DAG proof steps, dependencies, origins, module/declaration records, and unit/chapter fields against the Lean code. The existing target statement is unchanged, and no definition is hollow. No source, statement, or route error was found.

Changed during this second reading: no Lean proof or statement changes; added this review record only.
