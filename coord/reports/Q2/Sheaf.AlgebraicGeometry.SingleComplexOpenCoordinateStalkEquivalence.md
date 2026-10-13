## What changed

The original theorem `AlgebraicGeometry.nonempty_singleComplexOpen_stalk_arrow_iso`
keeps its signature and visible imports. Its proof now normalizes both coordinate
maps using exact-stalk homology, the coordinate chain map, and `represents`.
It factors the canonical restricted coefficient through the restricted identity
coefficient, applies naturality to the arbitrary coefficient, constructs the target
isomorphism from the two target-coordinate identifications, and packages the
commuting square using `Arrow.isoMk`.

The proof-only import
`Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateStalkTransportData` contains
one strictly smaller remaining source/counit transport theorem. It has no target
complex, coefficient morphism, or coordinate chain map. The parent node records
this reduction, and the new node records the original ring-transport calculation.
A private, fully proved normalization lemma supplies the coordinate calculation;
its proof follows the existing fixed-square normalization in
`StalkComparisonCoordinateInvariance`.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.nonempty_singleComplexOpen_stalk_arrow_iso`
(node `lem-pc-single-complex-open-coordinate-stalk-equivalence`).
There is no `sorry` left in the item's module.

Added hole:
`AlgebraicGeometry.exists_singleComplexOpen_normalized_transport`
(node `lem-pc-single-complex-open-normalized-transport`), in the new module
`Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateStalkTransportData`.
Its proof is exactly `by sorry`, with the source and full proof in words in its
docstring. This is a decomposition: one hole closed, one hole added, net zero.
The source/counit open transport still requires proof; this is not an axiom-free
completion of the target closure.

The private lemmas `stalkComparison_normalized` and `normalized_square` are proved
without adding a hole. The latter performs the final diagram algebra with abstract
objects, avoiding repeated unfolding of the tensor-cohomology source.
No definition, existing statement, or target signature changes.
The main proof compiled locally in 28 seconds; the delivery dry run checks the
complete two-module set and the signature and axiom probes.

## No longer needed

No modules are pruned, and no original import is removed. The following old
`proof_deps` are no longer direct dependencies of the parent proof; each is
retained beneath `lem-pc-single-complex-open-normalized-transport`:

- `lem-pc-open-restriction-stalk-extension-iso`
- `def-pc-derived-open-restriction-maps`
- `def-pc-base-derived-tensor-cohomology-model`
- `lem-pc-kflat-stalk-criterion`
- `lem-pc-ringed-spaces-derived-pullback-composition`

They remain in the dependency closure and are not claimed as pruning. The
fixed-square coordinate-invariance and source-open conjugacy theorems were
examined but not imported: neither handles restriction of both base schemes
with this canonical exact-restriction coefficient.

## Where the brief, the DAG or earlier work was wrong

The planned source-transport and pullback-naturality declarations transport
representatives within one fixed square. They do not directly provide the
cross-ring compatibility needed for the restricted square. The new theorem
isolates that part of the existing plan. The coefficient/target-coordinate part
is proved in Lean, including its factorization through the identity coefficient.
The original statement is not disputed.

The unit `sk-thm-picard-semicon` has no realized entries naming this node; the
reduction retains the original localization route and introduces no replacement
for a unit statement or step. Empty opens have no point z; top opens, zero rings,
zero complexes and unbounded complexes are allowed in the new statement. The
source and target representing isomorphisms may be arbitrary; their actions are
included in the normalized square, so no special coordinate presentation is
assumed.

## New nodes

`lem-pc-single-complex-open-normalized-transport` records only the source tensor
comparison into derived pullback under open restriction. It includes a natural
isomorphism of exact derived stalk cohomology functors and the square for the
restricted identity coefficient. Its module is
`lean/Sheaf/AlgebraicGeometry/SingleComplexOpenCoordinateStalkTransportData.lean`;
its node is
`dag/nodes/sec-picard-framework/lem-pc-single-complex-open-normalized-transport.json`.
LeanFinder, Loogle and source searches found underived restriction-stalk tools but
no exact normalized cross-ring comparison theorem. LeanSearch was also attempted
and returned Internal Server Error; this is recorded as unavailable. Its source is the parent's localization and
universal-counit calculation (Stacks Tags 0DJ9, 08HY and 08FE); the remaining
argument is documented in full. No change record is needed.

## Second reading by Q2

1. Compared both delivered modules with the repository baseline. The existing
   theorem signature is byte for byte identical (also checked programmatically).
   Existing visible imports and all definitions are unchanged. The added import
   in the parent is proof-only; the second module is new. No change record is
   required. Verdict: pass.
2. Compiled the two-module set through lcompile.py, then compiled scratch copies
   with explicit `#print axioms`. The parent depends only on `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`; both private helpers have only
   the three permitted axioms. The transport theorem has the same four axioms
   as the parent and is the sole added hole.
   There are no forbidden declarations or hollow definitions. Its existential
   witnesses are eliminated inside a proof of Nonempty, not selected as data of
   a definition. Verdict: pass as a decomposition, not axiom-free completion.
3. Read the normalized transport signature and docstring against the source/counit
   portion of the original argument. Arbitrary source representatives are related
   by e and a; no target representative, target K', coefficient phi, or chain map
   remains. Thus this is strictly a part of the argument, not a renamed parent.
   Empty opens have no z; top opens reduce to representative transport; zero
   complexes give zero sources; zero rings give zero modules. No boundedness or
   base-flatness premise is silently needed. Independent LeanFinder search for
   exact derived restriction/stalk cohomology returned restrictStalkNatIso tools;
   Loogle search for mapDerivedCategoryFactors returned localization tools;
   grep and repository searches found no exact replacement. Checked the fixed
   square and source-open results: their base schemes stay fixed. The remaining
   cross-ring counit compatibility is not a few-minute corollary of these results.
   Source pages were read at https://stacks.math.columbia.edu/tag/0DJ9,
   https://stacks.math.columbia.edu/tag/08HY, and
   https://stacks.math.columbia.edu/tag/08FE (literature files are absent here).
   Verdict: true reduction with one properly documented open theorem.
4. Read the proof downward: normalize using represents and exact-stalk homology
   naturality, factor the restricted coefficient through the identity coefficient,
   apply naturality, cancel the target normalization, then apply Arrow.isoMk.
   The abstract normalized_square calculation has the correct orientations.
   All imports supply names in signatures or proofs; no public proof-only import
   was added. The unit sk-thm-picard-semicon has empty realized entries, so no
   designated unit step is bypassed. Verdict: pass. Corrected No longer needed
   to enumerate the five dependencies moved below the new node; none is pruned.
5. Compared the parent node diff and new node with the Lean declarations. The
   proof steps, dependency unions, origins, new-node metadata, verbatim Lean
   statement, source, docstring blueprint tag, and searches agree. Existing-node
   changes are restricted to stage-3-owned fields. Verdict: pass.

Second reading changed only report.md: completed this review and corrected the
accounting of old direct proof dependencies. No Lean repair was necessary. One
original hole is closed by a proved reduction and one simpler hole is added:
net zero. The delivery dry run performs the complete declaration axiom probes
and preflight before push.
