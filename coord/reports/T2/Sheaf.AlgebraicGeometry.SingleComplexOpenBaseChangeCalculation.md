## What changed

Reduced `AlgebraicGeometry.singleComplexOpen_baseChange_calculation` to the
one-morphism counit compatibility and the coherence of a pullback cube. Its
signature, docstring and two public imports are unchanged. The two new proof
imports are `SingleComplexOpenCounitCompatibility` and
`SingleComplexOpenPullbackCube`.

The private adjunction calculation is fully proved: restriction intertwines
Hom equivalences by the counit equation, and naturality and the cube equation
then identify the two mates. The source comparison and the restricted identity
coefficient are identified by expanding their actual constructions and using
functoriality of the identity. `baseChange_homEquiv` proves the defining counit
formula for the existing base-change arrow.

The saved attempt timed out. Named abbreviations now share exactly its fixed
composition and adjunction expressions, with no new choice. The open square
isomorphism and the commuting-square natural transformation are constructed
componentwise. Their naturality is proved from the original transformations.
This avoids repeatedly comparing transports on functors with transports on
objects in the concrete calculation. All construction data are explicit;
no definition contains a proof hole. These changes are in new modules only.

Sources read: Stacks Tags 08FE, 08BS, 08HY, 0D5S and the first paragraph of
0DJ9, in the saved cohomology.tex and perfect.tex. The unit
`sk-thm-picard-semicon` has empty realization lists. The construction refines
the existing open-locality step below that unit and keeps its route.

## Proved and sorry left

The original hole is reduced:
`AlgebraicGeometry.singleComplexOpen_baseChange_calculation`
(`lem-pc-n3-open-base-change-calculation`). This is a decomposition, not a
sorry-free proof of the targets' import closure.

Two holes are added, both strictly parts of the original argument:

- `AlgebraicGeometry.singleComplexOpen_counit_compatibility`
  (`lem-pc-t2-open-counit-compatibility`): one morphism and one open,
  identifying the fixed direct-image comparison with the pinned counit.
- `AlgebraicGeometry.singleComplexOpen_pullback_cube`
  (`lem-pc-t2-open-pullback-cube`): a composition-coherence equation with
  no direct images, adjunctions or base-change arrows.

The delivery closes one upper hole and adds two lower holes: net one additional
hole. No other declaration in these modules contains `sorry`; in particular,
all private helpers and all naturality obligations are proved. Empty and whole
opens, zero objects and unbounded complexes impose no additional hypotheses.
The cube requires commutativity, without a pullback assumption.

Validation is through lcompile.py for the whole sandbox and deliver3.py
--no-push, including the axiom probe. The second reading remains the next
worker's task; nothing is pushed by this worker.

## No longer needed

No original import is removed and no existing module is globally pruned.
The original direct proof-dependency edges to
`def-pc-ringed-spaces-derived-direct-image`,
`lem-pc-ringed-spaces-derived-pullback-composition` and
`lem-sc-derived-k-injective-restrict-open` are replaced by the new statements.
Their modules `RingedSpaceDerivedDirectImage`, `DerivedPullbackComposition`
and `Sheaf.Algebra.Homology.KInjectiveRestrictOpen` remain indirect dependencies.
The original resolution and derived-direct-image dependencies remain needed
by the counit lemma, and composition coherence remains needed by the cube
lemma. They are used through these smaller statements in the upper proof.
No single-degree compatibility or source-open unit-naturality module is used.
The composition abbreviation needs only `DerivedPullbackComposition`; its
initial broader import of `SchemeDerivedBaseChangeMap` was removed.

## Where the brief, the DAG or earlier work was wrong

The existing dependency statements do not expose the fixed counit-comparison
equation; existence of an isomorphism alone does not identify its chosen arrow.
The counit lemma states that missing step. The existing single-degree lemmas
choose comparison witnesses and do not apply to this arbitrary unbounded K.

The saved attempt's generic mate calculation was sound, but its full module
could not pass the time limit. Componentwise construction and named expressions
address the expensive definition comparisons. The 60-second file limit is
unchanged. There is no adaptation of another existing module. The local elaboration
commands trigger the static interface classifier; the required change record
documents that these commands have no exported effect.

The docstring of `singleComplexOpenPullbackIso` cites 08DW; the saved pinned
tag table identifies 08DW as the quasi-coherence pullback lemma. The new
construction cites 0D5S. Its use of the existing comparison is unchanged.

The blueprint ancestor helper gives None for the created-module chain. The
verified ancestor of the parent identity node is `lem-pc-rf-perfect-base-change`;
new nodes retain that ancestor with the intervening locality nodes in `via`.
Existing blueprint fields are untouched.

## New nodes

`def-pc-t2-open-pinned-composition`: an abbreviation for the exact original
composition family, in `SingleComplexOpenPinnedComposition`.

`def-pc-t2-open-pinned-adjunction`: an abbreviation for the exact original
adjunction family, in `SingleComplexOpenPinnedAdjunction`.

`def-pc-t2-open-square-comparison`: the fixed commuting-square transformation,
constructed by its object-level component formula, with proved naturality,
in `SingleComplexOpenSquareComparison`.

`def-pc-t2-open-pullback-square-iso`: the open-square isomorphism, constructed
from the original open pullback and composition comparisons. Its componentwise
presentation is in `SingleComplexOpenCounitCompatibility`.

`lem-pc-t2-open-counit-compatibility`: the one-morphism restricted counit
equation, in `SingleComplexOpenCounitCompatibility`.

`lem-pc-t2-open-pullback-cube`: pullback composition coherence around the
commuting cube, in `SingleComplexOpenPullbackCube`.

LeanFinder, Loogle and Mathlib/project grep found underived open-restriction
and generic mate/naturality APIs. The private proof uses the found adjunction
Hom-equivalence API. The fixed scheme comparisons had no duplicate. The saved
LeanSearch request returned Internal Server Error. Alias nodes add no new
mathematical assertions or existence witnesses. The change record is
`coord/changes/T2-open-base-change-proof-elaboration.md`; every existing
statement, definition and public import is preserved.

## Second reading by T2

1. Compared the target module with the repository version. Its target
signature and docstring are unchanged; added declarations are recorded as new
nodes and its public imports are preserved. Verdict: unchanged target.

2. Compiled all delivered modules with `lcompile.py --all`. No forbidden
declarations or hollow definitions occur. The only remaining `sorry`s are the
two named split-off lemmas, each with a source, proof description, and node.
Verdict: clean compilation with explicit holes only.

3. Checked the split-off statements and edge cases. The counit lemma fixes one
morphism and open; the cube lemma contains only the needed commutative-square
data. Both are strictly simpler than the original target and no duplicate was
found. Verdict: true, needed decomposition.

4. Checked the proof route and imports. The target uses the pinned comparison
and adjunction abbreviations, componentwise square comparison, and both
split-off lemmas. The unit route is retained and dependency replacements are
recorded above. Verdict: route and pruning agree with the Lean proof.

5. Compared DAG metadata with declarations and proof calls. The existing
target metadata changes only in proof and proof dependencies; every new
declaration has a matching node and source. Verdict: DAG and Lean agree.

Changed only this report section; no further code changes were needed.
