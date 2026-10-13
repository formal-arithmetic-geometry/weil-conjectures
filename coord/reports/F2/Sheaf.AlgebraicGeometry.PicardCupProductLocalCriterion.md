## What changed

Proved the unchanged local cup-product criterion by four fully proved supporting
lemmas. Perfectness splits the counit; the supplied equal local ranks make that
split injection invertible. The converse uses a chain of adjunction and internal-Hom
bijections and Yoneda, avoiding the projection-formula route. The explicit pulled
pairing is checked against the actual tensor and unit comparisons, including the
scalar automorphism between the two unit isomorphisms.

All five modules compile through lcompile.py. Existing signatures and public imports
of the item are unchanged. No existing dependency module was adapted.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.picardCupProduct_isIso_iff_counit_of_local_ranks`.

Added zero holes. The following new public declarations are fully proved:

- `AlgebraicGeometry.Scheme.isIso_of_isSplitMono_of_picard_local_ranks`.
- `AlgebraicGeometry.Scheme.Modules.isSplitMono_counit_of_isIso_picardPushforwardPairing`.
- `AlgebraicGeometry.Scheme.Modules.isIso_curry_picardPushforwardPairing_of_isIso_counit`.
- `AlgebraicGeometry.Scheme.Modules.isIso_curry_picardPullbackEvaluation`.

No delivered declaration contains sorry. The equal-rank argument imports the existing
`AlgebraicGeometry.Scheme.Modules.stalk_isFiniteFree_of_isFiniteLocallyFree`
from StalkFiniteFree; its existing sorry is not changed by this delivery. Thus this
is a proof from the project's stated dependencies, not a claim that the entire
transitive closure is axiom-free. Zero rank and empty schemes require no exceptional
case or extra hypothesis.

## No longer needed

Removed the item's proof imports:

- `Sheaf.AlgebraicGeometry.PullbackDualFiniteLocallyFree`, node
  `lem-ag-pullback-dual-finite-locally-free`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeTensorUnit`, node
  `lem-sc-finite-locally-free-tensor-unit`.

Neither lemma occurs in this proof's new dependency path. No projection-formula
lemma or separate dual-base-change theorem is needed. This is pruning for this item;
other library declarations may still use these modules. PicardCupProductMap remains
the public statement import. The new proof imports are exactly the four helper modules.

## Where the brief, the DAG or earlier work was wrong

The earlier missing PicardCupProductMap.olean tool failure no longer occurs.
The original proof plan works, but its converse can be shortened: perfectness of
the original evaluation and an invertible counit suffice by adjunction, with no
finite local freeness or equal-rank condition on the direct image in this direction.
The node and docstring now describe that argument. No statement was disputed or changed.
LeanSearch returned Internal Server Error for all four new-statement queries; the
recorded LeanFinder and source-grep searches found component results but no exact
replacement. Source citations refer to the supplied Stacks proof plan; the categorical
refinements and complete Lean proofs were written by this worker (proof_origin agent).

## New nodes

- `lem-sc-picard-split-mono-equal-ranks`: PicardCounitEqualRanks, proved.
- `lem-sc-picard-perfect-pairing-split-counit`: PicardCupProductSplitCounit, proved.
- `lem-sc-picard-perfect-pairing-of-counit`: PicardCupProductOfCounit, proved.
- `lem-sc-picard-pullback-perfect-evaluation`: PicardPullbackPerfectPairing, proved.

Each is a strict, reusable part of the argument with its own module, complete proof
in words, recorded searches, and proof dependencies. None is a renamed copy of the
criterion, and none leaves a new item with a sorry.

## Second reading by F2

1. Interface: PASS. Compared the existing module with the repository using diff;
   its only existing declaration has a byte-for-byte identical signature. The
   existing public import and definitions are unchanged. The four helper modules
   are new; no existing dependency module or target is adapted. The existing node
   changes only proof, proof_deps and proof_origin. No change record is necessary.
2. Proof and axioms: PASS. All five delivered modules compiled locally through
   lcompile.py without errors or warnings. A scratch copy with #print axioms for
   all five public theorems showed only propext, Classical.choice and Quot.sound
   for the three categorical helpers. The equal-ranks helper and criterion also
   use sorryAx through the existing StalkFiniteFree dependency. No delivered
   declaration contains sorry, axiom, unsafe, opaque, implemented_by, extern or
   a kernel-check bypass. No definition is added. The selected adjunction and
   composition comparisons come from the existing canonical constructions;
   no arbitrary object is selected from an unproved mere-existence statement.
3. Helpers: PASS. No statements are split off with sorry: all four new statements
   are proved, strictly separate parts of the argument. Checked the equal-rank
   retraction argument over commutative rings, including rank zero; checked the
   exact-pairing retraction, unit automorphism and natural Hom-bijection arguments.
   Empty schemes cause no point or basis choice obligation. Independent LeanFinder
   queries used dualizable morphisms preserving a pairing, nondegenerate direct
   images, strong monoidal inverse image, and equal-rank finite projective modules;
   Loogle queried IsSplitMono and IsIso. Source searches covered lean/Sheaf,
   lean/WeilConjectures, Mathlib rigid/closed categories and scheme modules.
   These found component results, but no replacement for a helper. In particular,
   a field-only injective/equal-finrank theorem does not replace the ring argument.
4. Route and imports: PASS after repair. The proof starts at the unchanged criterion,
   uses existing categorical results, and proves each new intermediate statement.
   Both obsolete old proof-dependency nodes and their imports are listed above.
   The cube unit statement and its step applying the general cube theorem stay
   unchanged; this is a refinement below that step, not a bypass of a cited unit.
   dag/units/sk-prop-av-cube.json already has empty realized lists in the repository;
   this item is not listed there and this delivery does not alter that metadata.
   The rank helper incorrectly publicly imported PicardCupProductMap solely for
   its proof. Changed that to a plain import and explicitly publicly imported
   TensorPullback, the finite-local-freeness declarations and scheme Pullbacks
   needed by its signature. Recompiled the repaired helper successfully.
5. DAG: PASS. Read all five node records against their theorem signatures and
   proofs. Each proof_deps is exactly the union of its proof-step uses; every
   referenced dependency exists. The four new records have their chapter, unit,
   source, complete proof, searches, origin, creation, blueprint and Lean fields.
   The criterion records exactly the four helper applications and cup construction.

Second reading changed only the import visibility of PicardCupProductMap in
PicardCounitEqualRanks and added its explicit public signature dependencies.
No proof, statement, definition or DAG record needed repair. One original hole
is closed, zero holes are added, and zero unproved statements are split off.
