## What changed

Reduced `AlgebraicGeometry.Scheme.picard_termwise_model_comparison` to the two
independent counit-coherence equations, one for source singles and one for target
perfect models. The main proof explicitly constructs the restricted chain map by
termwise functorial pullback and the canonical ordinary comparison isomorphisms,
checks its zeroth component, and combines the two coherence equations using
naturality of the complex counit and cancellation of mapped isomorphisms.

Moved `picardTermwiseModel` and `picardTermwiseSource` verbatim to the publicly
re-exported module `Sheaf.AlgebraicGeometry.PicardTermwiseModels`, preserving
names, universes, signatures, bodies and visibility. That module also constructs
`picardTermwiseSourceRestrictionIso`, `picardTermwiseModelRestrictionIso`, and
`picardTermwiseCounit` explicitly. No arbitrary object comparison is selected.
The counit uses precisely the selected left-derived cone underlying the canonical
composition isomorphisms; its universal property determines the cone up to the
compatible isomorphism. This extraction prevents circular imports by the new
coherence modules. See `coord/changes/picard-termwise-models-extraction.md`.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.Scheme.picard_termwise_model_comparison`
(node `lem-sc-picard-termwise-model-comparison`) by a decomposition.

Added exactly two named holes:
- `AlgebraicGeometry.Scheme.picard_termwise_source_coherence`
  (`lem-sc-picard-termwise-source-coherence`), which concerns only the source single,
  without a local model or a chain map.
- `AlgebraicGeometry.Scheme.picard_termwise_target_coherence`
  (`lem-sc-picard-termwise-target-coherence`), which concerns only the perfect target
  model, without a source single or a chain map.

No hole remains in the item's module; no definition contains a hole. This is a
reduction, with one hole closed and two added, not a fully closed transitive proof.
The degree-zero and naturality/cancellation parts of the argument are proved here.
The edge cases remain included: zero complexes, empty schemes, negative terms,
and arbitrary scheme morphisms. Source coherence has no perfectness assumption;
target coherence retains exactly strict perfectness and the given local model.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`
and `Sheaf.AlgebraicGeometry.DerivedPullbackStructureSheaf` from the item's module.
The old direct proof dependency `lem-pc-flat-complex-derived-pullback` is now
used through both new coherence nodes rather than directly by the main theorem.
The bounded-flat computation and its module remain in the import closure.
`def-pc-perfect-complex` remains a dependency: the main proof passes hK to the
target-coherence theorem. These account for every original proof dependency. The standalone object-only node
`lem-sc-derived-pullback-structure-sheaf-local` and its module
`Sheaf.AlgebraicGeometry.DerivedPullbackStructureSheaf` do not supply the required
coherence and are no longer needed on this proof route. No claim is made that
another target branch no longer uses them.

The original public Mathlib.CategoryTheory.Adjunction.Additive import is supplied
through the publicly re-exported PicardTermwiseModels module. Every original
statement-level dependency remains available. No unit-level step is bypassed;
`dag/units/sk-prop-av-cube.json` has no realized node in this local reduction.

## Where the brief, the DAG or earlier work was wrong

The stated object-computation dependencies provide isomorphisms but not the
simultaneous equations with the pinned canonical composition maps. Arbitrary
object isomorphisms would be insufficient: the final equation requires separate
source and target coherence. These are the precise parts now split off. The
original theorem's statement has not changed.

Mathlib searches ran through msearch.py: Loogle and Lean Finder found the
single-complex and termwise functor ingredients; grep found their definitions.
LeanSearch returned Internal Server Error, recorded as unavailable.

## New nodes

`def-sc-picard-termwise-models` records the existing two model abbreviations at their
new source file and the explicit restriction isomorphisms and natural complex
counit. It has no sorry and no postponed construction.

`lem-sc-picard-termwise-source-coherence` isolates the invertible counit on the
structure-sheaf single and its composition equation, independently of K and E.

`lem-sc-picard-termwise-target-coherence` isolates the transported perfect model's
invertible counit and its composition equation, independently of all source singles
and chain maps. Each theorem has its source and full proof in words in its docstring.

Change record: `coord/changes/picard-termwise-models-extraction.md`.

## Second reading by P2

1. Compared the main module with its repository version using diff and compared
   the declaration text programmatically. The complete existing theorem signature
   is byte-identical. Both extracted abbreviations have byte-identical signatures
   and bodies, with the same universe and public visibility. The extraction is
   declared in picard-termwise-models-extraction.md; its source-tag comments change,
   but its data does not. No existing downstream module is adapted. Verdict: pass.
2. Read all four modules. The private categorical transport lemma uses only
   naturality, functoriality and inverse cancellation. The main proof actually
   constructs f' = u.hom ; F.map f ; w.inv, proves its zeroth-component formula,
   and uses that transport lemma to prove the canonical derived restriction
   equation. Only the two reported public coherence theorems contain sorry.
   There is no forbidden declaration or hole in a definition. The counit is a
   whiskered left-derived cone selected together with its composition maps;
   the universal property determines this cone up to compatible isomorphism,
   which is precisely the equality transported downstream. No arbitrary witness
   from a mere existence proposition is used to define an object. All four modules compiled locally without warnings. A separate scratch
   module ran #print axioms for all five model/construction declarations and all
   three public theorems: the five constructions use only propext, Classical.choice
   and Quot.sound; the two coherence theorems and the main theorem additionally
   use sorryAx, as expected for this decomposition. The delivery tool also ran
   its declaration-by-declaration axiom probes without reporting forbidden axioms. Verdict: valid decomposition, not a
   complete transitive proof.
3. Read both new statements and their complete proof docstrings against
   [Stacks 06YJ](https://stacks.math.columbia.edu/tag/06YJ),
   [0D5S](https://stacks.math.columbia.edu/tag/0D5S), and the open-restriction
   assertion in the proof of [08DW](https://stacks.math.columbia.edu/tag/08DW).
   Source coherence drops all local-model data and every chain map; target
   coherence drops the source single and every chain map. Neither restates the
   original theorem. The single unit is flat and bounded above; tensor pullback
   of the transported finite-free retract terms computes the perfect target.
   The selected composition lift's factorization and associativity give exactly
   the stated orientations of c.inv, u.hom and w.hom. Checked identity i and
   reflexive transports, zero K and E, empty U/schemes, negative nonzero terms of
   bounded K, and nonflat i: no extra geometric or connectivity assumption is
   needed. Repeated searches with different words: Lean Finder found
   Functor.leftDerived_fac_app and leftDerived_ext, Loogle rejected the guessed
   leftDerivedLift_fac name, and msearch grep confirmed the actual factorization
   lemma. Searched local Sheaf and upstream Lean for composition/counit and
   coherence. Read canonicalSinglePullbackComposition,
   isIso_canonicalSinglePullbackMap and localizedPullback_perfectCounit: these
   provide ingredients, with different single targets or independently selected
   local-model counits, rather than either full stated equation. Converting those
   ingredients to the pinned complex equations is substantive, so neither hole
   can responsibly be closed in a few minutes. Verdict: true, strictly smaller,
   sourced holes; no exact duplicate found.
4. Inspected the imported object-computation lemmas and the shorter existing
   routes above. An unrelated object isomorphism would not prove the pinned
   equation, and the submission correctly avoids it. Proof-only coherence and
   flat-computation imports are private; Models is public because the existing
   theorem signature uses its extracted abbreviations. The additive import is
   needed in the public abbreviation body. No unused new direct import found.
   Expanded No longer needed to account explicitly for the former direct
   bounded-flat edge and retained perfectness edge. The object-only structure
   sheaf module is removed on this route; bounded-flat remains indirectly.
   Inspected sk-prop-av-cube.json: realized.statement and its step are empty,
   so this local refinement bypasses no recorded unit realization. Verdict: pass.
5. Matched each new node's statement to its Lean declaration and its proof steps
   to the docstring. Main steps record the explicit chain-map construction and
   the categorical naturality/cancellation proof. Restored the perfect-complex
   dependency explicitly used by passing hK. Fixed all three new blueprint
   records: their ancestor is the actual imported thm-sc-theorem-of-cube, with
   the existing item's ancestry and a specific place, rather than the newly
   created intermediate item. Searched the whole blueprint for counit and
   termwise; none duplicates these concrete model/coherence statements.
   Verdict: node records agree after these repairs.

Changed only node metadata and this report in the second reading. Kept the
correct Lean proof and interfaces. One original hole is closed by decomposition,
two holes are added; the local net is minus one, and no positive net progress or
whole-library pruning is claimed.
