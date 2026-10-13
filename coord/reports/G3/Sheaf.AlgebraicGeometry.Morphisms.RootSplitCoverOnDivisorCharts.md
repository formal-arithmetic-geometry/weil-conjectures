## What changed

The assigned module now proves `AlgebraicGeometry.Scheme.root_split_cover_on_divisor_charts`
from two strictly separate argument steps, imported privately:
`Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverIndEtaleCharts` and
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootChartsIndEtaleDescent`.
The first stops at the ind-etale strict local limit and proves the affine finite-presentation
properties needed for descent. The second is a general descent statement with no regularity,
root-splitting, or divisor-point hypotheses. It retains the orbit index set and exponents.
The Lean proof extracts the local model, applies descent, and assembles the required witnesses.
The original signature and existing public imports are unchanged. No definitions or other
existing modules were changed. The node now records these two proof dependencies.

## Proved and sorry left

One original hole closed: `AlgebraicGeometry.Scheme.root_split_cover_on_divisor_charts`
(node `lem-sbc-root-split-cover-on-divisor-charts`). No sorry remains in the assigned module.
This is a decomposition, not an unconditional proof of the entire mathematical argument:
two new public theorem holes remain:

- `AlgebraicGeometry.Scheme.root_split_cover_indEtale_charts`,
  node `lem-sbc-root-split-cover-ind-etale-charts`.
- `AlgebraicGeometry.Scheme.punctured_root_charts_descend_indEtale`,
  node `lem-sbc-punctured-root-charts-ind-etale-descent`.

Each is in its own module, with exactly `:= by sorry`, a source, and a complete proof in words.
The net hole count is 1 closed minus 2 added = -1. Both new holes are necessary parts of the
argument. They are not the assigned statement under another name: the first supplies only an
ind-etale limit model, and the second descends an already supplied model independently of
its origin. No arbitrary data was put into a definition or chosen from an existence theorem.

The three sandbox modules compile with lcompile.py. Edge cases checked in the new statements:
empty cover (m=0), n=1, empty punctures, and zero rings in the general descent statement.
The point over y excludes a zero H; no nonempty chart hypothesis was added. Positivity and
the original image of g in every root equation survive descent unchanged.

## No longer needed

None. No original import or planned node was pruned. The original node had no proof dependencies;
its formerly unsplit argument is now isolated into two parallel items. The unit route through
the tame divisor calculation and finite-presentation descent is retained.

## Where the brief, the DAG or earlier work was wrong

The saved attempt contained no proof changes and reported an empty sorry baseline.
That tool failure no longer reproduces: stage3_delivery.diff_module detects the original
`AlgebraicGeometry.Scheme.root_split_cover_on_divisor_charts` hole. The dry run on the unchanged
saved module correctly refused it because nothing was proved. No tool was changed or bypassed.
The original DAG proof was one long non-elementary step with an empty uses list, so there were
no stated proof-dependency declarations to apply. The new nodes make its strict local and
finite-stage parts explicit. Searches found no exact existing theorem: LeanFinder returned
standard etale and field-product facts, while the descent search returned general finite-
presentation factorization facts. LeanSearch was unavailable; this was recorded without a
negative search verdict. Existing punctured-root section descent and limit-presentation nodes
concern a single section of a finite etale morphism, not an isomorphism of the orbit-chart
product; they do not state either new step.

## New nodes

`lem-sbc-root-split-cover-ind-etale-charts` states the strict-local cyclic-orbit calculation
and the affine finite-presentation properties of the original cover. Its source is Stacks
Project Tag 0EYG (strict henselization and intermediate-root paragraphs), with Tags 02LA
and 02VN for descent of finiteness and etaleness. Its module is
`lean/Sheaf/AlgebraicGeometry/Morphisms/RootSplitCoverIndEtaleCharts.lean`.

`lem-sbc-punctured-root-charts-ind-etale-descent` states finite-stage descent of a finite
punctured product of root charts for an affine finite-presentation morphism, retaining the
exponents and projection identity. Its source is Tag 0EYG (descent paragraph) and Tag 05N9
(2), (3). Its module is
`lean/Sheaf/AlgebraicGeometry/Morphisms/PuncturedRootChartsIndEtaleDescent.lean`.

No change record is needed: no existing statement, definition, or public interface changed.

## Second reading by G3

1. Interface: PASS. Diffed the assigned module against the repository. Its existing
   theorem signature and docstring are byte for byte unchanged; only two plain
   proof imports and the proof body differ. Both additional modules are new.
   No definition, existing public import, target statement, or other existing
   module is changed. The existing node differs only in proof, proof_deps, and
   proof_origin, as permitted.
2. Kernel and holes: PASS as a decomposition. Compiled all three modules locally
   with lcompile.py. Compiled scratch copies with #print axioms for all three
   declarations: each lists only propext, Classical.choice, Quot.sound, and
   sorryAx. The item has no sorry; the only two delivered sorries are exactly
   the named public theorems listed above. There are no definitions or forbidden
   declarations. Thus the upper proof is conditional on the two explicit holes,
   not a sorry-free mathematical proof; the net hole change remains -1.
3. Split statements: PASS. Read both full signatures and proofs in words, checked
   RingHom.IndEtale against its actual filtered-colimit definition, and checked
   IsRegularRing includes Noetherianity. The local lemma stops before finite-stage
   descent; the descent lemma assumes a supplied model and has no regularity or
   splitting hypothesis. Neither merely renames the item. Checked d=0, n=1,
   m=0, empty punctures, and unit/zero base cases: the on-divisor point rules out
   a zero local base and a unit g; the general descent statement still handles
   empty punctures. The finite product and localization are finitely presented,
   allowing maps, inverses, unit witnesses, and equalities to descend together.
   Sources checked: https://stacks.math.columbia.edu/tag/0EYG and
   https://stacks.math.columbia.edu/tag/05N9. Second searches used LeanFinder
   queries on finitely presented algebra isomorphisms in filtered colimits and
   cyclic Galois torsor subgroup classification, Loogle on AdjoinRoot/IndEtale,
   and grep on strictHenselization/AdjoinRoot and intermediate roots in lean/.
   Supporting Mathlib results include autEquivRootsOfUnity, autEquivZmod,
   CommRingCat.preservesFilteredColimits_coyoneda, and
   CategoryTheory.IsFinitelyPresentable.exists_eq_of_isColimit; none directly
   proves either new scheme theorem. Loogle does not know the upstream
   Algebra.IndEtale identifier, so that search gives no negative-match evidence.
   Read the existing punctured-root section descent and pointed-section stage
   descent: they descend one map, not an isomorphism of a prescribed finite
   product with its inverse identities. The higher root-chart theorems depend
   on this item, so cannot supply a shorter acyclic proof. Neither new hole can
   be closed in a few minutes from these results.
4. Route and pruning: PASS. The proof applies the local-model lemma, then the
   general descent lemma, then packages their witnesses. Both proof imports
   are plain imports. All remaining imports supply types or notation in the
   signatures. There were no old proof_deps to prune, so No longer needed is
   complete. Read dag/units/sk-prop-input-spreading.json: its tame structure
   input through 0EYG is retained, and no unit step is bypassed. Its realized
   entries are already empty in the repository; this delivery does not change
   the unit record or claim to repair that earlier metadata gap. The referenced
   literature unit file is absent on this machine; the unit JSON carries its
   statement and steps.
5. DAG agreement: PASS after repair. The parent proof steps and dependency union
   match the two theorem applications. Each new node has its source, complete
   argument, searches, split status, creation record, blueprint provenance,
   chapter, unit, and Lean record. Removed empty proof steps from both new nodes
   and replaced their normalized Lean statement strings with the exact multiline
   signatures from the corresponding files. No statement meaning changed.

Second reading changed only the two new DAG records as described in point 5
and added this review section. No Lean repair was needed. No additional hole
was closed or added during the second reading.
