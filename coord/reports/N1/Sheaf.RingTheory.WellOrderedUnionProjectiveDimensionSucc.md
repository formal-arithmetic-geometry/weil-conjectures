## What changed

Reduced the unchanged successor theorem in
`Sheaf.RingTheory.WellOrderedUnionProjectiveDimensionSucc` to a projective presentation
and a bounded-resolution splice. The target uses `obtain`, rewrites the presentation's
codomain equality, and applies the proved splice theorem.

The second reader proved the splice in `Sheaf.RingTheory.ProjectiveResolutionSuccSplice`
using `ChainComplex.augment`. The unresolved filtration presentation is in its own new
module, `Sheaf.RingTheory.WellOrderedUnionProjectivePresentation`, with its full
natural-language construction. Both imports in the original module are proof-only;
its three original public imports and existing declaration header are unchanged.
The unused-variable linter is disabled only for the target declaration because its
unchanged induction-hypothesis type names unused proof binders.

## Proved and sorry left

Hole closed relative to the repository:
`ModuleCat.hasProjectiveResolutionLE_of_wellOrderedUnion_succ`.

One new hole remains:
`ModuleCat.exists_shortExact_projective_middle_of_wellOrderedUnion_succ`, node
`lem-weil-pbc-well-ordered-union-succ-data`, in the presentation module.

The second reading also closed the first worker's added hole
`ModuleCat.hasProjectiveResolutionLE_of_shortExact_projective_middle`, node
`lem-weil-pbc-projective-resolution-succ-splice`. This theorem is proved with only
`propext`, `Classical.choice`, and `Quot.sound`.

Relative to the repository this is one hole closed and one added: a decomposition,
net zero holes, with a genuinely proved splicing component. The original theorem
still depends on `sorryAx` through the filtration presentation; it is not a completed
proof under AGENTS.md §5. There are no definitions or arbitrary data choices added.

## No longer needed

No original Lean import or module is pruned. The proposed public `ShortExact` import
in the original module was removed after moving the new statement to its own module;
its earlier import change record is consequently unnecessary and removed.

All seven old direct `proof_deps` are replaced in the successor node by the presentation
and splice nodes:
`def-weil-pbc-direct-sum-modules`, `def-weil-pbc-exact-sequence`,
`def-weil-pbc-finite-global-dimension`, `def-weil-pbc-quotient-module`,
`lem-weil-pbc-projective-dimension-ses-kernel`,
`lem-weil-pbc-projective-direct-sum-family`, and
`lem-weil-pbc-ses-projective-quotient-splits`.
They remain mathematical ingredients of the presentation's proof plan; the dimension
definition also remains a statement dependency. No claim of transitive pruning is made.

## Where the brief, the DAG or earlier work was wrong

The first worker left the filtration lemma without the required complete docstring
proof, put it in the existing module, copied unrelated SES-kernel review and split
metadata into both new nodes, and omitted the replacement of all old direct proof
dependencies from the pruning report. These are repaired. The previous second-reading
claim that no prior proof dependency was removed was incorrect.

The existing SES-kernel declaration is restricted to module universe `max u v`,
so it cannot discharge the unrestricted-universe dimension-shifting component
without further work. The presentation docstring records the categorical Schanuel
argument instead of assuming an unavailable enough-projectives instance.

## New nodes

`lem-weil-pbc-well-ordered-union-succ-data` records the construction of a short exact
projective presentation with kernel bound `n`. Its statement explicitly retains all
successor hypotheses and its Lean declaration is copied verbatim into the node.

`lem-weil-pbc-projective-resolution-succ-splice` records the proved augmentation
construction, in arbitrary module universe `v`. Its proof and dependencies match
that construction. No statement or definition change record is needed.

## Second reading by N1

1. Compared the delivered target with the repository by `diff` and an independent
   byte-for-byte declaration-header comparison. The existing theorem signature and
   docstring are unchanged; there are no changed definitions. New statements have
   their own modules. Verdict: pass after moving the presentation and removing the
   unnecessary public-import change.
2. Compiled all three delivered modules in import order with `lcompile.py --all`.
   The only sorry is the named presentation theorem. No axiom, unsafe, opaque,
   implemented_by, extern, or hollow definition occurs. Scratch-copy axiom checks
   show the splice uses only the three permitted axioms; the presentation and target
   additionally use `sorryAx`. Verdict: valid partial reduction, not a completed target.
3. Checked the split against [Stacks 0D1U](https://stacks.math.columbia.edu/tag/0D1U)
   and [065S](https://stacks.math.columbia.edu/tag/065S), including bound zero, zero
   modules, repeated stages, singleton filtrations, empty indices, and independent
   universes. The presentation and splice are distinct components, not a renamed
   copy of the target. Expanded the presentation proof through shrinking, kernel
   filtration, dimension shifting and the induction hypothesis. New searches by
   grep, loogle and leanfinder found no public theorem of either precise statement.
   LeanSearch returned Internal Server Error for both statements; that unavailability
   is recorded without asserting a search verdict.
   `Sheaf.Algebra.TorDimensionShiftNatural` has private splicing helpers restricted
   to equal universes and a free middle term; these cannot be imported as this theorem.
   Verdict: true, necessary split; splice now fully proved.
4. The target now combines one unresolved construction with a proved splice.
   Statement imports remain public and proof imports are plain. Tested removing
   the splice's ModuleCat Abelian import: homology-instance synthesis failed, so
   it is retained. The report lists every replaced old direct dependency, without
   claiming transitive pruning. Read `dag/units/sk-thm-p1.json`: its realized route
   is unchanged and no unit step is bypassed. Verdict: pass.
5. Matched the target proof to its two direct proof dependencies, both new Lean
   statements to their nodes, and their docstring proofs to their node plans.
   Removed copied unrelated metadata; corrected provenance, blueprint ancestry,
   actual search records, and the presentation module path. Verdict: pass.

Second reading changed the splice proof and its proof imports, moved and documented
the remaining presentation statement, localized the linter option, repaired node
metadata and pruning accounting, and removed the unnecessary import change record.
