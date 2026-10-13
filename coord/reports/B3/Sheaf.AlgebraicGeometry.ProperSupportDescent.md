## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.ProperSupportDescent` with a
complete Lean proof of
`AlgebraicGeometry.exists_hasSupportProperOver_baseChange_of_isLimit`.
All existing signatures, definitions, and public imports are unchanged.
Added the proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier` for the existing
`AlgebraicGeometry.Scheme.range_snd_of_isPullback` lemma.

The proof follows all four steps of `lem-pc-proper-support-descent`:
`Scheme.schemeTheoreticSupport` supplies the closed immersion; pullback pasting
constructs its base change inside each base-changed ambient scheme; the range
formula and `Scheme.Modules.finiteType_module_support_pullback` identify its
range with module support. The two structure-independence equivalences in
`Scheme.closed_subset_proper_over_base_properties` prove that support properness
is equivalent to properness of this base change. Compactness and
quasi-separatedness follow by morphism permanence from the affine stage.
`exists_isProper_baseChange_of_isLimit` then gives the later stage.
Its map into the pullback of the identity is converted to the second projection
by composition with an isomorphism. The support comparison gives the conclusion.
No new intermediate statements, nodes, or route changes were needed.

Validation: single-file compilation through `lcompile.py` succeeds with no errors
or warnings, in approximately six seconds. Every line is at most 100 characters.
LeanFinder returned finite-presentation and finite-type sheaf declarations but
no direct proper-support-descent result. Loogle returned no matching declaration
(the query identifier was not recognized); Mathlib grep returned no relevant
proper-support/eventual-properness theorem. Source-library searches found the
existing pullback range lemma and the already-proved `ProperNoetherianStage`
assembly using eventual properness.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.exists_hasSupportProperOver_baseChange_of_isLimit`
(node `lem-pc-proper-support-descent`).
There are no sorries left in the delivered module and no new holes anywhere.
This is a proof from the four existing declarations of the plan, not a
new decomposition. Existing dependencies may themselves depend on unfinished
proofs; the delivery does not claim that their entire transitive axiom closure
is already sorry-free.

## No longer needed

None. All four original proof-dependency modules and nodes are used:
`Sheaf.Paper.SchemeTheoreticSupport`
(`lem-weil-pbc-scheme-theoretic-support`),
`Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback`
(`lem-weil-pbc-support-pullback-finite-type`),
`Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties`
(`lem-weil-pbc-closed-subset-proper-over-base-properties`), and
`Sheaf.AlgebraicGeometry.EventuallyProper`
(`lem-weil-pbc-eventually-proper`).
No original imports or public re-exports were removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement correction was needed. The DAG's four-step plan
fits the existing declarations. The unit `sk-thm-picard-semicon` has no realized
entries that this proof bypasses, and the original route is retained.
The local checkout lacks the cited Stacks TeX files, so the existing sources were
checked at https://stacks.math.columbia.edu/tag/081G and
https://stacks.math.columbia.edu/tag/0CYL.
The planned elementary base-change range identification is supplied by the
already-proved source-library pullback range lemma.

## Second reading by B3

1. I compared the delivered module with the repository version. The theorem
   signature and all existing declarations are unchanged; the only interface
   addition is the proof-only import needed by the proof.
2. I compiled the module with `lcompile.py`, checked that no `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, or `extern` remains, and probed the
   theorem axioms. The result is `propext`, `Classical.choice`, and
   `Quot.sound` only.
3. The closed theorem is exactly the DAG node statement. No split-off
   statements or new nodes were added, so there are no additional truth or
   strength concerns and no duplicate declarations.
4. The proof uses the four planned dependency declarations and the existing
   pullback range lemma. I found no shorter applicable library route and no
   unused imports or proof dependencies to prune.
5. The unit route is retained: scheme-theoretic support, support under
   pullback, independence of closed-subscheme structure, and eventual
   properness are all used in the stated order. The realized unit data is
   unaffected.

I changed only the proof of
`AlgebraicGeometry.exists_hasSupportProperOver_baseChange_of_isLimit`, added
the proof-only pullback-carrier import, and added this second-reading record.
