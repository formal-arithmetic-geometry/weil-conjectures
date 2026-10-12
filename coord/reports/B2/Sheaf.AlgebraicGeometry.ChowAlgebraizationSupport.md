## What changed

Completed the earlier reduction of
`AlgebraicGeometry.chow_algebraization_pushforward_support`, keeping its signature unchanged.
Its Lean proof unpacks the original proper support, obtains closed pushforward support
contained in the image, applies the existing image-properness conjunct, and then applies
its closed-subset-properness conjunct. The remaining closedness/containment obligation is
in the new module `Sheaf.AlgebraicGeometry.PushforwardSupportClosed`.

Repaired the new node's signature record, ran the three required kinds of search, and
recorded the unavailable LeanSearch service without an absence claim. Expanded the helper's
proof in words to explain the closed image, the zero-stalk-to-zero-section argument, and
shrinking stalk representatives. Checked the source online at Stacks Tags 088E and 02O5.
Updated the parent node's proof to match the actual Lean composition.

Removed two unused direct proof imports from the item. Both sandbox modules compile with
`lcompile.py --all`; the only warning is the named helper theorem's intended `sorry`.
No statement or definition was changed, and no other existing module was adapted.

## Proved and sorry left

Closed the item's sole direct hole:
`AlgebraicGeometry.chow_algebraization_pushforward_support`
(node `new-chow-algebraization-support`). Its proof is complete Lean, using the existing
closed-subset properness theorem and the new support lemma.

Added one lower hole:
`AlgebraicGeometry.pushforward_support_closed_subset`
(node `new-chow-pushforward-support-closed`), whose entire proof is `by sorry`.
This theorem asserts only support closedness and containment and has no base S or
proper-over-base conclusion. The parent supplies both properness steps. This is a
one-hole-to-one-hole decomposition, not a sorry-free proof or a net hole reduction.
There are no remaining direct sorries in the item's module; imported declarations may
still depend on sorries.

## No longer needed

Removed the direct imports
`Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase` and
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex` from the item.
The parent's proof no longer uses nodes `lem-weil-pbc-module-support-proper-over-base`
or `lem-pc-coherent-hi` directly, and its `proof_deps` now names the support sublemma and
`lem-weil-pbc-closed-subset-proper-over-base-properties` only.

`lem-pc-coherent-hi` remains a mathematical dependency of the new support sublemma;
it is not claimed globally unnecessary. The module-support characterization is not used
in this reduction. Transitive imports and other targets can still reach both modules;
no whole-library pruning claim is made. No unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's node record included `:= by sorry` in `lean.statement`, contrary
to the required signature-only record. Its search records omitted LeanSearch, and the
report incorrectly said the target was proved without distinguishing decomposition.
It also supplied a premature second-reading section; that section has been removed.
The earlier docstring did not explicitly justify the open complement of the support
image; properness of q makes that image closed. The expanded proof explains this.

The previously reported "nothing is proved" failure did not recur. The current dry
check recognized the reduction and identified the two node metadata defects above.
The original plan's coherence and proper-support characterization declarations alone
do not state the direct-image support containment; the new node isolates that missing
part. The existing higher-direct-image coherence theorem does not supply containment.

## New nodes

`new-chow-pushforward-support-closed`, in
`dag/nodes/sec-proper-base-change/new-chow-pushforward-support-closed.json`, states the
closedness of the proper coherent pushforward's support and containment in the image
of its source support. Its signature is strictly a part of the parent argument.
The source is the support paragraph of Stacks Theorem 088E and Proposition 02O5;
its proof plan cites the existing coherence and finite-type-support nodes. Empty source,
empty target, and zero module cases are covered by the same sheaf argument. No object
is chosen in a definition from this unproved existence assertion.

## Second reading by B2

1. Compared the complete parent module against the repository with diff, and checked its
   declaration signature byte for byte by script: identical. Only proof and plain proof
   imports changed. The other module is new. No definitions or existing interfaces changed.
2. Compiled both modules locally with lcompile.py. Scratch copies with #print axioms for
   both declarations reported exactly propext, Classical.choice, Quot.sound and sorryAx.
   The sole new sorry is the named public helper listed above; no prohibited declarations,
   hollow definitions, or arbitrary data choices occur. This remains a decomposition,
   with one parent hole closed and one lower hole added, not a net hole reduction.
3. Read the entire helper statement and its natural-language proof. It is true: properness
   closes the image of C, zero stalks imply zero sections on its open complement, and
   proper coherent pushforward has closed support. Empty schemes, zero F, and identity q
   cause no exception. Verified Stacks [088E](https://stacks.math.columbia.edu/tag/088E),
   [02O5](https://stacks.math.columbia.edu/tag/02O5), and
   [056J](https://stacks.math.columbia.edu/tag/056J). Independent LeanFinder, Loogle and
   Mathlib grep searches, plus project searches using stalk vanishing and coherent
   pushforward terminology, found no matching theorem. ClosedPushforwardStalks handles
   closed embeddings only. The helper removes the base and both properness obligations;
   it is strictly a part of the argument, not a renaming of the parent. Closing it would
   require formalizing both the general closed-map stalk argument and coherence bridge;
   there is no immediate existing theorem closing it in a few minutes.
4. Read the proof top down and both properness conjuncts it uses. The composition is
   direct, and the old dependency list is fully accounted for under No longer needed.
   Read sk-thm-p1.json and its realized fields: neither the parent nor the pruned direct
   dependencies realize a unit step; the unit route is preserved. Removed the helper's
   redundant public ClosedSubsetProperOverBase import: its statement needs no proper-over-
   base definition. Remaining public imports supply its statement's types and classes.
5. Compared the parent node against its baseline: only proof and proof_deps changed.
   Both proof steps match the Lean. The new node has its source, complete proof plan,
   dependency union, proof_origin, search records, creation/blueprint fields, chapter,
   unit, and exact signature-only Lean record. Added this reader's independent searches.

Second reading changes: pruned the new helper's redundant public import; added independent
search records and this review. No proof repair or signature change was necessary.
