## What changed

Proved `CategoryTheory.site_epimorphic_family_iff_cover_lifts` in
`Sheaf.CategoryTheory.Sites.EpimorphicFamilyCoverLifts`, with the original statement
and public imports unchanged. Added a proved private covering-refinement helper.
The forward direction uses the already proved `small_sheaf_coproduct_labels` to
obtain a coproduct model and its local labels. The induced map from that model
is epi because the chosen coproduct map factors through it. Composing its local
surjectivity with the labelled-section map and refining its image sieve gives
an actual covering with the requested labelled lifts. The reverse direction
uses separatedness, lifted Yoneda and sheafification uniqueness.

Updated the item's DAG proof and origin to match this implementation. All five
previous proof dependencies remain used. No other existing module was changed.

Validation: `lcompile.py` compiled the item cleanly in 7.0 seconds. A textual
comparison confirmed that the theorem signature and public imports are unchanged.
The delivery preflight additionally checks every declared constant’s axioms.

Searches: LeanFinder for epimorphic coproducts over a sheafified representable
returned the general epi/local-surjectivity lemmas and generating-sheaf results;
Loogle for `"isLocallySurjective", "epi"` confirmed the existing criterion;
Mathlib grep for `epimorphic.*cover|cover.*epimorphic` had only a coherent-site
comment. Local searches of both library roots found no replacement for the
whole equivalence. Read the actual declarations of all recorded dependencies
and Stacks Sites `lemma-quasi-compact` and
`lemma-covering-surjective-after-sheafification`.

## Proved and sorry left

Closed the single hole in
`CategoryTheory.site_epimorphic_family_iff_cover_lifts`
(node `lem-trf-site-epimorphic-family-cover-lifts`). Added zero holes;
zero holes remain in the delivered module. No split-off statements.

## No longer needed

None. Both proof imports are used, the existing public imports are retained,
and every recorded proof-dependency node is used. The explicit inverse pair
between two coproduct models from the original plan is unnecessary: factoring
the chosen coproduct map through the model suffices to transfer epimorphy.
The two successive local refinements are composed by Mathlib's local-surjectivity
composition lemma before choosing the actual cover. No module or node is pruned.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The original proof plan is valid but needs neither
the full coproduct comparison isomorphism nor an explicit dependent-sum
presentation of two successive covers. The private refinement proof uses the
recorded presieve-bind composition axiom, without assuming composition for
arbitrarily repeated indexing families or global pullbacks. The cover index is
lifted into `Type (max u v w)`. No nonempty-cover, nonempty-index or subcanonical
hypothesis is used. Empty covers and the empty family are handled by the same
separatedness and local-label arguments.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
