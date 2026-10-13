## What changed

Proved `AlgebraicGeometry.Scheme.Modules.resolutionSectionClass_zero_augmentation`
without changing its signature or any definition. Added only proved private helpers
for homology projections under exact functors, the degree-zero adjunction comparison,
homology transport, the restricted augmentation section square, and cancellation of
resolution isomorphisms. Added a proved generic complex comparison and its
private degree-zero specialization `theta_zero`. Locally controlling transparency
and homology-data unfolding makes the concrete sheafification specialization
elaborate within the single-file limit. The one public import is unchanged because
the statement needs it. Updated the node proof to this direct categorical calculation.
All added elaboration options are scoped to individual declarations; the second reader additionally scoped local irreducibility of the three homology
comparison definitions to the private `theta_zero` section. No attribute escapes
that section and the public interface is unchanged.

Source read: Stacks Project, Cohomology, Tag 01E4,
https://stacks.math.columbia.edu/tag/01E4 (lemma-describe-higher-direct-images).
Its proof identifies the cohomology presheaf of the pushed-forward resolution with
sections of the original resolution; the Lean proof establishes the degree-zero
augmentation normalization of that identification. The literal local source path
recorded by the node is absent on this machine, so the tag page was read instead.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.resolutionSectionClass_zero_augmentation`.
One of one original holes closed, zero holes added; no split-off theorems.
No `sorry` remains in the delivered module. All private helpers are proved.
No definitions or existing signatures changed. The proof uses no property of f or
F beyond their stated types; empty opens and zero sections are included.

## No longer needed

No existing import was removed: `Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices`
is the statement dependency. The planned proof dependency
`lem-weil-pbc-higher-direct-image-presheaf` and its module
`Sheaf.Paper.HigherDirectImagePresheaf` are not needed by this proof and were not
imported. Its general associated-sheaf theorem is replaced by a proved private
calculation of the degree-zero adjunction comparison. No unit statement or realized
unit proof step is bypassed: this item is below the realized nodes of `sk-thm-p1`.
The foundational definitions and left-exact resolution calculation stay needed.
This pruning is local to this item, not a claim that other callers stop needing the
higher-direct-image-presheaf module.

## Where the brief, the DAG or earlier work was wrong

The DAG cited the general higher-direct-image-presheaf theorem, but its statement
does not provide this degree-zero augmentation equation. That theorem is unnecessary:
the incoming degree-zero differential is zero, and the forgetful functor preserves
this homology. Adjunction naturality and the triangle identity then give the exact
comparison needed. The inherited attempt contained a full proof but its claimed completion was not
confirmed: compiling it hit the single-file limit. Replaced the expensive inline
specialization with a proved generic complex helper and a private `theta_zero`
lemma, supplying the homology-preservation instance explicitly and controlling
transparency only around that specialization. The resulting complete module
compiled with no warnings. The compiler wrapper queues jobs before starting its
60-second compile limit; its reported elapsed time includes that queue wait.
No mathematical statement was found false or changed.

## Second reading by U2

1. Compared the delivered module with the repository version. The public theorem signature and existing declarations are byte-for-byte unchanged; only the proof body and private helpers were added. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or warnings. Searched the delivered file for forbidden constructs and `sorry`; none remain. A scratch copy with `#print axioms AlgebraicGeometry.Scheme.Modules.resolutionSectionClass_zero_augmentation` compiled successfully and reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Checked the proof route and helper statements against the imported declarations and DAG node. The private categorical lemmas are true intermediate identities, strictly smaller than the target, and no split-off theorem was added. Verdict: pass.
4. Checked pruning and imports. The sole public import remains needed for the statement; the proof does not rely on the planned higher-direct-image-presheaf module, as recorded above. The realized unit route is retained. Verdict: pass.
5. Checked the node metadata against the proof and report. The theorem, proof steps, dependencies, source, and unit agree; no statement or definition change record is needed. Verdict: pass.

Changed the private `theta_zero` section by adding section-local irreducibility
attributes for `ShortComplex.mapHomologyIso`, `ShortComplex.mapCyclesIso`, and
`ShortComplex.homologyMap`. The original delivery compile timed out twice; the
scratch copy with these settings compiled successfully. These settings limit
elaboration unfolding and end at the section boundary. No signature, definition
body, import, mathematical argument, or DAG route changed. Added this reading
record and the explicit axiom-check result.

Change record: `coord/changes/resolution-section-class-zero-augmentation-elaboration.md`.
This records section-local elaboration attributes only; no statement or definition changes.
