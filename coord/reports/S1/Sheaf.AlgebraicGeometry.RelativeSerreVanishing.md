## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_tensorPow_of_relatively_ample` without changing its signature. The local assertion `key` restricts to an affine neighbourhood, applies coherent Serre vanishing to its proper map to the spectrum, transports tensor powers through open restriction, compares module cohomology with the source H, and detects zero higher direct images on the affine base. Ordinary open base change transports this back to the neighbourhood. A finite subcover and `Finset.sup` give the global uniform bound. Empty bases are covered by the empty supremum.

Added proof imports for the existing affine zero-detection helpers in `WeilConjectures.AlgebraicGeometry.Cohomology.RelativeSerre`, coherence restriction, tensor-power restriction comparisons, and the module/source cohomology comparison. Updated the node's proof and proof dependencies to match the code. No new declarations or modules are delivered. All public imports remain unchanged.

Searches through msearch leanfinder, loogle, and grep found no Mathlib relative Serre theorem. Repository searches found the existing affine zero-detection helpers, which are reused. Single-file compilation of the complete proof passed; the delivery check also compiles with its axiom probe.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_tensorPow_of_relatively_ample` (node `lem-pc-relative-kill-by-twisting`). Added 0 holes, split off 0 statements, and left 0 direct sorries. The proof uses the already stated library results; this report does not claim that every transitive dependency is axiom-free.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`, `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`, and `WeilConjectures.AlgebraicGeometry.Cohomology.Projective`. The declarations used from Sections are available through the retained public DirectImage import and the new RelativeSerre import.

Node `lem-pc-restrict-derived-direct-image-open` and its module `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction` are unnecessary for this proof: the existing ordinary higher-direct-image open-base-change theorem suffices, avoiding passage through a derived category. Its obsolete tool-use entry is removed. The uniform high-degree vanishing theorem of Projective is not used; the quasi-coherence clause of `lem-pc-finite-support-hi` remains used by the existing affine zero-detection helper in RelativeSerre. No other original mathematical dependency is pruned. Global unreachability of these modules is not asserted because other parents may still use them.

## Where the brief, the DAG or earlier work was wrong

The original plan requested a full derived-category open-restriction comparison where the ordinary higher-direct-image comparison already suffices. Coherence restriction, tensor-power restriction, and the module/source H comparison needed explicit existing APIs; these are now recorded in the proof dependencies. The statement and the unit route are unchanged. There were no mathematical statement repairs or consumer adaptations.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
