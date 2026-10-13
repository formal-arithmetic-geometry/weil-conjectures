## What changed

Repair of the returned delivery: removed the duplicate private theorem
`CategoryTheory.pullback_kernel` and replaced its single use in
`quotient_kernel` with the existing
`CategoryTheory.BigradedExactCouple.pullback_kernelSubobject`. Added the
proof-only `import all Sheaf.CategoryTheory.DerivedCoupleKernelIdentities`
to access that private theorem, and recorded its node
`lem-sp-derived-couple-kernel-identities` in the proof dependencies. The import
direction check confirms that this introduces no cycle. No existing public
signature or visibility changes.

Proved `CategoryTheory.filteredStationary_cycle_comparison` in its original module,
with its original statement, visibility, public imports and docstring. Added only
proved private helpers. Actual cycles cover the graded cycles by the existing
representative-cover theorem at the stationary upper bound. A direct image and
inverse-image calculation identifies both projection kernels; two applications
of `Abelian.epiDesc` construct inverse comparison maps and give the required
representative equation.

Added proof-only imports of `FilteredComplexDifferentialRepresentativesCover`,
`FilteredNormalizedQuotientPresentation` (with `import all`, to reuse its proved
private subobject calculations), `FilteredCohomologyImage` (for its constructed
image filtration), and `Mathlib.CategoryTheory.Abelian.Exact`. Updated the item's
node proof, proof dependencies and proof origin to describe these calculations.
The normalized presentation's object-only `Nonempty` theorem is never applied:
we reuse its proved private `map_pullback_mono`, `subobject_modular`,
`pullback_exists_isCokernel`, and `filtered_preimage` declarations. The
cohomology-image finiteness theorem is not applied either; its module supplies
only the image-filtration definition. No public helper or new node is added.

The resumed worker checked the existing attempt against the original theorem,
all seven remaining helper proofs and the imported declarations. The theorem signature is
textually unchanged; the node changes only `proof`, `proof_deps` and
`proof_origin`. A fresh single-file compile and delivery dry run both pass;
the dry run prints OK, awaiting the independent second reading, and pushes nothing.

The final single-file compile completes without warnings. All constructors are
actual image, cycle, cokernel and kernel constructions. The chosen cover is
used only within the proof of a proposition. The argument retains zero objects,
zero graded pieces and r=1 without extra assumptions or elementwise lifting.

## Proved and sorry left

Closed the original one hole:
`CategoryTheory.filteredStationary_cycle_comparison`
(`lem-weil-pbc-stationary-cycle-comparison`).

No `sorry` remains in the item's module. No holes added or split off: this is
one proof, not a decomposition. All seven remaining local helpers are fully proved.
The delivery dry run performs the axiom probe of every declaration.

## No longer needed

The duplicate local `CategoryTheory.pullback_kernel` proof is removed; its
existing library theorem is now used directly. No additional module is pruned
by this repair.

Removed the proof import `Sheaf.CategoryTheory.FilteredStableSubquotient` and
the corresponding proof dependency `lem-sp-filtered-stable-subquotient-at-bounds`.
Its unnormalized object isomorphism supplies no representative equation and
is unnecessary for the explicit kernel/descent construction.

Comparing this module's source import closure before and after the proof removes
these five modules from this route (other targets may still need them):

- `Sheaf.CategoryTheory.FilteredStableSubquotient`
  (`lem-sp-filtered-stable-subquotient-at-bounds`);
- `Sheaf.CategoryTheory.FilteredCohomologyImagePresentation`
  (`lem-sp-filtered-cohomology-image-presentation`);
- `Sheaf.CategoryTheory.FilteredCohomologyImageNormalized`
  (`lem-sp-filtered-cohomology-image-normalized-quotient`);
- `Sheaf.CategoryTheory.FilteredCohomologyImageCycleMap`
  (`new-cohomology-image-cycle-map`).
- `Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries`
  (`lem-sp-filtered-complex-first-page-cycles-boundaries`).

`FilteredNormalizedQuotientPresentation` remains needed for its proved private
subobject lemmas, and `FilteredCohomologyImage` remains needed for its definition.
`FilteredComplexPageDifferential` and the filtered-complex subquotient definitions
remain needed for the existing statement. The cover module remains needed.
There are no bypassed unit realizations: `sk-prop-h2` has empty realized lists;
only the internal stationary-comparison calculation changes.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the already-stated private pullback-kernel
identity in `DerivedCoupleKernelIdentities`. The binders agree exactly; this
repair imports and applies the existing theorem rather than reproving it.

The old second step referred to `stableSubquotient_at_bounds`, whose statement
provides only a `Nonempty` object isomorphism, not its action on representatives.
It cannot by itself justify the displayed equation. The new proof explicitly
computes the kernels and constructs the normalized comparison by cokernel
descent. The original theorem statement remains unchanged.

The source of `cohomologyImage_cycle_map` is present but its compiled module is
absent from the available last green build. Rather than depend on it or copy its
statement as a new hole, the delivery proves the needed inverse-image identity
as the private helper `filtered_class_preimage` using existing compiled generic
lemmas. The final proof imports no unavailable module.

Read Stacks online at Tag 012K, in particular Equation the project server and the explicit
cycle and boundary formulas, and Tags 012Q and 012W. The literature checkout is
not populated on this machine; the proof origin is marked agent-written.
Searches were run through msearch (LeanFinder, Loogle and grep), plus source
searches in Mathlib and both library roots. No existing compiled declaration
provides the complete stationary representative comparison.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module with the repository version. The target
   statement, visibility, and existing declaration signatures are unchanged;
   only proof-only imports, private proof helpers, and the recorded node route
   differ.
2. Compiled the module with `lcompile.py`; it succeeds with no warnings. The
   module has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow
   definition. The proof uses only explicit image, pullback, kernel, cokernel,
   and epi-descent constructions.
3. Checked the private calculations and searched the library/Mathlib for an
   existing complete comparison theorem. No new split-off statement was added;
   the original theorem is proved directly and its edge cases are covered by
   the categorical universal properties.
4. Verified pruning: the stable-subquotient import and its dependent route are
   removed, while the cover, normalized-presentation calculations, image
   filtration, and page differential remain. The unit realization is not
   bypassed.
5. Compared the DAG node with the Lean proof. Its proof steps, dependencies,
   and origin now describe the actual cover and kernel/descent argument, with
   the original statement intact.

Changed only the proof route and proof-only imports, updated the existing node
metadata accordingly, and added no holes or nodes.

## Second reading by N1

1. Compared the sandbox module with the repository version. The target theorem
   signature, existing declarations, and public visibility are unchanged;
   only proof imports, private helpers, and proof metadata differ. Verdict:
   pass.
2. Compiled the module with `lcompile.py`. It succeeds without warnings, and
   the source contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   hollow definition. Verdict: pass.
3. Checked the proof and edge cases, and searched Mathlib and the library for
   an existing comparison theorem. The stationary kernel calculation proves
   the unchanged statement directly; no split-off statement was added.
   Verdict: pass.
4. Checked pruning and the unit route. The obsolete stable-subquotient import
   and dependent route are removed; the cover, normalized-presentation
   calculations, image filtration, and page differential remain. No unit
   realization is bypassed. Verdict: pass.
5. Compared the DAG node with the Lean proof. Its proof steps, dependencies,
   and origin match the actual imports and helper calculations, while the
   statement remains unchanged. Verdict: pass.

Changed only proof code, proof-only imports, and the existing node's proof
metadata; no holes or nodes were added.
