## What changed

Proved `CategoryTheory.pur_inverse_image_compatible_free_tower` with its original signature.
The five-step unit route is retained: compatible local bases give the limit basis;
the normalized slice inverse image transports it; projection equations give the
local comparison; the image covering detects invertibility; projections give naturality
and uniqueness. Scalar actions and their compatibility are proved categorically.

Added and proved `CategoryTheory.unit_normalized_slice_inverse_image` in
`Sheaf.CategoryTheory.Sites.NormalizedSliceInverseImage`. It constructs the slice
functor from the sigma presheaf and fibres after actual Kan extension and sheafification.
For restricted global sheaves the sigma presheaf is a binary product. Preservation
of that product makes the second projection a fibrewise bijection. Naturality of
the actual units supplies the required normalization. No arbitrary existence
witness chooses data. All auxiliary declarations are private and fully proved.

Replaced the proof import `Sheaf.Paper.SliceSiteLocalization` with the proved
normalized comparison; added proof imports for flat Kan extension and AB5 in Types.
All original public imports, signatures, and definitions remain unchanged.
The new module also uses the existing Mathlib sheaf and binary-product APIs.
Both modules compile independently through lcompile.py with no warnings.
Explicit #print axioms checks of both public theorems report exactly
propext, Classical.choice, and Quot.sound; no sorryAx or additional axioms.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.pur_inverse_image_compatible_free_tower`
(node `lem-pur-inverse-image-compatible-free-tower`).
Also proved the retained auxiliary theorem
`CategoryTheory.unit_normalized_slice_inverse_image`
(node `lem-pur-unit-normalized-slice-inverse-image`).
No holes remain in either module; no holes were added, and none are split off.
This is a proof, not a decomposition. Definitions contain no holes.

## No longer needed

Removed `import Sheaf.Paper.SliceSiteLocalization` and the direct proof dependency
`lem-weil-pbc-slice-site-localization`. The new normalized comparison uses neither
that theorem nor `lem-weil-pbc-localized-sheaves-over-representable` or
`lem-weil-pbc-slice-sheaf-inverse-image-equivalence`. Its direct sigma/fibre
construction avoids their precoverage and universe interfaces altogether.
No claim is made that these modules are globally unreachable through other parents.

The tensor theorem `CategoryTheory.siteInverseImage_tensor` is not applied;
its node is absent from the main proof dependencies, but it remains a statement
dependency and its original public import remains. Finite-limit preservation here
comes from flat Kan extension and Mathlib sheafification. The ringed-module and
sectionwise-limit dependencies remain necessary for the existing definitions.
The sheaf local-bijection criterion is applied from Mathlib. No blueprint unit is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original slice localization theorem supplies only an unnormalized isomorphism
in Type (max u v), with the older stable-precoverage assumptions. The item requires
an explicit actual-unit equation in Type (u+1), under IsSiteForCoverings. This is
an interface gap, not a counterexample. Continuity is proved from the covering
axioms; the direct sigma/fibre proof handles the larger universe and normalization.
The retained attempt had left that comparison as a hole; it is now proved.

The original hK binder is unused by this proof and retained verbatim, with the
unused-variable linter disabled only for the original theorem. No target changes.
Edge cases include empty or singleton coverings, empty section types, arbitrary
Grothendieck topologies, and degenerate sigma fibres; the universal-property proofs
require no nonemptiness assumptions. The slice construction itself needs only
flatness; continuity remains in the stated signature.

Earlier dry runs were interrupted while waiting for shared worktree capacity.
On resumption both modules passed lcompile.py. The first completed preflight
requested a change record for a new module-wide elaboration option. Scoped that
option to each new private declaration and the original theorem instead; the
original module command interface is now identical. No statement, definition,
or downstream module requires adaptation. Final validation uses the unchanged
delivery tool.

## New nodes

`lem-pur-unit-normalized-slice-inverse-image` is a proved, strictly narrower
categorical ingredient, with no tower, coefficient, basis, or limit-comparison
hypotheses. Its source is Stacks 03CF's product calculation. The node and docstring
record the actual sigma/fibre construction and unit equations; the three search
kinds are recorded. There are no definition or statement repairs and no change records.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
