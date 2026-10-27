## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.supported_kernel_image_derived_complete`
by the combination of the source kernel/image result and support preservation applied
separately to the two actual modules. The original theorem signature is unchanged.

Added `SupportedKernelImageBaseComplete`, which applies the stated principal complete
heart theorem through the exact section-action equivalence. Added
`SupportedKernelImageExtensionComplete`, which proves preservation for an arbitrary
complete module along the finite support path and the final site-object restriction.
The support proof uses the actual open/closed units and counits, joint detection of
isomorphisms, strict comparison of completion units, and exact degree-zero transport.

Added `SectionIntegralPrincipalCompletionModel` for the missing comparison between
`IsSectionIntegral` and the universal principal quotient completion model. This is a
comparison of normalized completion units for arbitrary derived objects, with no finite
local model, kernel/image, support-path, or affine hypotheses. Its complete natural-language
proof is in the docstring. It is strictly a coefficient-presentation step of the argument.
No definition or existing theorem statement was changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.supported_kernel_image_derived_complete` (1 of 1 original
holes). This is a decomposition, not a net hole closure: one new hole is added in
`AlgebraicGeometry.ProEtale.StrictCompletionRestriction.section_integral_principal_completion_model`
(node `lem-sfb-section-integral-principal-completion-model`).

The new public theorems
`AlgebraicGeometry.ProEtale.supported_kernel_image_base_complete` and
`AlgebraicGeometry.ProEtale.supported_extension_derived_complete` have complete proofs.
All private helpers have complete proofs. No sorry occurs in a definition.

Validation: `lcompile.py --all` compiled all four delivered modules without errors or
warnings (36.7 s, 37.5 s, 49.2 s, and 42.4 s respectively). The original theorem
signature and every original public import were compared verbatim and are unchanged.

The support proof includes the empty path by identity, the zero object by the exact
completion functor, and both open and closed branches. The source argument uses the
actual categorical kernel/image and the principal heart theorem, so it includes zero
maps, identity maps, nonconstant maps, and torsion models. The new comparison is valid
on the empty scheme and on zero complexes; its regularity assertion is only about the
coefficient ring.

## No longer needed

Removed direct proof imports from the item module:
`Sheaf.Paper.FiniteScalarLocalModelComplete`,
`Sheaf.Paper.StrictCompletionRestrictionComparison`,
`Sheaf.Paper.DerivedNakayamaResolution`,
`Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization`, and
`Sheaf.Paper.CondensedOpenClosedRecollement`.
The first, second, and fourth remain dependencies of the proved helper modules.
The coefficient resolution remains a planned dependency of the comparison hole.
Recollement is used through the already-proved exact support localization interface;
the standalone recollement theorem is not used directly.

No original public import was removed, no module was withdrawn, and no unit step was
bypassed. None of these direct-import removals is claimed as global module pruning.
The DAG now names the two helper statements as the item's actual direct proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The original step 2 invokes the principal quotient heart theorem after obtaining an
`IsSectionIntegral` presentation. The two interfaces do not directly coincide in Lean:
the former takes a universal `PrincipalQuotientCompletion.Model`, whereas the latter
records a strict presentation with normalized section quotient/Roos comparisons.
The new comparison statement isolates precisely the required identification and regular
coefficient scalar; no kernel/image theorem is restated under another name.

The standalone condensed recollement statement is not required by the support proof:
`condensedSupportDerivedLocalization` already supplies the exact closed-support functor,
the needed unit/counit isomorphisms, vanishing of mixed restrictions, and joint detection.

## New nodes

`lem-sfb-supported-kernel-image-base-complete` records original steps 1--2 and is proved
in `Sheaf.Paper.SupportedKernelImageBaseComplete` from finite-model completeness, the
strict section-action comparison, the new model comparison, and the existing principal
heart theorem.

`lem-sfb-supported-extension-derived-complete` records original steps 3--5 and is proved
in `Sheaf.Paper.SupportedKernelImageExtensionComplete`. It generalizes the support
calculation to any complete module; no affine condition is needed for this intermediate.

`lem-sfb-section-integral-principal-completion-model` is the one remaining hole, in
`Sheaf.Paper.SectionIntegralPrincipalCompletionModel`. It compares two canonical
presentations of the same augmented principal quotient completion, rather than asserting
any new kernel/image or support closure result. No change record is needed because every
existing signature, definition, attribute, and public import remains unchanged.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
