## What changed

Replaced `completedCoefficientOrdinarySquare_exists` with a construction of the normalized
ordinary square. The underlying isomorphism is `eS.underlying` followed by direct image of
`eX.underlying.symm`. The proof checks its linearity on pure tensors of local sections,
packages it with `Mod.isoMk`, proves naturality using the two given natural comparisons,
and proves the prescribed normalization by inverse cancellation.

Added private proof import `Sheaf.Paper.CompletedCoefficientPushAction` and three new modules:
`CompletedCoefficientSectionAction` records the single-site action identity and explicitly
constructs the section action and normalized scalar comparison, with a proved generic
section-action formula for direct image, a generic sectionwise linearity criterion, and
a typed inverse scalar section map with its proved cancellation law; `CompletedCoefficientScalarPush`
records the coefficient-only compatibility with direct image.
`CompletedCoefficientPushAction` proves the supporting section-action calculation through
completed direct image and records its underlying map as an explicit isomorphism. This
isolates an expensive definitional comparison behind a typed API. No existing shared module,
public import, definition, or theorem signature was changed. Updated the item's proof plan
to the actual construction.

Validation: `lcompile.py --all` accepted all four modules under the server's per-file
60-second check. Profiling options were removed before delivery. The parent has no
remaining hole. Its formal proof includes two separate action calculations followed
by scalar surjectivity, pure-tensor extensionality, naturality, and normalization.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedCoefficientOrdinarySquare_exists`
(node `lem-diagonal-completed-ordinary-square`). No sorry remains in the item module.

Added two holes, each the entire proof of its named theorem:

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedRealization_section_action`,
  node `lem-sfb-diagonal-completed-section-action`.
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedRealization_scalar_push`,
  node `lem-sfb-diagonal-completed-scalar-push`.

This is a decomposition: one original hole closed, two strictly smaller holes added;
net hole count increases by one. It is not a claim of a sorry-free coefficient comparison.
The first residual statement has one scheme, one realization, and no direct image. The
second concerns only the coefficient rings and the regular module, with no arbitrary
module or natural-isomorphism conclusion. The parent supplies the actual combination.

The section-action, scalar-comparison, and typed section maps are concrete composites
of existing maps; neither chooses data from an unproved existence statement.

## No longer needed

No import or module was pruned. The original public import of
`Sheaf.Paper.DiagonalCompletedPushSquare` is still needed for the statement.
The original direct proof dependency `det-prop-sfb-qlbar-colimit-x-pullback` now belongs to
`lem-sfb-diagonal-completed-scalar-push`; it remains mathematically needed and is not claimed
as pruned. No upstream declaration was removed or altered. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan correctly separates linearity from the formal naturality argument, but
its declared inverse-image coefficient comparison does not itself assert how an arbitrary
`CompletedRealization` transports module actions. That is the single-site residual statement.
The finite-projection/unit-normalization comparison also needs to be identified with the
actual coefficient map used by completed ringed direct image; the second residual statement
makes this precise. Neither has been assumed as an additional hypothesis of the item.

The search inspected the actual `sfb_integral_comparison_pullback` signature, Mathlib's
module-sheaf APIs, and the internal module-object action/forgetful APIs. Search service
results were general free-module and adic-completion statements, not either residual
statement. Blueprint searches for coefficient actions found no duplicate assertion.

The concrete condensed coefficient morphism contains an adjunction mate. Its section
application was expensive to normalize repeatedly during kernel checking. The generic
`SheafModuleSection.pushScalar` definition supplies the same section map to both the
pushforward action formula and `condensedPushScalarSection`. The remaining typed section
wrappers expose the original module carriers. This fixes the checking cost inside the
new modules without changing any shared definition or transparency option.

Edge cases checked when stating the residual lemmas: the empty scheme (all section
identities are between the unique sections), identity morphisms (the coefficient equation
compares the two prescribed unit normalizations), zero modules (both action sides are
zero), and prime two (no division by two or sign convention is used). No noetherian,
properness, or invertibility hypothesis has been introduced. Any scheme-specific line
existence hypotheses remain contained in the supplied realizations.

## New nodes

`lem-sfb-diagonal-completed-section-action` extracts the local scalar-action assertion from
the first step of the original plan. Its source and proof in words are in the module's
docstring. Its supporting constructions use the existing internal action and the given
underlying/unit isomorphisms.

`lem-sfb-diagonal-completed-scalar-push` extracts the coefficient-ring compatibility: the
condensed direct-image coefficient map composed with the normalized scalar comparison is
the normalized comparison applied to the completed direct-image coefficient action on one.
Its proof uses finite projection normalization and integral coefficient pullback compatibility.

`lem-sfb-diagonal-completed-push-action` is a proved supporting node: single-site action
transport specialized to a completed pushforward, with inverse cancellation and the
restriction-of-scalars action computed on sections. It adds no hole.

No change record is required: only the item, new modules, and their nodes were changed.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
