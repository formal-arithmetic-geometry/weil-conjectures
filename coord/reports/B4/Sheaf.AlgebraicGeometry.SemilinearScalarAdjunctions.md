## What changed

Replaced the proof hole in `AlgebraicGeometry.ProEtale.VaryingRing.ordinaryScalarAdjunctions`
by an assembly of the prescribed level comparisons and adjunction mates. Direct image is
constructed from the existing normalized direct-image comparisons, with successor-transition
compatibility and the required pointwise heterogeneous section identity. The inverse mate is
identified level by level with the existing invertible scalar/pullback comparison. The open
comparison is constructed from a second inverse mate; its invertibility follows from the
varying-ring open unit and preservation of ordinary single-sheaf open support.

Added `Sheaf.AlgebraicGeometry.ScalarRestrictionOpenSupport` for that remaining support step.
Added the fully proved native-carrier normalization
`Sheaf.AlgebraicGeometry.SemilinearEvaluationDirectSections`; it reuses
`moduleEvalP_existsUnique` and adds no hole. Its separate module avoids repeated expensive
normalization of continuous-module section carriers. Also extracted the fully proved successor-compatibility lemma
`Sheaf.AlgebraicGeometry.SemilinearScalarDirectTransitions` after a fresh delivery compile
exceeded the per-file limit. It proves the component square from the existing restriction
transition equations and the section formula for pushed morphisms; it adds zero holes.
All added imports of the item are private
proof imports. No existing public signature, definition, instance, attribute or public import
changes. Private component equations and an explicit view of pushed sections expose
section-preserving functor projections without changing shared definitions. In the transition
module, private level-section functions give one consistent raw carrier for the section
calculation; this reduced that module from over the limit to a 17.6-second debug compile. No consumer needs
adaptation, and no adopted source-library file changes.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.VaryingRing.ordinaryScalarAdjunctions` from the smaller support
statement. There are zero holes left in the item module.

Added one hole:
`AlgebraicGeometry.ProEtale.StrictTower.restrictScalars_openCounit_isIso`, in
`Sheaf.AlgebraicGeometry.ScalarRestrictionOpenSupport`, node
`lem-sf-scalar-restriction-open-support`.
Its docstring gives the localized direct-sum and sheafification proof, including empty and
identity opens and zero coefficients. The statement concerns only a single coefficient level
and an individual extended sheaf. It has no semilinear systems, arbitrary restriction package,
tower comparisons, natural isomorphism package, or unit-normalization conclusion.

This is a decomposition: one original hole closed, one strictly smaller hole added, net zero
holes removed. The new
`AlgebraicGeometry.ProEtale.VaryingRing.moduleEvalP_sections_heq` is proved from the existing
normalization; it adds zero holes. The new
`AlgebraicGeometry.ProEtale.VaryingRing.ordinaryScalarDirectComponents_step` also has a
complete proof and adds zero holes. Every helper in the item has a complete proof.

Validation: the final remote `lcompile.py --all` run compiled all four modules successfully
and accepted their per-file checking times. The delivered transition module has no profiling
options and uses the default heartbeat limit.
The comparison record and the signatures of
`ordinaryScalarAdjunctions`, `OrdinaryScalarAdjunctions.unit`, and
`OrdinaryScalarAdjunctions.counit` were checked verbatim against the current source.
The retained hypothesis `hψ` is redundant once the supplied restriction package C provides
its prescribed coherent transitions; its binder remains unchanged.

## No longer needed

No module is withdrawn, and no original public import is removed.

The item does not use `lem-coef-semilinear-derived-sections`: the existing underived
coefficient-change API and the evaluation mate normalization directly prove the inverse-image
step. It also needs no separate application of the full
`lem-cbc-strict-tower-proper-open-calculus`; only the operations and the varying-ring open unit
are used in this assembly.

`def-weil-extension-by-zero-presheaf`, `def-weil-presheaf-modules-sheafification`, and
`lem-pur-site-restriction-module-adjunction-exact` move from direct proof dependencies of the
item to the source proof of the new single-sheaf support lemma. They remain needed there and
are not claimed as globally pruned. No source-tree declaration is removed or given a hole.

## Where the brief, the DAG or earlier work was wrong

The original statement is preserved. The DAG's inverse-image construction can use the already
proved single-ring scalar/pullback mate API; rebuilding its sheafification argument is
unnecessary. The updated proof records the mate-pasting route actually used by Lean.

`Sheaf.Paper.SemilinearOpenRestrictionSupport` cannot discharge the new support step: it
imports the present item and obtains its support comparison from `ordinaryScalarAdjunctions`.
Using it here would be circular. The new support lemma instead cites the localized extension
presheaf and module-sheafification construction directly.

The unit route is retained. The ordinary part of
`lem-weil-pbc-ring-sheaf-change-adjunction` is used as a generic coefficient-change tool;
it supplies the normalized single-ring direct-image comparison and invertible inverse mate,
not a replacement for a step of the six-functor unit. The new node similarly uses the generic
localized-site extension adjunction already cited by the parent. There are no statement
repairs or forced adaptations.

## New nodes

`lem-sf-scalar-restriction-open-support` states invertibility of the B-open counit on the scalar
restriction of an A-open extension. Its source is Stacks 03DI/03DJ and 03CY; its proof is the
identity on localized direct-sum summands, followed by sheafification and adjoint uniqueness.
The node records LeanSearch, LeanFinder, Loogle and Mathlib source searches, its Lean attachment,
and the inherited blueprint origin. It is strictly a part of the open-extension argument.

`lem-sf-scalar-evaluation-direct-sections` is a proved native-carrier version of the existing
direct-image evaluation normalization. Its public declaration is
`AlgebraicGeometry.ProEtale.VaryingRing.moduleEvalP_sections_heq`, in
`Sheaf.AlgebraicGeometry.SemilinearEvaluationDirectSections`. It makes no mathematical choice
and introduces no new assumption or proof hole; its proof applies the normalization of
`moduleEvalP_existsUnique`. Its separate file isolates the expensive carrier normalization
after adding private section APIs in the item. The node records all four search methods.

`lem-sf-scalar-direct-transition-compatibility` proves the successor square for a family of
component isomorphisms normalized by the prescribed level identifications. Its proof uses
`C.transitions` on both schemes, the actual product base-change map, extensionality, and
cancellation by a pushed isomorphism. It records all four searches, introduces no hole, and
is strictly the transition step of the direct-image construction.

No change record is needed: no existing statement, definition or exported interface changes.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
