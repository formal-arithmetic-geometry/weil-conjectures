## What changed

Replaced the hole in `WeilConjectures.IntegralSystemRealization.integralSystemDirectEvaluation`
by the canonical mate construction. Its evaluation map is the right mate of the inverse
of the existing `pullbackTensorDerivedEvaluation`, under `d.adj` and `finiteAdj`.
The unit and counit equations are proved from Mathlib's mate identities. The
restricted-direct comparison is `sfDerivedImageRestriction` transported across the
existing `originRestrictionEquality`; its heterogeneous equality is proved in Lean.
A proved private existence lemma carries out this deterministic equality transport.

Added three proved private categorical helpers in the item module: naturality of mates
under top and bottom whiskering, and transition pasting. The latter adapts the existing
categorical calculation in `CoefficientSystemUnboundedComparison` to a natural
transformation in the scalar square; it does not assume that transformation invertible.
This yields the full direct-image transition identity from a pullback quotient square,
followed by cancellation of the published scalar comparison and its inverse.

Added two proof-only imports for the smaller geometric obligations, in separate new
modules, and a proof-only import of `IntegralSystemExpressionDomain` for its existing
`originRestrictionEquality` (the adjacent scalar restriction presentation equality).
No existing signature, definition, instance, public import or consumer changes.
The item's DAG proof now records the actual canonical-mate argument.

Validation: both new statement modules compiled with lcompile, and the final item
compiled cleanly in 7.1 seconds, with zero holes. The delivered files contain no
profiling or transparency overrides. The dependency union and all three Lean
statement attachments agree with their DAG records; no dependency cycle is added.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.IntegralSystemRealization.integralSystemDirectEvaluation`
(node `lem-sf-integral-system-direct-evaluation`) by a complete proof from two new
statements. Original item: one hole before, zero holes after. This is a decomposition,
not an unconditional proof of the geometric input; two holes are added, so the local
net hole change is +1.

The added holes are exactly:

- `WeilConjectures.IntegralSystemRealization.integralDirectEvaluationMate_invertible`
  (`lem-sf-integral-direct-evaluation-mate-invertible`), only invertibility of the
  specified mate, with no construction or adjunction/transition conclusions.
- `WeilConjectures.IntegralSystemRealization.integralPullEvaluation_quotientSquare`
  (`lem-sf-integral-pull-evaluation-quotient-square`), only the pullback quotient
  square, with no system direct-image datum as an input.

Each is a named public theorem in its own module, with its entire proof `by sorry`,
a source, a complete proof in words, and a matching DAG node. The assembly's private
helpers, including the scalar-restriction equality transport, are proved and contain
no holes. No object is selected from a holed existence theorem: the evaluation natural transformation is an explicit mate; `asIso` uses only
its invertibility proof. The scalar comparison is the already published one,
transported solely across proved equalities of its restriction functors.

Edge cases checked in the statements and argument: zero complexes, index zero,
unbounded noncartesian inputs, arbitrary scheme maps, and nonflat quotient maps.
No excluded case or additional hypothesis is introduced. The pullback square uses the
inverse mate of the inverse scalar comparison, whose orientation is essential.
It accepts a heterogeneously equal normalized restriction comparison, accounting for
the propositionally equal quotient functors without making an additional choice.

## No longer needed

No original Lean import is removed: `IntegralSystemOperations` remains necessary for
the statement. The old direct proof dependencies
`lem-pur-coefficient-system-derived-comparison` and
`lem-coef-semilinear-derived-sections` are replaced in this item's `proof_deps` by the
two smaller obligations. They remain proof-plan dependencies of those obligations;
there is no claim that their modules leave the targets' closure.

An import-closure comparison confirms that `IntegralSystemExpressionDomain` adds only
itself to the existing project imports, and it contains no holes. Its other dependencies
already belong to `IntegralSystemOperations`.

The general strict-coefficient and semilinear comparison packages need not be imported
as proof dependencies of the assembly. It uses only the concrete canonical maps and
Mathlib's categorical mate calculus. No declaration or module is withdrawn, and no
unit-level route is changed.

## Where the brief, the DAG or earlier work was wrong

The existing dependencies provide comparisons in presentations with independently
chosen ordinary and derived models. They do not specialize by definitional equality
to the specified sequence-site functors and the intrinsic finite comparisons. In
particular, neither existence of an unspecified isomorphism nor invertibility of the
pullback comparison alone establishes invertibility of its right mate. The latter is
a separate geometric obligation.

The original single prose proof step also hides the identification of the scalar
comparison with `sfDerivedImageRestriction`. The new pullback square states that
identification through inverse mates explicitly. The formal pasting proof then gives
the required transition without any faithfulness assumption on derived evaluations.

Searches run through msearch: LeanFinder (8 unrelated/generic hits), Loogle on
`mateEquiv` (12 hits, used for assembly), LeanSearch (8 ordinary sheaf/evaluation
hits), and Mathlib grep (one unrelated HomComplexInduction hit). Local searches read
`CoefficientSystemDerivedComparison`, `CoefficientSystemUnboundedComparison`,
`SemilinearDerivedSections`, `CompletedPullbackTowerRealizations`, and
`CompletedPullbackTensorComparison`. Blueprint searches for evaluation direct image
and restriction pullback returned no duplicate nodes. Zheng Construction 4.1 and
the paragraph preceding Lemma 4.10 were read in the local PDF.

## New nodes

`lem-sf-integral-direct-evaluation-mate-invertible`, module
`Sheaf.SixFunctors.IntegralDirectEvaluationMateInvertible`: the finite-extension/
evaluation argument specialized to invertibility of the fixed mate. It contains none
of the adjunction equations or quotient transition conclusions of the original item.

`lem-sf-integral-pull-evaluation-quotient-square`, module
`Sheaf.SixFunctors.IntegralPullEvaluationQuotientSquare`: the pullback transition
square for the inverse mate of the inverse published scalar comparison. It concerns
only inverse image and restriction, and is independent of the arbitrary universal
derived system direct-image presentation d.

No change records are needed: all existing public interfaces are preserved.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
