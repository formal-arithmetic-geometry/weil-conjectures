## What changed

Proved the ten original holes in `Sheaf.Paper.WeilTensorProduct`, keeping their
statements and the unit's K-flat tensor/completion/rationalization route.
The proof uses resolving localization, the completion reflector and normalized
quotient-completion comparisons, the actual coefficient-preserving pullback,
and tensor-product extension of bilinear Hom maps.

Added `Sheaf.Paper.ProEtaleTensorModelLinear`: sectionwise tensor and totalization
are coefficient-linear, and this descends through the homotopy quotient and the
flat-term K-flat localization. This is a proved mathematical lemma needed for
rational tensor, not a new assumption.

The site tensor now uses a reordered existential specification and a named total
functor to retain totalization instances. The normalized representative comparison
and its uniqueness are proved. See
`coord/changes/J4-wfSiteDerivedTensor-interface.md` for the definition change,
consumer list, and semantic-review requirement.

The rational Hom action is now explicit tensor-product base change.
`wfRationalTensorHom_eq_choose` proves equality with its former unique-witness
construction. See `coord/changes/J4-wfRationalTensorHom-explicit.md`; its target
semantic review is also reopened.

Validation: both delivered modules and all seven external direct consumers of
`wfSiteDerivedTensor` compiled cleanly against the revised definitions. The main
module took 48.6 seconds in that check. All ten original theorem signatures are
unchanged; both delivered modules contain zero `sorry` tokens. No external
consumer needed adaptation.

## Proved and sorry left

Closed the ten original holes, by declaration:

- `SheafOfModules.wfSiteDerivedTensor_first`.
- `AlgebraicGeometry.Scheme.wfTensorRepresentative_exists`.
- `AlgebraicGeometry.Scheme.wfRationalTensorHom_exists`.
- `AlgebraicGeometry.Scheme.wfIsoPullback_complete`.
- `AlgebraicGeometry.Scheme.wfCompletePullback_linear`.
- `AlgebraicGeometry.Scheme.wfPullbackCompletion_exists`.
- `AlgebraicGeometry.Scheme.wfRationalTensorPullback_exists`.
- `AlgebraicGeometry.Scheme.wfConstructible_complete`.
- `AlgebraicGeometry.Scheme.wfConstructibleInclusion_exists`.
- `AlgebraicGeometry.Scheme.wfConstructiblePullback_obj`.

Holes added: zero. Holes remaining in either delivered Lean module: zero.
`AlgebraicGeometry.Scheme.proEtaleTensorModel_linear` and all new helpers are
proved. Existing imported dependencies may still contain their previously stated
holes; this delivery adds none and does not replace any proved source declaration.

## No longer needed

None. All original public imports remain. The node had no numbered proof plan to
prune. Its K-flat descent, completion and actual coefficient-transport dependencies
remain needed. In particular, the first-argument computation theorem stays: other
modules use it even though the normalized tensor-model comparison is proved by
localization directly.

## Where the brief, the DAG or earlier work was wrong

No original statement was weakened or disputed. The DAG lacked the explicit
coefficient-linearity result needed to extend tensor to raw localized Hom modules;
the new node records and proves it.

Completion compatibility is obtained from direct image, quotient towers and its
adjunction with the actual pullback. It does not assume in advance that pullback
preserves complete objects. The completed coefficient identification is checked
at every finite quotient to prove scalar compatibility.

The generic tensor's original nested choice presentation caused repeated
elaboration of totalization instances. Its revised existence interface retains the
same normalized localization construction. Target statements are unchanged;
semantic review is reopened for the definition's consumers as the contract requires.

## New nodes

`lem-wf-proetale-tensor-model-linear`, in the same chapter and unit as
`def-wf-tensor-product`, records additivity and coefficient linearity of each
partial functor of any normalized pro-etale tensor model. Its proof is complete,
including the resolving-subcategory calculus of fractions and localization
transfer; it leaves no separate proof item. Change record:
`coord/changes/J4-wfSiteDerivedTensor-interface.md`.

`lem-wf-bilinear-scalar-extension`, in the item module, records the explicit
base-change construction of the bilinear Hom action and its uniqueness. Every
attached declaration is proved; no additional proof item or hole is introduced.
Change record: `coord/changes/J4-wfRationalTensorHom-explicit.md`.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
