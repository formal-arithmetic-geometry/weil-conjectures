## What changed

Proved `WeilConjectures.zlFiniteCompletedImageComparison` without changing any public
signature or definition. Two proved private helpers handle exactness for the actual
ring map and the comparison over an arbitrary base field in which the coefficient
prime is a unit. The latter is applied to the given finite map and each finite
geometric base change, including empty fibres.

The displayed derived functor is the existing completed right derived direct image.
Its inverse cochain resolution unit supplies `factors`; exactness makes that unit an
isomorphism at every complex. The comparison is the identity, with the prescribed
resolution normalization. The existing completed derived product-preservation and
Roos transport helpers construct the required boundary and triangle with exactly the
specified projections. Constructibility and reduction follow from
`sfIntegralDirectImage_constructible`. The proved finite-level origin argument and
exact-functor cohomology comparison supply the remaining fields.

The proof privately imports all of `SfCompleteDirectImageReduction` and
`ProEtaleConstructibleOrigin` to reuse their proved helpers, and imports the upstream
exact right-derived comparison and Mathlib characteristic/cardinality lemma. All
existing public imports remain unchanged. The two interfering completed-coefficient
instances are disabled only within the private helper declaration. No source-library
file is changed, and no consumer adaptation or interface change record is needed.

Updated the item's node proof, dependencies and proof origin to describe this actual
construction. No new nodes or unproved statements were introduced. The unit's
`realized` lists are empty; its statement and route are unchanged.

Validation: the complete file compiled successfully through `lcompile.py`, first with
all proof imports and then with unused proof imports removed (29.6 seconds for the
cleaned file), without warnings. Import-direction and DAG reach checks found no cycle
from the added dependencies back to the item.

## Proved and sorry left

Closed 1 of 1 holes: `WeilConjectures.zlFiniteCompletedImageComparison`
(node `lem-zl-finite-completed-image-comparison`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
Both new private helpers, `finite_module_exact` and `finite_comparison`, are proved.
Existing dependencies are used as published, regardless of their own proof status.

## No longer needed

Removed direct proof imports:

- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.Paper.SfBcAdicRingDomain`
- `Sheaf.Paper.RoosIntrinsicCompletenessEquivalence`
- `Sheaf.CategoryTheory.StrictRoosComparison`
- `Sheaf.Paper.ExactProductFunctorStrictLimit`
- `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`

The first, third and seventh modules above are absent from this item's new import
closure. The others remain available transitively where the retained dependencies
need them; this delivery does not withdraw any module or claim global unreachability.

The node no longer directly needs these old planned proof dependencies, and removes
their old `tool_uses` approvals in the original order:

- `lem-sf-exact-functor-derived-triangulated`: use the existing right-derived
  triangulated structure and its invertible exact-functor unit.
- `lem-weil-pbc-exact-functor-derived-functor`: the existing specialized exact
  right-derived comparison already gives the required cochain unit.
- `lem-weil-pbc-ringed-topoi-module-adjunction`: use the already constructed canonical
  pro-etale ring-module adjunction for products.
- `lem-sf-bc-adic-ring-domain`
- `lem-pur-roos-intrinsic-completeness-equivalence`
- `lem-weil-strict-roos-comparison`
- `lem-cbc-exact-product-functor-strict-limit`
- `lem-weil-proetale-direct-image-restriction-of-scalars`

The last five are unnecessary as direct proof steps: input completeness already
provides the prescribed Roos triangle, and its image and transition transport are
proved in `SfCompleteDirectImageReduction`. The direct dependency on
`def-pur-integral-derived-operations` is also removed: no strict representative or
new completion construction is needed here. Existing statement dependencies remain.

New uses of existing nodes are `lem-pur-exact-derived-unit`,
`lem-sf-complete-direct-image-reduction`, `lem-weil-derived-limit-products-core`,
`def-weil-pbc-proetale-operations`, `def-weil-derived-complete` and
`lem-pe-constant-derived-encoding`. They provide existing canonical constructions and
proved tools; they do not replace a unit's statement or proof route. Maintainer
approval entries for these tools are not added by this delivery.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The old proof plan needlessly rebuilt the strict
completion model and its scalar-transition comparison. The existing `IsSfDerivedComplete`
predicate already includes the normalized Roos triangle, and the proved helpers in
`SfCompleteDirectImageReduction` transport it to the exact tower used here. The original
public docstring is retained, while the node now gives the proof actually written.

The constant-ring encoding must be respected when applying module exactness: the
forgetful sheaf-map and the explicitly whiskered map agree sectionwise. This equality
is proved in the private exactness helper, rather than assumed definitionally.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
