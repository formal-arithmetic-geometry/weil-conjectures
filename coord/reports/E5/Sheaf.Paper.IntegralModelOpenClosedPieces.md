## What changed

The original theorem `AlgebraicGeometry.ProEtale.integralModel_open_closed_pieces`
has a complete assembly proof with its original signature. It chooses the actual
coefficient pullback isomorphisms, obtains localization for the concrete continuous
module functors, constructs the open scalar-change comparison by adjoint uniqueness,
and transports the canonical sequence using an explicit isomorphism of three-term
sequences. The coefficient square for the closed comparison is proved by naturality
of inverse-image adjuncts. No Krull-dimension or invertibility hypothesis is added.

Four definitions move verbatim into `IntegralModelOpenClosedBasic`, publicly
reexported by the original module, to avoid proof-import cycles. Their bodies,
names, types, universes and visibility are preserved. The change record is
`coord/changes/E5-integral-model-open-closed-basic.md`. The existing consumer `Sheaf.Paper.RationalStratumIntegralModels` retains access
through its public import of the item; its explicit `piece`, `generator` and
`tensorSection` constructions do not need adaptation. New supporting modules contain the coefficient presentation bridge,
the continuous direct-image adjunction, concrete open restriction, categorical
localization transport, continuous localization and open scalar change.

Two genuinely separate results remain: finite-stratification constructibility of
supported modules, and the generic underived closed scalar-change comparison.
They apply beyond the original rationalization statement and have their own modules,
source citations, full proof plans and DAG nodes. Their statements include empty
complements and zero modules. The closed scalar-change lemma allows an arbitrary
coefficient map and arbitrary modules; no flatness is assumed or needed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.integralModel_open_closed_pieces` by a complete proof
from the new supporting results. Because two lower holes are added, this is a
decomposition, not a claim of one net proof.

Fully proved new public theorems:

- `AlgebraicGeometry.ProEtale.latticeCoefficientPullback_isIso`.
- `AlgebraicGeometry.ProEtale.continuousModule_adjunction`.
- `AlgebraicGeometry.ProEtale.continuousModule_open_restriction`.
- `AlgebraicGeometry.ProEtale.localization_equivalence_transport`.
- `AlgebraicGeometry.ProEtale.continuousModule_localization`.
- `AlgebraicGeometry.ProEtale.continuousExtension_scalar_change`.

Exactly two new holes remain:

- `AlgebraicGeometry.ProEtale.continuousConstructible_supported`, node
  `lem-weil-pbc-continuous-constructible-supported`.
- `AlgebraicGeometry.Scheme.closedImmersion_scalar_change`, node
  `lem-weil-pbc-closed-immersion-scalar-change`.

There is no hole in the item module, no hole in a definition, and no other hole
in the delivered Lean files. Syntactically: one original hole closed, two added.
The pinned sorry ledger determines the actual closure totals.

## No longer needed

Removed direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`.
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`.

The explicit ordinary open tensor lemma is unnecessary for the new open
scalar-change proof: both operations are left adjoints and their right adjoints
commute sectionwise. Thus `lem-weil-pbc-ringed-slice-extension-tensor` is not used
on this route. The concrete site equivalence remains necessary.

The Mathlib noetherian-source quasi-compactness instance supplies quasi-compactness
of the open immersion. Consequently the item no longer needs the planned
`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` or
`lem-sfb-noetherian-space-compact-subsets` proof steps.

The separate `FiniteLocallyClosedStratification` module is not used: continuous
constructibility already uses the adopted `Scheme.Stratification` definition.
That adopted definition node remains a dependency of the supported-constructibility
result. The inverse-image tensor/coefficient facts and closed underived projection
remain needed by the lower proof plans; no global pruning of those is claimed.
No module is withdrawn, and the parent's unfinished DAG dependency and the unit
route are preserved. Blueprint-wide searches for scalar change under closed
immersions, supported continuous constructibility, and localization across
equivalences found no exact blueprint node to reuse. New nodes retain
`thm-weil-pbc-finite-extension` as their imported blueprint ancestor.

## Where the brief, the DAG or earlier work was wrong

The statement is retained unchanged. The plan is mathematically sound. Its
geometric facts were stated for the raw inverse-image coefficient categories,
whereas the conclusion uses explicit continuous-function coefficients and actual
sheafified changes of rings. The delivery supplies the missing presentation,
adjunction and localization interfaces instead of identifying these categories
by definitional equality. In particular, the two open-site functors are related
by a natural isomorphism induced by the identity scheme morphism.

The open scalar-change step has the shorter adjunction proof described above.
The remaining closed step must preserve the B-action when passing from the
ordinary tensor projection to actual scalar extension; the generic remaining
lemma states that requirement explicitly. No derived tensor, completed scalar
model, weakened statement or arbitrary object witness is used.

## New nodes

`def-weil-pbc-integral-model-open-closed-basic` records the verbatim relocation of
the four explicit constructions. Change record:
`coord/changes/E5-integral-model-open-closed-basic.md`.

`lem-weil-pbc-lattice-coefficient-pullback-isIso` proves the lattice-presentation
coefficient bridge, using the canonical norm and homeomorphic ring presentations.

`lem-weil-pbc-continuous-module-adjunction` proves the adjunction with the actual
continuous direct image by comparing the sectionwise scalar actions.

`lem-weil-pbc-continuous-module-open-restriction` proves the explicit slice
equivalence and the comparison between pullback and restriction to the open site.

`lem-weil-pbc-localization-equivalence-transport` proves categorical localization
transport, including the exact unit and counit formulas.

`lem-weil-pbc-continuous-module-localization` applies that transport to the
continuous-coefficient functors.

`lem-weil-pbc-continuous-extension-scalar-change` proves ordinary open scalar
change by commuting the right adjoints and invoking left-adjoint uniqueness.

`lem-weil-pbc-continuous-constructible-supported` isolates the finite-stratification
support argument, with the coefficient-immersion hypothesis explicit; one hole.

`lem-weil-pbc-closed-immersion-scalar-change` isolates the generic conversion of the
B-linear ordinary closed projection to actual scalar extension, with the exact
coefficient square explicit; one hole.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
