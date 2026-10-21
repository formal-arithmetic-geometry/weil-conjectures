## What changed

Filled `AlgebraicGeometry.ProEtale.exists_lisse_lattice_reduced_open` with the
etale-cover, stratification, and finite-etale descent argument. Private proved
comparison helpers transport the arbitrary coefficient universe to a small
spectral-norm field and return the resulting lattice in the original `WithAbs`
coefficient presentation. The public statement is unchanged. The continuity helper is a private theorem
with a local instance attribute; all added reducibility attributes are local.
The conservative command-interface change is recorded in
`coord/changes/D5-lisse-lattice-reduced-open-proof-interface.md`.

## Proved and sorry left

The delivery closes the original hole in
`AlgebraicGeometry.ProEtale.exists_lisse_lattice_reduced_open`.
There are no `sorry` occurrences in the edited module and no added holes or split-off
statements. All auxiliary declarations are private and proved. The complete proof compiled with the project defaults. An initial clean compile
was 12.4 seconds; the local-instance revision compiled in 18.5 seconds and exposed
only the continuity helper's declaration-kind warnings, which are corrected by
stating that proposition as a theorem. The axiom
print includes `sorryAx` inherited through existing imported declarations; the
item has no local holes. The delivery probe checks the dependency provenance.

## No longer needed

The preliminary restriction to one affine member and its open image is absorbed
by the existing qcqs etale-cover lattice theorem. The open extraction uses the
existing dense-interiors theorem for finite locally closed stratifications.
Removed original proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`: its module
  comparison is for constant coefficients; the continuous comparison is proved here.
- `Sheaf.CategoryTheory.SiteInverseImageTensor` and
  `Sheaf.CategoryTheory.ModulePullbackTensorIso`: replaced by the existing internal
  coefficient pullback/scalar comparisons and explicit continuous ringed adjunction.
- `Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal`: replaced by the existing
  `ContinuousEtaleLocalLattices` interface, whose coefficient conventions match descent.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: replaced by
  the direct Mathlib closed-immersion isomorphism API.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`: continuous restriction
  is compared explicitly using the composition/base-change adjunction.

Additional draft imports pruned during proof development:

- `Sheaf.Paper.LatticePullback`: only the coefficient inverse-image isomorphism
  was needed, now imported from `ContinuousCoefficientPullbackIso` directly.
- `Sheaf.Paper.ContinuousAffineEtaleLattice`: subsumed by
  `ContinuousEtaleLocalLattices`.
- The old private `ContinuousLissePullbackSystem` API is replaced by the public
  `ContinuousLocallyFreePullback` API.

Removed direct DAG dependencies, grouped by replacement:

- `def-weil-etale-morphism`, `def-weil-pbc-finite-etale-category`,
  `lem-weil-pbc-etale-covering-base-change`: finite/etale/surjective base change
  is discharged by the Mathlib morphism-property instances already in scope.
- `lem-weil-pbc-affine-scheme-qcqs`, `lem-weil-pbc-etale-morphism-open-map`,
  `lem-weil-pbc-locally-noetherian-quasi-separated`,
  `lem-weil-pbc-lisse-lattice-etale-local`: the existing continuous qcqs
  etale-cover lattice theorem packages these preliminary steps.
- `lem-kun-finite-union-noetherian`,
  `lem-sc-affine-noetherian-underlying-space`,
  `lem-weil-pbc-noetherian-open-subscheme-noetherian`: Mathlib's Noetherian-space
  instance and its inducing-map theorem supply the required topology directly.
- `lem-weil-pbc-reduced-source-factors-through-closed-subscheme`: Mathlib's
  surjective closed immersion into a reduced target isomorphism theorem supplies
  the actual scheme factorization.
- `lem-sfb-proetale-object-inverse-image-restriction`,
  `lem-weil-pbc-left-exact-site-inverse-image-tensor`,
  `lem-weil-pbc-ringed-topoi-module-pullback-tensor`,
  `lem-weil-proetale-weakly-etale-localization`: the existing internal scalar
  pullback/composition API and the explicit continuous module adjunction replace
  these direct uses.

The object restriction and weakly etale localization tool-use entries are
removed from this node: the explicit continuous ringed adjunction supplies the
required comparison. The implementation additionally uses the already proved generic tools
`Topology.Stratification.dense_iUnion_interior_stratum` (attached to
`prop-constructible-generic-constancy`) and
`lem-sfb-continuous-coefficient-inverse-image-iso`. The former is the finite
locally closed partition argument; the latter identifies the canonical
continuous coefficient pullback map. These are existing declarations, not new
mathematical assumptions. No adopted source declaration is removed or changed.
These are direct proof dependency removals, not claims that their other consumers
or the source declarations can be deleted.

## Where the brief, the DAG or earlier work was wrong

The etale-local and finite-etale descent interfaces use a small coefficient type,
whereas this theorem permits `E : Type u`; this requires an explicit algebra
isomorphism to a small model. The existing object module-restriction result is
stated for constant coefficients, so continuous coefficients require their own
ringed restriction comparison. Neither issue changes the mathematical statement. The first delivery preflight
required a change record for the new elaboration commands and identified a private
instance registered globally. The helper now has only a local instance attribute,
and the command changes have the required record.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
