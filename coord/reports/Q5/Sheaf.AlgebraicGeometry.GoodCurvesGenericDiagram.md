## What changed

Proved `AlgebraicGeometry.exists_good_curves_generic_diagram` with its signature and
public imports unchanged. The proof derives both density clauses from a curve presentation
whose thickening open meets each smooth curve fibre. A proved private helper transfers
componentwise density to density on the target fibres through the surjective coproduct map.
Smooth geometrically connected completions are geometrically irreducible by the existing
`WeilConjectures.AlgebraicGeometry.Regular` API.

Added three proved intermediate modules: `GoodCurvesNonemptyThickening` restricts to an
affine neighbourhood and transports the result back; `GoodCurvesAffineNonemptyThickening`
passes to the reduction and transports the result back; and
`GoodCurvesReducedAffineNonemptyThickening` combines the existing field-completion theorem
with a finite radicial residue-field model and spreading of that prescribed generic diagram.
The transports explicitly preserve the pullback target, thickening projection, commuting
triangles, generic-component hypothesis and fibre-dimension bound.

Also proved `AlgebraicGeometry.finite_radicial_root_cover`: adjoining a p-th root over
any ring of characteristic p yields a finite surjective universally injective spectrum map.
It uses the monic quotient's faithful flatness and the field-point criterion with injectivity
of Frobenius. Proved `AlgebraicGeometry.exists_affine_shrinking_under_finite_radicial`:
a neighbourhood on a finite radicial cover contains the inverse image of an affine open
neighbourhood downstairs, by removing the closed image of its complement.

Proved `AlgebraicGeometry.generic_residue_field_affine_limit`: at a generic point of a
component of a reduced scheme, the spectrum of its residue field is the limit of its
affine neighbourhoods. The proof constructs the cone explicitly, identifies the reduced
generic stalk with its residue field, and transports the existing stalk-spectrum limit.
No integral or Noetherian hypothesis on the whole base is needed. The spreading construction
now uses this result instead of rebuilding the principal-localization limit.

Added two unfinished construction modules, with complete source proofs in their docstrings:
`FiniteRadicialGenericResidueExtension` and `GoodCurvesSpreadGenericCompletion`.
No existing definition or statement changed; no consumer adaptation or change record is needed.
Validation: all nine delivered modules compile together through `lcompile.py --all`,
without warnings and with every individual file below the 60-second limit.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.exists_good_curves_generic_diagram`,
by decomposition. The delivered module has zero `sorry`. The new combining, transport and construction
lemmas are also fully proved:

- `AlgebraicGeometry.exists_good_curves_nonempty_thickening`.
- `AlgebraicGeometry.exists_good_curves_affine_nonempty_thickening`.
- `AlgebraicGeometry.exists_good_curves_reduced_affine_nonempty_thickening`.
- `AlgebraicGeometry.finite_radicial_root_cover`.
- `AlgebraicGeometry.exists_affine_shrinking_under_finite_radicial`.
- `AlgebraicGeometry.generic_residue_field_affine_limit`.

Added exactly two holes, each a public theorem whose entire proof is `by sorry`:

- `AlgebraicGeometry.exists_finite_radicial_generic_residue_extension`
  (`lem-weil-pbc-finite-radicial-generic-residue-extension`): still needs the finite
  degree-p root-adjunction tower over a reduced affine ring, characteristic and denominator
  shrinking, reduction at each step, and the compatible generic residue-field calculation.
  The finite/radicial/surjective property of each root adjunction and affine shrinking
  downstairs are already proved in this delivery.
  The existing generic spread theorem only asserts an integral universal homeomorphism;
  it does not give the finiteness required here. The nonintegral reduced base is also essential.
- `AlgebraicGeometry.exists_good_curves_spread_generic_completion`
  (`lem-weil-pbc-good-curves-spread-generic-completion`): still needs simultaneous
  affine-neighbourhood descent of the supplied generic diagram, its morphism properties,
  proper smooth good-fibre shrinking, descent of a normal-locus thickening open, and shrinking
  to make its preimages meet every curve fibre. Its input is the explicit generic
  normalization/completion diagram, including finite presentation and qcqs data; it has no
  dimension hypothesis and does not invoke generic completion existence itself.
  The affine-neighbourhood limit of its generic residue field is already proved here.

Thus this is a decomposition, not a net hole reduction: one original hole closed and two
new holes added. No data definition chooses a witness from either unfinished theorem.
The empty index family is covered by the source proofs; the proved density helper needs
only surjectivity and therefore also handles that case.

## No longer needed

The following proof-only imports were removed from the item module:

- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`.
- `WeilConjectures.FieldTheory.PurelyInseparableDegreePIntermediate`.
- `Mathlib.FieldTheory.PurelyInseparable.Basic`.
- `Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations`.
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`.
- `Sheaf.AlgebraicGeometry.DescendFinite`.
- `WeilConjectures.AlgebraicGeometry.DescendSurjective`.
- `Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`.
- `Sheaf.AlgebraicGeometry.EventuallyProper`.
- `Sheaf.AlgebraicGeometry.DescendClosedImmersion`.
- `Sheaf.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore`.
- `Mathlib.AlgebraicGeometry.Properties`.
- `Sheaf.AlgebraicGeometry.DescendSmoothQcqs`.
- `Sheaf.AlgebraicGeometry.FieldCurveCompletionInsep`.
- `Sheaf.AlgebraicGeometry.OpenImmersionInverseLimitDescent`.
- `Sheaf.AlgebraicGeometry.ProperFibreDimensionUpperSemicontinuous`.
- `Sheaf.AlgebraicGeometry.ProperSmoothGeometricComponentsLocallyConstant`.
- `Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent`.
- `WeilConjectures.AlgebraicGeometry.Thickening`.

The main proof now imports only `GoodCurvesNonemptyThickening` and the existing
`WeilConjectures.AlgebraicGeometry.Regular` geometry API. Most former construction dependencies
remain needed by the new construction statements and are recorded there, rather than being
claimed as globally pruned. The three proved reductions have only their actual proof imports.
The duplicate source-library étale-descent and thickening imports were removed from the
spreading module, which already sees those interfaces through its retained imports.
Its unused public `Mathlib.FieldTheory.PurelyInseparable.Basic` import was also removed:
the spreading statement needs the supplied residue-field model and generic diagram,
and does not itself assume a purely inseparable field extension.
The spreading module also drops `LocalizationColimitPrincipalLocalizations` and its direct
`LimitAffineTransition` import: `GenericResidueFieldAffineLimit` constructs the needed cone
using the existing stalk-spectrum limit. The descent interfaces retain their own limit
imports as needed. This replaces the original node's principal-localization setup, while
preserving the spreading step of its blueprint unit.
The new limit module also omits a redundant direct `Mathlib.AlgebraicGeometry.Stalk` import;
its residue-field interface already imports that module publicly.
The original nodes `lem-weil-pbc-localization-colimit-principal-localizations` and
`lem-weil-pbc-limit-affine-transition` are no longer direct dependencies of this construction:
the explicit affine-neighbourhood cone replaces their limit-construction role. Other users
of those modules, including descent interfaces, are unaffected. The separate
`lem-weil-pbc-finite-presentation-base-change-composition` step is also unnecessary here:
the prescribed generic diagram includes its structural finite-presentation data, and
base-change preservation in the proved reductions is provided by Mathlib instances.
`def-pc-integral-scheme` remains a statement dependency of the generic diagram, rather
than a density-proof dependency: density uses geometric irreducibility of the fibres.
`lem-pc-projective-proper` remains needed in the spreading node, through the general
projective-morphism interface rather than a direct `ProjectiveSpace` import.
No blueprint unit or its realized step is bypassed. No global module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

No false assigned statement or source proof was found. The plan's affine-neighbourhood and
reduction steps require explicit transport of generic components, scheme fibres and the
thickening projection; these are now proved. The existing inseparable generic-spread theorem
is not a finite-cover theorem and cannot replace the degree-p construction unchanged.

## New nodes

`lem-weil-pbc-good-curves-nonempty-thickening`: complete nonempty-thickening presentation;
proved by affine restriction and cartesian transport.

`lem-weil-pbc-good-curves-affine-nonempty-thickening`: presentation over an affine base;
proved by reduction, its topological fibre comparison and cartesian transport.

`lem-weil-pbc-good-curves-reduced-affine-nonempty-thickening`: presentation over a reduced
affine base; proved by combining field completion, finite radicial realization and spreading.

`lem-weil-pbc-finite-radicial-generic-residue-extension`: the finite radicial generic
residue-field construction, independent of curves; unfinished as specified above.

`lem-weil-pbc-good-curves-spread-generic-completion`: spreading of a supplied generic
normalization/completion diagram over its supplied finite radicial model; unfinished as
specified above. The final geometric-irreducibility and density argument is outside it and
has been proved in the assigned module.

`lem-weil-pbc-purely-inseparable-root-cover`: the finite radicial p-th-root spectrum cover,
proved from the monic quotient and field-point criteria without domain assumptions.

`lem-weil-pbc-finite-radicial-affine-shrinking`: affine shrinking downstairs,
proved by removing the finite image of a closed complement and choosing an affine open.

`lem-weil-pbc-generic-residue-field-affine-limit`: an explicit limiting affine-neighbourhood
cone with vertex the generic residue-field spectrum, proved from the stalk-spectrum limit
and the reduced minimal-prime stalk field theorem.

All eight nodes inherit the original chapter, unit and blueprint ancestor. The original node's
proof dependencies now describe the presentation plus density argument. The construction
steps and their dependencies are retained in the new nodes that state them. No change records.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
