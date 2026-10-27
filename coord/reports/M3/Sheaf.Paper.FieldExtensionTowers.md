## What changed

Replaced the sole `sorry` in `Sheaf.Paper.FieldExtensionTowers` by a complete assembly
of the existing exceptional-system comparison and four strictly smaller descent
obligations, each in its own new module. All existing public declarations, definitions,
signatures, and public imports are unchanged.

The private proved helper `ordinary_scalar_properties` transfers intrinsic completeness
to the legacy augmented K-flat tower definition, applies `finiteFreeCompletedScalarComparison`,
and transports `sfIntegralScalarExtension_constructible` along the resulting isomorphism.
It supplies both ordinary scalar-extension fields of `Result` without adding a hole.

The assembly privately imports Nagata compactification and Euclid's prime-existence theorem.
It first proves compactifiability, then uses the existing exceptional-system
theorem to obtain the same simultaneous coefficient models and finite laws used by the
integral descent. It feeds the resulting integral coefficient cocycle into rational descent
and supplies every dependent field of `Result` from those shared choices.

The parent DAG proof now describes this assembly. The source unit's integral-tower,
finite-comparison, inverse-limit and rational-localization route is preserved.

Validation: the first all-file compile stopped before checking a delivered file.
The private overlay failed compiling existing `FieldExtensionSourceNormalization`
because the built object for the existing source module
`WeilConjectures.CategoryTheory.Sites.SheafCohomologyTorsion` is absent.
That attempt did not validate the delivered Lean files. A subsequent delivery run
against the newer private overlay compiled all five delivered modules. It stopped
on four haveILetI style warnings in the item proof; those local proof bindings have
been changed to let bindings. The public theorem signature remains unchanged.

## Proved and sorry left

One original hole closed: `AlgebraicGeometry.ProEtale.FieldExtensionTowers.field_extension_towers`
(node `det-sp-field-extension-towers`). The item module has zero remaining sorries.
Its proof still depends on existing open declarations and the following four newly named
obligations; this is a decomposition, not a net proof or a sorry-free target.

Four holes added, each the entire proof of a public theorem in its own module:

- `AlgebraicGeometry.ProEtale.FieldExtensionTowers.field_extension_completed_strict_limit`
  (`lem-sp-field-extension-completed-strict-limit`): unbounded strict-limit transport,
  including K-injectives and representative normalization.
- `AlgebraicGeometry.ProEtale.FieldExtensionTowers.field_extension_reduction_descent`
  (`lem-sp-field-extension-reduction-descent`): ordinary/derived completed and system
  scalar coordinate identifications and the canonical reduction word.
- `AlgebraicGeometry.ProEtale.FieldExtensionTowers.field_extension_integral_descent`
  (`lem-sp-field-extension-integral-descent`): reconstruct supplied whole-system laws
  as coherent integral comparisons and their limit equations.
- `AlgebraicGeometry.ProEtale.FieldExtensionTowers.field_extension_rational_descent`
  (`lem-sp-field-extension-rational-descent`): localize a supplied coherent integral
  family on raw rational Hom tensors, with the source-completion normalization.

Each conclusion omits substantial parts of the original theorem. The strict-limit and
reduction lemmas have no geometric compactification; integral descent assumes the actual
whole-system comparisons and reduction family and asserts no rationalization; rational
descent assumes integral models, comparisons and their cocycle and asserts none of their
existence. The root combines these independent obligations in real Lean code.

## No longer needed

Removed these direct private imports from the item module:
`Sheaf.Paper.FiniteFreeCompletedScalarComparison`,
`Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`,
`Sheaf.Paper.FieldScalarStrictLimit`,
`Sheaf.Paper.FieldScalarNormalizedSystems`,
`Sheaf.Paper.SmoothPurityReductionTowerNormalized`,
`Sheaf.Paper.FieldShriekSystemComparison`,
`Sheaf.Paper.FieldProjectionSystemSquare`,
`Sheaf.CategoryTheory.SemilinearScalarLocalization`,
`Sheaf.Paper.QcqsCompactSupportRealization`, and
`Sheaf.Paper.DerivedPullbackTensorHom`.

The parent also drops these direct proof-dependency edges, with their obligations
retained in the new descent nodes or in the exceptional-system theorem:
`lem-sp-field-scalar-strict-limit`, `lem-sp-field-scalar-normalized-systems`,
`det-sp-reduction-tower-normalized`, `lem-sp-field-shriek-system-comparison`,
`lem-sp-field-orientation-system-comparison`, `lem-sp-field-projection-origin-witnesses`,
`lem-sp-field-projection-system-square`, `lem-sp-field-purity-system-transpose`,
`det-sp-integral-direct-image-tower`, `det-sp-integral-adjunction-bijection`,
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`, `lem-pur-semilinear-scalar-localization`,
`def-weil-rationalization-karoubi`, `def-weil-integral-rational-qbar-compact-support`,
`def-weil-derived-pullback-tensor-hom`, and `def-coefficient-twists-detailed`.

Their declarations remain available through public statement imports where needed;
their mathematical obligations are retained in the descent nodes. No existing module or
node is withdrawn, and none is claimed to be globally pruned. The parent no longer
cites the previous unimplemented transport steps as if they already assembled the
record: their dependencies are assigned explicitly to the smaller descent nodes.

## Where the brief, the DAG or earlier work was wrong

There was no direct complete assembler in the stated dependencies. In particular:

1. `fieldScalarStrictLimit` supplies Roos-normalized comparisons on a small site;
   `StrictLimitComparison` also asks for preservation of K-injectives and an equation
   for the published `coefficientConstantTowerLimit`. Finite freeness alone does not
   make scalar extension preserve K-injectives for a general algebra. For these DVR
   coefficient extensions the dual integral lattice is free of rank one, identifying
   extension with coinduction; the strict-limit proof obligation records this argument.
2. `field_scalar_normalized_systems` supplies its family only on the source and target
   in the geometric finite-type setting. `Result.reduction` quantifies over arbitrary
   schemes and arbitrary reduction presentations. The new reduction lemma retains
   that actual scope and requires the tensor-coordinate construction itself, rather
   than applying the narrower theorem with missing hypotheses.
3. The existing rationalized-adjunction diagrams use a separate integral presentation.
   They do not supply the exact `RationalModel` source-identification normalization
   of these models. Rational descent explicitly retains the tensor completion unit.

Edge cases checked from the statements and constructions: equal coefficient fields
use tensor multiplication and unitors; ramified extensions use one finite integral
basis and cofinal ell powers, not etaleness; empty schemes and relative dimension zero
are not excluded; strict limits remain unbounded; rationalization changes no objects.
The coordinate lemmas assert no faithfulness of finite derived evaluation.
The arbitrary-scheme reduction node cites the generic cochain change-of-rings and
semilinear system calculus as tools for constructing its coordinate maps. It does
not apply the narrower geometric normalized-system theorem to an arbitrary scheme;
the latter is retained only where the geometric hypotheses are present.

Mathlib and source-library searches found the generic projection-normalized limit
isomorphism, fully faithful adjunction restriction and adjunction localization, but
no theorem supplying these coefficient-model normalization records. Search queries
and results are recorded in the four new nodes and the launcher's real search log.

## New nodes

`lem-sp-field-extension-completed-strict-limit`, module
`Sheaf.Paper.FieldExtensionCompletedStrictLimit`, isolates source proof (1)'s unbounded
strict-limit comparison with its K-injective representative normalization.

`lem-sp-field-extension-reduction-descent`, module
`Sheaf.Paper.FieldExtensionReductionDescent`, isolates source proof (1)'s multiplication
and insertion-of-one maps after transport through the published coefficient models.

`lem-sp-field-extension-integral-descent`, module
`Sheaf.Paper.FieldExtensionIntegralDescent`, isolates source proof (2)'s passage from
supplied system arrows and equations to normalized integral reconstruction.

`lem-sp-field-extension-rational-descent`, module
`Sheaf.Paper.FieldExtensionRationalDescent`, isolates source proof (3)'s raw localization
of supplied coherent integral adjunctions and scalar comparisons.

No statement, definition, consumer interface, or source-library body was changed;
there is no change record or forced consumer adaptation.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
