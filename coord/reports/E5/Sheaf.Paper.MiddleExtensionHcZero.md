## What changed

Replaced the sole `sorry` in `Sheaf.Paper.MiddleExtensionHcZero` with a complete
Lean proof from the existing constructible degree-zero proper-support comparison
and the separate unique-continuation statement described below. The existing
public signatures, definitions and public imports are unchanged.

The proved private lemma `middleExtensionCurve_closedSubset_ne_top` base-changes
affineness, smooth relative dimension and connectedness, proves the geometric
curve has dimension one, and excludes properness using proper-affine finiteness.
The universal closed-subscheme characterization then excludes a proper-support
closed subset equal to the whole curve. In particular it avoids constructing the
reduced induced closed subscheme of the whole curve.

The main proof constructs the common-stage heart object, obtains the injective
comparison and support, proves the complementary open is nonempty, applies unique
continuation, and transports equality back through the actual compact-value
isomorphism and universe lifts. It works for the unchanged arbitrary Frobenius
isomorphism and arbitrary compactification.

`Sheaf.Paper.MiddleExtensionSectionRestriction` isolates the genuine
unique-continuation result: sections of an ordinary middle extension are determined
on any nonempty open of a smooth geometrically connected curve. This statement has
no affineness, compactification, compact-support class, or Frobenius isomorphism.
Its source is the lissity argument in the blueprint, separately from the support
argument. Both DAG records follow this decomposition. No definition repair or
consumer adaptation is made.

Validation: `lcompile.py --all` compiled both delivery modules in import order
(9.0 s and 13.5 s in the completed current-source run), with no compiler errors or
warnings. Earlier server no-response failures were transport failures, not Lean
timeouts. The delivery checks are run separately.

## Proved and sorry left

Original holes: 1. Closed original hole:
`WeilConjectures.subsingleton_adicMiddleExtension_hcZero`
(node `lem-a1-middle-extension-hc0`). Its proof body contains no `sorry`.
The private geometric lemma `middleExtensionCurve_closedSubset_ne_top` is also
proved with no holes.

Added holes: 1. The only delivered `sorry` is
`WeilConjectures.adicMiddleExtension_section_eq_zero_of_restriction`
in `Sheaf.Paper.MiddleExtensionSectionRestriction`
(node `lem-a1-middle-extension-section-restriction`). Its entire proof is `by sorry`;
its docstring and node give the source and the full mathematical argument.

This is a decomposition: one original hole is replaced by one strictly separate
unique-continuation hole, for a net hole change of zero in these delivered files.
It is not an unconditional proof of the vanishing theorem. Existing imported
statement holes, notably `a1ConstructibleDegreeZeroProperSupport` and
`adicMiddleExtension_heart`, are used as the stage-3 brief directs and are unchanged.
No hole is introduced in a definition, and no target statement is changed.

## No longer needed

Removed proof-only imports from the item module:

- `Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings`
- `Sheaf.Paper.GaloisLisseRepresentations`
- `Mathlib.CategoryTheory.Abelian.Basic`
- `Mathlib.CategoryTheory.ObjectProperty.Kernels`
- `Mathlib.RepresentationTheory.Rep.Basic`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`
- `Sheaf.Paper.LisseAdicFiberFunctors`
- `Sheaf.Paper.LisseModuleSheaves`
- `Sheaf.Paper.LisseTensorScalarExtension`
- `Sheaf.RepresentationTheory.LAdic`
- `WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Properties`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.Topology.NoetherianSpace`
- `Mathlib.Topology.Irreducible`
- `Sheaf.Paper.CommonStageCurveWeilMiddleExtension`

These imports are absent from the compiling main proof. This does not assert that
their modules disappear from the targets' whole transitive import closure; several
remain accessible through the public interfaces or are needed by the separate
unique-continuation argument.

Former direct proof dependencies now delegated to unique continuation:

- `lem-sc-smooth-connected-curve-local-rings`
- `def-pc-integral-scheme`
- `lem-sc-scheme-over-field-universally-open`
- `def-weil-irreducible-components`
- `lem-sfb-noetherian-space-compact-subsets`
- `pqf-def-locnoeth`
- `def-wf-middle-extension`
- `cor-galois-lisse-representations`

Former direct dependencies not required as separate nodes in either new proof:

- `pqf-lem-affine-open-locnoeth`
- `lem-sc-affine-noetherian-underlying-space`
- `def-weil-pbc-closed-subset-proper-over-base`

The affine-Noetherian-coordinate detour is unnecessary: the geometric curve is
already Noetherian in the smooth connected curve interface and its open inherits
this property. The proper closed-subset *definition* remains a statement notion;
the main proof uses the stronger already-proved universal characterization in
`lem-weil-pbc-closed-subset-proper-over-base-properties` instead of unfolding the
definition. The ordinary-image definition remains a statement dependency and is
used in the separate unique-continuation argument.

Removed obsolete entries of the item's top-level `tool_uses` (remaining entries
retain their original order):

- `lem-sc-smooth-connected-curve-local-rings`
- `lem-sc-scheme-over-field-universally-open`
- `pqf-lem-affine-open-locnoeth`
- `lem-sc-affine-noetherian-underlying-space`
- `lem-sfb-noetherian-space-compact-subsets`
- `cor-galois-lisse-representations`

No unit realization or unit route is removed or bypassed. No existing Lean module
is withdrawn, and no whole-library pruning count is claimed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan's step 5 treated the proper-support comparison's lisse
compatibility as if it directly normalized restriction for the ordinary image
`j_*F`. The declared lisse compatibility instead requires a globally lisse lattice
on its object; the ordinary image need only be constructible on the whole curve.
Also, the finite-level faithful lisse fibre functor does not by itself identify
arrows in the intrinsic common-stage derived category with ordinary sheaf sections.
The remaining theorem explicitly includes that coefficient-stage and normalized
restriction argument. No false statement or mathematical counterexample was found.

Short-route searches found a proved dense-open restriction-injectivity theorem
for locally constant etale sheaves
(`AlgebraicGeometry.Etale.upperStar_map_injective_of_isLocallyConstantSheaf`), and
proved dense-open unit results for the source library's `AdicSheaf` category.
Neither directly handles the intrinsic ordinary-image common-stage arrow in this
item. LeanFinder, LeanSearch, Loogle and source grep results are recorded in the
new node; blueprint duplicate searches found no existing statement of this exact
unique-continuation interface. A scratch proof also establishes finite-level
restriction injectivity into ordinary etale direct images: use the ordinary
adjunction, pullback composition, and dense-open restriction injectivity for the
lisse target. That scratch file compiled in 14.4 s. It does not identify the
common-stage completed-module realization or its normalized restriction, so it is
not claimed as a proof of the remaining theorem and is not an unused library import.

The earlier interrupted attempt had retained compilable Lean but no report or
new-node record. This delivery supplies those records and validates the reduction.
Across provider-error resumptions, the launcher reference start changed from
1792428211.631951 to 1792439343.8532367. The worker did not edit the budget metadata;
this reset is reported for launcher-owner review. The last completed restoration
compile checked both delivery modules again (6.4 s and 6.8 s).

## New nodes

`lem-a1-middle-extension-section-restriction`, in
`dag/nodes/sec-deligne-laumon-a1/lem-a1-middle-extension-section-restriction.json`,
states unique continuation independently of compact support and affineness.
The new module is `lean/Sheaf/Paper/MiddleExtensionSectionRestriction.lean`.
It realizes the lissity portion of `lem-fd-stalk-at-origin`'s second paragraph,
via `lem-a1-middle-extension-hc0`, with full finite-stage transport included.
Edge cases: the zero input and rank zero are immediate; the identity open gives
usual lisse unique continuation; a proper smooth curve is allowed; the nonempty
open excludes the vacuous empty-curve case. The lemma gives no compact-support
vanishing on a proper curve. No change records are required: no existing
statement or definition is changed.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
