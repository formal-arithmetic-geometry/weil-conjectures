## What changed

Filled all three original theorem holes in the assigned ordinary-etale module.
Two are proved from existing library declarations; the compact-support isomorphism
is proved through a proper-factor lemma and an open-factor/universal-arrow
argument, with one independent scalar-unit normalization left below it. Existing public signatures, definitions and public imports are unchanged.

The private `universal_left_adjoint` transports universal arrows through a pair of
adjunctions using the mate unit equation. Its derived open specialization proves
`coefficientRestrictionOpen_universal`. Applying that result and the proper-factor
lemma makes the compact-support image of the tensor unit universal. The defining
inverse Hom bijection then gives invertibility of the specified B-linear comparison;
the full inclusion of D+ reflects the ambient isomorphism.

The finite-Tor existence proof uses the source bounded flat representative,
the principal kernel of the actual coefficient quotient, and `Sheaf.reductionDatum`.
Reduction inherits the lower degree bound, and the K-flat reduction theorem proves
universality against arbitrary ambient B-complexes. The origin proof identifies the
two universal presentations with scalar extension and uses `pbcComparisonReduction`.
It does not require flatness of the reduced complex or an arbitrary choice of tensor data.

Added the proved proper-factor module `Sheaf.Paper.ProperCoefficientUniversal`,
the derived comparison calculation `Sheaf.Paper.EtaleScalarMateNormalization`,
and the scalar-unit lemma `Sheaf.Paper.EtaleScalarPullbackUnit`, with matching nodes,
and proof-only imports of the derived mate, quotient reduction, flat model and
witness-compatibility interfaces. Updated the item node's proof to record these
ordinary-etale arguments while retaining its separate pro-etale obligations.

All four delivered modules compiled together through `lcompile.py --all`, with no
warnings or errors. The main module's five public imports are identical to the
shared source; 26 proof imports were removed and five added. The four node files'
proof dependencies equal the unions of the uses in their recorded proof steps.

## Proved and sorry left

Closed the original holes in:

- `AlgebraicGeometry.Etale.nonempty_coefficientTensorModel_of_finiteTor` (proved).
- `AlgebraicGeometry.ProEtale.CoefficientTensorModel.origin_of_etale_finiteTor` (proved).
- `AlgebraicGeometry.Etale.compactSupportCoefficientComparisonPlus_isIso`
  (decomposed; the open-factor and universal-arrow combination are proved).

The assigned module has zero textual `sorry` occurrences. The delivery adds one:

- `AlgebraicGeometry.Etale.scalarPullbackUnit`, node
  `lem-r2-etale-scalar-pullback-unit`, in
  `lean/Sheaf/Paper/EtaleScalarPullbackUnit.lean`.

Thus there are three holes closed and one added: two direct proofs and one
normalization decomposition, not three independent proofs. The previously proved
`coefficientRestrictionOpenMap_isIso` is retained and is not counted as newly closed.
No hole is inside a definition or a private declaration.

The proper-factor lemma is proved from the finite-ring proper projection formula.
It first proves that scalar extension of the direct image is bounded below, using
the projection formula and exact faithful restriction, and then proves invertibility
of the B-linear scalar mate using the restricted-mate projection identity. The
normalization module proves the equality between the ambient restriction mate and
the bounded comparison by adjunction counits and full-subcategory restriction. It
also proves the abstract scalar-unit/mate identity and transports arbitrary scalar
transposes through this equality. The only retained obligation is the scalar-unit
identity for the specified K-flat-normalized pullback comparison; it contains no
properness, direct-image isomorphism, compactification or universal-arrow assertion.
It is therefore a separate canonical-map calculation, not the assigned statement
under a new name. No scalar extension of an arbitrary object is asserted to be D+.

## No longer needed

The following former proof-only imports are removed from the assigned module.
Their generic results are not used by these ordinary-etale proofs; the companion
pro-etale module retains its own imports and obligations. This is local pruning,
not a claim that all these modules leave the targets' global import closure.

- `Sheaf.Algebra.Homology.ChangeOfRingsTensorComparison`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.FixSiteOpenExchange`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`.
- `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`.
- `Sheaf.Paper.CondensedAmbientExchange`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`.
- `Sheaf.Paper.ProjectionMateExact`.
- `Sheaf.Paper.RingedExchangeTensorCoherence`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.SecSmoothPurity.DirectImageScalarExchange`.
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`.
- `Sheaf.SecSmoothPurity.OpenScalarExchange`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`.
- `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`.

The corresponding old pro-etale proof steps and dependencies remain in the shared
item node because it also describes the companion pro-etale theorem and its
compatibilities. No unit statement or unit proof step is bypassed, and no new
maintainer `tool_uses` approval is added or reordered.

`lem-sf-flat-model` is not used through its constructible refinement: the source
`DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn`, recorded by
`lem-sc-source-tor-amplitude-flat-model`, suffices. The reduced-flatness result
`lem-sf-reduction-flat-model` (`Sheaf.Paper.FiniteCoefficientReductionFlatModel`)
is unnecessary for these two domain proofs. The reduction datum supplies the
universal property and the lower degree bound directly.

## Where the brief, the DAG or earlier work was wrong

No existing statement is changed or disputed. The compact scalar-coherence and
proper finite coefficient-extension interfaces assume noetherian schemes, which
are not hypotheses of the assigned ordinary-etale comparison theorem. Adding
those hypotheses would change the assigned statement. The separate proper-factor
lemma instead uses the existing finite-ring proper projection formula, whose
source theorem has no such assumption. The restriction/direct-image normalization
is proved, and the remaining obligation is solely the scalar/pullback comparison's scalar-unit identity.

The previous report described an obsolete direct Tor-bound construction and one
untouched original hole. This report replaces it with the actual bounded-flat
quotient proof and explicit proper-factor decomposition.

Provider interruptions repeatedly resumed this same sandbox. The launcher changed
`.budget.start` from 1792424347.5179965 (seen in the earlier continuation) to
1792432757.3071096 (2026-10-19 17:59:17 UTC). R2 did not edit `.budget` or any
launcher file. The preceding dry run of the added-lemma packet reported zero of
120 minutes despite the retained earlier proof work; this is the metadata lifecycle
reset mentioned by the standing brief. Work and the original session deadline
were retained; no sleep or repeated unchanged retry was used to pass its clock gate.

The resumed server preflight required LeanSearch separately from LeanFinder/Loogle.
Ran three additional LeanSearch queries, checked their results, and added the actual
query/result records to the new nodes. No matching derived comparison was found.

## New nodes

`lem-r2-proper-coefficient-universal` records the proper case of Stacks 0GL6,
with the precise canonical bounded-below restriction comparison and universality
against all ambient coefficient complexes. Its completed Lean proof first identifies the
supplied tensor presentation by the scalar adjunction, then checks the projection
formula's bounds, uses its canonical restricted-mate equality, and identifies the
resulting unit through the derived adjunction normalization. Edge cases checked:
identity f or identity coefficient map gives the original universal arrow; zero
objects or the zero coefficient ring give the unique universal zero arrow; empty
source gives zero direct image. Nonflat quotients are explicitly allowed; there
is no assertion that arbitrary scalar extension preserves D+. Its boundedness is
part of the supplied presentation, and properness plus the projection formula
supplies boundedness on the image when needed. No change record is required,
since no existing statement or definition is modified.

`lem-r2-etale-scalar-mate-normalization` records the proved ambient-to-D+ mate
comparison and its consequence for an arbitrary scalar-adjoint transpose. The proof
uses the existing bounded restriction-adjunction identities. It checks all inclusion
isomorphisms and proves the generic mate calculation explicitly.

`lem-r2-etale-scalar-pullback-unit` records the remaining scalar-adjunction unit
identity for the K-flat-normalized scalar/pullback comparison of Tags 07A4 and 07A7.
Its proof is the ordinary conjugate unit equation transported along K-flat resolving
counits. Edge cases: identity coefficient map or identity f gives the scalar unit's
naturality equation; zero ring, zero complex and empty scheme give equal unique
zero arrows. Arbitrary nonflat coefficient maps are allowed because the comparison
is derived, and no lower bound is claimed. No existing declaration or definition is
changed by either node, and no change record is needed.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
