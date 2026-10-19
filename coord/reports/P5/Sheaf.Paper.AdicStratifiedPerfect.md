## What changed

Reduced `AlgebraicGeometry.Scheme.adic_stratified_perfect` to two strictly smaller geometric
obligations. Its proof constructs perfectness from the explicit finite-projective model,
uses reverse descent for the converse and bounds, and intersects the complete and residue
triangulated object properties for the closure clauses. The theorem's signature is unchanged.

Proved local-completeness triangulatedness using the existing internal-Hom exactness theorem
and exact slice restriction. Proved the common finite cohomology stratification, its lisse
restriction in every degree, and Noetherianity of each stratum. Proved residue extension
closure over arbitrary residue fields using the proved Noetherian finite-presentation
extension lemma on common strata. Exact geometric stalks give finiteness and flatness. Full bounded-below comparison gives a
triangulated etale essential image; its inverse image is precisely the residue predicate. Reusing that
image also proves residue triangulatedness without duplicated scalar or shift calculations.

Moved the existing definitions verbatim into `Sheaf.Paper.AdicStratifiedPerfectData`, publicly
reexported by the original module. `IsSfbResidueConstructible` only names the old second
conjunct. All twelve original declaration signatures are identical. Every original definition body
and docstring is retained. The fixed-scalar restriction functor is now `@[no_expose]`, with
proved public theorem `sfbFixedScalarRestriction_forget_iso` comparing its underlying
additive sheaf. Both private exactness proofs use this interface. This avoids repeatedly
unfolding the sectionwise scalar-restriction construction in importing modules.
No target statement or meaning changes. The change record is
`coord/changes/sfb-adic-stratified-shared-definitions.md`.

Validation: all eight final delivery modules compiled against the current published build
through `lcompile.py --all` (0.0--24.6 seconds each). Both current direct
consumers, `IntegralCohomologicalAdicCriterion` and `IntegralHeartLocalModel`, retain their
original source. The earlier `IntegralConstantModelHeartClosure` no longer imports the item.
No consumer edit is included.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.Scheme.adic_stratified_perfect`, by a Lean
reduction. Added two holes: this is a decomposition, with net progress 1 - 2 = -1 and the
number of holes increased by one, not a complete mathematical proof of the characterization.

The additional completed proof steps are:

- `CategoryTheory.locallyDerivedRingedIdealComplete_triangulated`.
- `AlgebraicGeometry.Scheme.sfb_adic_stratified_local_models`, using the remaining
  one-stratum lifting statement after constructing the common stratification in Lean.
- `AlgebraicGeometry.Scheme.sfb_adic_residue_extension_closed`.
- `AlgebraicGeometry.Scheme.sfb_adic_residue_triangulated`.
- `AlgebraicGeometry.Scheme.sfbFixedScalarRestriction_forget_iso`.

Exactly these two new named holes remain:

- `AlgebraicGeometry.Scheme.sfb_adic_lisse_stratum_models`
  (`lem-sfb-adic-lisse-stratum-models`): restrict completion and the specified residue
  along the immersion, transport them to the coefficient-sized models, and apply
  `adicResidueLissePerfectLift`. Identify its local coefficient model with the restriction
  of `sfbCompletedModel X I P`. The finite stratification and Noetherianity of its strata
  are already proved in the caller. This statement assumes one specified lisse residue
  stratum; it neither assumes global constructibility nor selects a stratification.
- `AlgebraicGeometry.Scheme.sfb_adic_stratified_descent`
  (`lem-sfb-adic-stratified-descent`): construct the idempotent-summand inverse limits,
  apply torsion-limit completeness, detect completeness globally, select finite covering
  pieces for bounds, compute residue termwise, and apply constructible comparison descent.

Both are public theorems with proofs exactly `by sorry`, complete natural-language proofs
and sources in their docstrings, and matching DAG nodes. No definition contains a hole.

Checked the source statements against Bhatt--Scholze Definition 6.5.1, Lemma 6.5.3 and
Proposition 6.6.11. Edge cases: empty schemes, zero complexes and rank-zero projective
terms, infinite residue fields, nilpotent maximal ideals, and fields with I=0. Maximality
excludes the zero coefficient ring. No dimension, invertibility or perfectness of A/I
as an A-module is assumed.

## No longer needed

Removed these former proof imports from the main module:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.Paper.ConstantModuleSectionProperties`
- `WeilConjectures.ConstructibleSheaf.Refinement`
- `Sheaf.AlgebraicGeometry.NoetherianStratumDetection`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`
- `Sheaf.Paper.PbcActualScalarPullback`
- `Sheaf.Paper.TorsionLimitSheafCompleteness`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`

The former public imports belong to the shared definition module and remain reexported.
Most original proof dependencies remain needed below the two unfinished geometric steps;
these import removals are not claimed as global module pruning.

The residue proof reuses `lem-sfb-discrete-noetherian-constructible-serre` through the proved
helper `noetherian_flc_of_shortExact`, imported from
`Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre`. It does not use
`sk-thm-pe-constructible-comparison` or `lem-sfb-noetherian-global-constructibility`;
reverse geometric descent still needs both. No global module pruning is claimed.

Reusing the essential image removed three imports from the residue-triangulated module:
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`,
`WeilConjectures.ConstructibleSheaf.Pullback`, and `Mathlib.CategoryTheory.Sites.Adjunction`.
Removed redundant direct proof imports `Mathlib.Algebra.Module.Projective`,
`Mathlib.RingTheory.Flat.Basic`, and `Mathlib.LinearAlgebra.Basis.VectorSpace` from the
residue-extension module. Its triangulated-subcategory import is private to its proof.
No unit statement or route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned geometric lemmas use coefficient-sized small-site module presentations, while
the item's predicates use the original sites. Applying them requires actual coefficient,
restriction and derived-completion comparisons; these do not follow by type conversion.
The remaining two geometric obligations explicitly isolate this work.

The retained report was stale: residue extension closure and the common stratification
had proofs, but it still listed them as holes. Its description of an independent finite-basis
extension proof was also obsolete: the current proof reuses the existing proved Noetherian
finite-presentation lemma. The source and node now record this dependency.

The current downstream scan finds 340 transitive consumers. `IsSfbAdicConstructible` is used
only by this item and `IntegralCohomologicalAdicCriterion`. The definitions retain their
bodies, universe parameters and exported names; no target meaning changes.

Earlier interrupted attempts had already assembled this packet. The resumed dispatch reset
the split-off reference clock to 2026-10-20 00:16:58 CST (attempt recorded in
`scratchpad/dry-run-resumed.log`). Its initial dry run refused two new holes before 72 minutes;
no push occurred. The dispatcher later reset the start to 2026-10-20 02:51:25 CST
(`.budget` start 1792435885.4233673), recorded by the dry runs in
`scratchpad/dry-run-final-resumed.log` and `scratchpad/dry-run-final-2.log`. We did not edit
that metadata. We continued proof searches, reused an existing proved extension lemma,
and investigated the two source geometric steps. The lifting theorem uses coefficient-sized
small-site module sheaves, while the predicates here use original sites and fixed scalar
sheaves. Their coefficient, completion and immersion comparisons require actual natural
isomorphisms and are not definitional equalities. The two remaining results are the separate
forward lifting and reverse descent arguments of Bhatt--Scholze Proposition 6.6.11.

The previous session's delivery preflight timed out after 900 seconds without a push.
Current compilation exposed expensive unfolding in `ringedDerivedRestriction` and
`completedAdicDerivedChange`. The proofs use selective unfolding at their structure
interfaces and local irreducibility in the residue proof, without changing either definition.

## New nodes

`lem-sfb-local-completeness-triangulated`: proved zero-kernel argument, in
`Sheaf.CategoryTheory.LocallyDerivedCompleteTriangulated`.

`lem-sfb-adic-stratified-local-models`: proved common stratification and application of the
one-stratum step, in `Sheaf.Paper.AdicStratifiedLocalModels`.

`lem-sfb-adic-lisse-stratum-models`: remaining immersion/site-transport and local lifting
step, in `Sheaf.Paper.AdicLisseStratumModels`.

`lem-sfb-adic-stratified-descent`: remaining reverse descent and bounds, in
`Sheaf.Paper.AdicStratifiedDescent`.

`lem-sfb-adic-residue-triangulated`: proved triangulated inverse-image argument, in
`Sheaf.Paper.AdicConstructibleResidueTriangles`.

`lem-sfb-adic-residue-extension-closure`: proved field-extension and essential-image
argument, in `Sheaf.Paper.AdicResidueExtensionClosure`.

The existing definition node `def-sfb-adic-stratified-perfect-data` only changes its Lean
attachment to the shared module. The change record is
`coord/changes/sfb-adic-stratified-shared-definitions.md`.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
