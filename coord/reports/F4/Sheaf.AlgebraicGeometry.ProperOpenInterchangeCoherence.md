## What changed

Constructed the ordinary proper/open isomorphism from
`properSupportSheafComposition`, and proved its normalization into the common
ordinary direct image by cancelling the support-composition comparisons.
Constructed the derived isomorphism with the source library's
`rightDerivedFunctorPlusBaseChange` and its acyclicity criterion. The imported
open-extended-injective acyclicity theorem supplies the only geometric vanishing
input. A generic proved homology-to-classical-acyclicity lemma avoids expensive
unfolding of concrete etale derived categories. The isomorphism is a real
`asIso` construction, with a proved hom API and a named invertibility theorem.
Private generic lemmas handle unit factorization, acyclicity conversion and
isomorphism cancellation without unfolding concrete sheaf-module operations.
The ordinary and derived choices are uniquely determined by their prescribed
homs; no arbitrary object is extracted from a mere existence assertion.

The delivered modules are:

- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence` (existing statement unchanged).
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeBaseChange` (proved subargument).
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeRefinementNormalization` (remaining equation).
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeComposition` (remaining pasting equations).

The top-level proof assembles that construction with refinement normalization,
composition coherence, and arbitrary base change. Vertical identity is deduced
from refinement normalization and the existing `properOpenComparison_id`.
The new base-change module proves the ordinary cube by cancellation into the
common direct image and lifts it with the proved generic right-derived cube.
No existing public statement or definition is changed; no consumer adaptation
is required. The parent DAG route and the new subargument nodes follow this proof.

Validation: the complete main module compiled in 56.2 seconds. The base-change
module and both remaining statement modules also compiled. The delivery dry run
checks the final warning cleanup, all four files and the preflight together.

## Proved and sorry left

The original module has one hole, `AlgebraicGeometry.Etale.properOpenInterchangeCoherence`.
Its replacement is a complete proof from the named inputs and the strictly
smaller remaining statements below. This is a decomposition, not an axiom-free
proof of the original result: one upper hole is closed and two lower holes remain.

The new holes are exactly:

- `AlgebraicGeometry.Etale.properOpenInterchange_refinement_normalization`
  (`lem-cbc-proper-open-interchange-refinement-normalization`): identify the
  canonical derived lift with the independently specified component-restriction
  definition of `properOpenComparison`. Its statement has no existence conclusion
  and no invertibility claim; it only proves this one normalization equation.
- `AlgebraicGeometry.Etale.properOpenInterchange_composition`
  (`lem-cbc-proper-open-interchange-composition`): prove the two pasting laws and
  the horizontal identity law for the already constructed canonical derived
  transformation. The remaining work is the ordinary inclusion/compositor
  calculation and the formal `rightDerived_ext` lifting described in its docstring.

The arbitrary-base-change statement
`AlgebraicGeometry.Etale.properOpenInterchange_baseChange` has a complete, compiled
proof. All private helper proofs are complete;
there is no `sorry` in a definition or private theorem. The final source count is zero holes in the item and base-change module, and
one in each remaining statement module: one hole closed and two added (net −1).

Edge cases: the arguments use categorical identities, monomorphisms and zero
objects, so they also apply to the zero coefficient ring, empty schemes and empty
fibres. Original squares need not be Cartesian; only the four side squares in
the base-change statement are assumed to be pullbacks. No quasi-compactness or
residue-characteristic hypothesis is introduced.

## No longer needed

Removed these unused proof-only imports from the item (original public imports are
preserved):

- `WeilConjectures.CategoryTheory.RightDerivedPlusCube`
- `WeilConjectures.SixFunctors.BaseChange.Pasting`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`
- `Sheaf.AlgebraicGeometry.DerivedOpenRestriction`
- `Sheaf.AlgebraicGeometry.ClopenSectionDirectImage`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `WeilConjectures.SixFunctors.BaseChange.Derived`
- `WeilConjectures.SixFunctors.BaseChange.Square`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`

These original proof dependencies are not needed as proof steps in the new route
or its new subarguments (some definitions remain in the unchanged public signature):

- `def-weil-pbc-bounded-derived-subcategories`
- `def-weil-pbc-extension-by-zero`
- `lem-weil-pbc-derived-exchange-module-termwise`
- `lem-weil-pbc-direct-image-preserves-injectives`
- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-exchange-forget-coefficients`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `lem-weil-pbc-open-immersion-base-change`
- `lem-weil-pbc-proper-base-change`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `lemma-weil-pbc-leray-acyclicity`
- `prop-pur-kinjective-resolutions-exist`
- `prop-weil-pbc-inverse-image-modules-exact`

The remaining old proof dependencies used by a subargument have moved to that
node rather than being discarded. In particular open restriction and the clopen
section comparison remain in refinement normalization; ordinary base-change
pasting remains in the base-change module. No module is withdrawn. Global
reachability and pruning are left to the maintainer.

Removed obsolete top-level `tool_uses` approvals from the parent node:

- `prop-pur-kinjective-resolutions-exist`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-extension-by-zero-exact`
- `lemma-weil-pbc-leray-acyclicity`
- `lem-weil-pbc-kinjective-hom-derived`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-direct-image-preserves-injectives`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `lem-weil-pbc-proper-base-change`
- `lem-weil-pbc-open-immersion-base-change`
- `lem-weil-pbc-exchange-forget-coefficients`
- `lem-weil-pbc-termwise-adjunction-homotopy`
- `lem-weil-pbc-derived-exchange-module-termwise`

## Where the brief, the DAG or earlier work was wrong

The node `lem-weil-pbc-derived-exchange-module-termwise` points to
`Sheaf.AlgebraicGeometry.DerivedExchangeModuleTermwise`, but that file was absent
when this item was opened. The proof bypasses it using the already proved
`CategoryTheory.Functor.rightDerivedFunctorPlusBaseChange_cube` and the actual
module base-change definitions. Thus this missing declaration does not remain
an obligation of the delivery.

The attachment of `lemma-weil-pbc-leray-acyclicity` to the long-exact-sequence
module does not provide the acyclic-complex computation described in the parent
plan. The proved source `isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic`
provides precisely the needed comparison instead. No statement was weakened.

## New nodes

`lem-cbc-proper-open-interchange-refinement-normalization` isolates the comparison
with the clopen-section definition of the refinement map (Stacks 0F7B).

`lem-cbc-proper-open-interchange-composition` isolates the formal vertical and
horizontal pasting laws and horizontal identity (Stacks 0F7C and 0F7D).

`lem-cbc-proper-open-interchange-base-change` records the ordinary cancellation
and generic derived-cube proof of arbitrary base change (Stacks 0F7F).

The change record `coord/changes/F4-proper-open-interchange-proof-options.md`
explains the elaboration and scoped lint options flagged by the visibility check.
Existing signatures and definitions are unchanged; no consumer adaptation is needed.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
