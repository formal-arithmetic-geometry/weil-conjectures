## What changed

Closed the hole in
`WeilConjectures.CompactSupportCondensedRealization.systemRestrictionOpenInv_isIso`
by a categorical proof from ordinary support preservation. The existing invertible
open units give full faithfulness. Essential-image membership makes the ordinary
counit invertible on the restricted open extension. A proved private
`exact_support_counit_isIso` transports this termwise counit calculation through
exact localization and its composition isomorphisms. The proved
`inverse_mate_isIso_of_support` then proves invertibility of the specified mate.
The mate, its definition, and all existing public signatures are unchanged.

The private proof import `Sheaf.Paper.SemilinearOpenRestrictionSupport` supplies
one strictly smaller assertion: arbitrary ring-system restriction preserves the
ordinary essential image of open extension. It mentions neither derived functors
nor mates, chosen comparisons, finite coefficient extensions, or this item.
Its docstring gives the direct-sum and sheafification proof in full.

The proper-image proof uses the library's ringed resolution/model-transfer lemmas
and derived-unit factorization, imported privately from
`ProEtaleRingSheafChangeAdjunction`. A complete local generic criterion resolves the
restricted complex, cancels the universal units on K-injective representatives,
and transports invertibility by naturality to all objects. It avoids loading the
finite-coefficient specialization in `ProEtaleFixedScalarRestrictionDirectImage`.
The small-site equivalence and constant-map naturality APIs are reused from
`VaryingRingOperations`; exactness and K-injective transport use the given
equivalence adjunctions. No supporting library module is adapted.

The tower scalar comparison is the identity on additive sections; its linearity
follows directly from the commuting ring square, and the fully faithful forgetful
functor lifts the presheaf isomorphism to module sheaves.

Compile-time improvements use explicit sectionwise uniqueness, explicit continuity
and equivalence adjunctions, direct additivity proofs, and explicit presheaf limit
transport. The strict-tower level proof uses a generic component formula for
whiskered restriction isomorphisms. Local irreducibility settings make the proof
use component and naturality APIs for coefficient maps, units, and derived functors.
Generic helpers temporarily exclude the unrelated completed-scalar-extension
additivity instance. Existing positive instance registrations and exported reducibility are unchanged.
The now-inapplicable suppression of `pbcRestriction_isRightAdjoint` is removed
with the private import that supplied that instance.
All existing public signatures and definition bodies are unchanged.

## Proved and sorry left

Original holes: 3. Closed by decomposition: 1,
`WeilConjectures.CompactSupportCondensedRealization.systemRestrictionOpenInv_isIso`.
Added holes: 1,
`AlgebraicGeometry.ProEtale.SemilinearProperOpen.scalarRestriction_ordinaryOpenSupported`
(node `lem-pur-semilinear-open-restriction-support`). This is a decomposition,
with no net reduction in holes.

Two holes remain unchanged in the assigned module, both on
`def-pur-semilinear-compact-support-coefficient-transport`:

- `WeilConjectures.CompactSupportCondensedRealization.systemRestrictionPullInv_isIso`.
- `WeilConjectures.CompactSupportCondensedRealization.limitRestriction_existsUnique`.

The support statement's empty-open, identity-open, and zero-module cases were
checked mathematically. They use respectively zero sums, the single identity
summand, and zero sums. The passage to unbounded complexes uses exact degreewise
functors. No flatness or preservation of K-injectives by scalar restriction is assumed.
Validation uses `lcompile.py --all` in artifact-output mode and the normal delivery's
independent preflight and probes. The packet is checked without profiling or tracing options
before submission. Sequential elaboration is retained as a compile-time setting;
it changes no declaration or proof obligation.

## No longer needed

Removed the private import and this proof's dependency on
`lem-coef-finite-free-compact-composition` / `Sheaf.Paper.FiniteFreeCompactComposition`.
The ordinary square uses Mathlib pushforward compositors directly.

Removed the full private import of `SemilinearProperOpenMatePasting`; its public
API remains needed. Its small coefficient-map, push/pull equality, and normalized-square
arguments are complete local proofs. The private `VaryingRingOperations` import
remains necessary for the existing small-site equivalence and constant-map naturality APIs.
Removed the private `ProEtaleFixedScalarRestrictionDirectImage` import and this
proof's edge to `lem-weil-proetale-direct-image-restriction-of-scalars`: the
generic unit-cancellation criterion is proved locally from the existing ringed
derived-unit factorization. The `ProEtaleRingSheafChangeAdjunction` import remains
needed for that factorization and the ringed-resolution/model-transfer declarations. No module or declaration is withdrawn, and the adopted
`WeilConjectures/` source tree is untouched. The unit `sk-thm-purity-transport`
and its realized steps are unchanged.

Searches also examined `SheafOfModules.RingedOpenScalarAdjunction.comparison`
and `scalar_open_existsIso` in `SemilinearProperOpenMatePasting`. The former needs
a slice presentation of the actual sequence-site functors; the latter has a
constant target ring. Neither directly supplies the two-varying-system support
assertion. The generic tower comparison in `RingedRestrictionStrictLimitCoherence`
has a relevant unit equation, whose transport to this item's restrictions remains
unfinished. These investigation-only modules were not imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction. The previous DAG text described the proper-image
argument but not the remaining open-mate argument. The new step records its support
subargument and the actual categorical combination. The generic mate criterion
needed on sequence sites is proved locally from the existing ringed derived-unit
factorization, with no finite-coefficient specialization or new public API.
The assigned node has no resolved imported blueprint ancestor
(`blueprint.from.node` is null). The new node preserves the inherited via chain
and cites the actual direct-sum/sheafification construction, Stacks 03DI and 03DJ.

## New nodes

`lem-pur-semilinear-open-restriction-support`, in
`Sheaf.Paper.SemilinearOpenRestrictionSupport`, is the ordinary support substep of
Step 10. It gives objectwise essential-image membership only, with no functorial
comparison or unit equation. LeanSearch, LeanFinder, grep, and the imported
blueprint search found no matching statement; the existing comparisons with
different endpoints are described above. No existing public statement or
definition is changed, and no change record for a supporting module is needed.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
