## What changed

Replaced the sole proof hole in `AlgebraicGeometry.Etale.properSupportSheafComposition`
without changing its signature. Constructed the functor as literal submodules of the
ordinary direct-image sections, with literal subtype inclusions. No object is chosen
from a non-unique unproved existence assertion. Unique preimages under injective maps
supply the comparison isomorphisms.

Added seven modules for closed supports of module sections, locality, linear and sheaf
calculus, closed images of supports, composition, open extension, and the remaining
base-change range comparison. The first six contain complete proofs. The main module
constructs the natural compositor and open comparison from their exact ranges, expands
the ordinary exchange to prove the precise unit/counit mate formula, and proves the
required composition coherence by ordinary mate pasting and injective cancellation.
All proof-only imports are non-public. Existing signatures and target meanings stay
unchanged. The unit `sk-prop-sf-cbc` has no realized steps to bypass.
Verified all eight modules with `lcompile.py --all`; each compiled within 10 seconds
on the final full run. Compared the original theorem signature verbatim with the
repository copy and checked that each node's proof dependencies are exactly the
union of its proof-step uses.

Repair of the current return (returned head `fe62cc70b`): removed the duplicated
private theorem `support_iso_image` from `ProperSupportCompositeRange`. The existing
`proper_iso_image` proof in `ProperSupportSectionLocality` is now public and documented,
and the composite-range proof calls it through its existing non-public import. Its
binders are unchanged and explicit. The locality node records the shared declaration;
the composite-range node records its locality dependency. Both modules are new in this
retained delivery and absent from current main, so no existing-library interface or
external consumer requires adaptation. The earlier zero-germ duplicate repair is retained.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.properSupportSheafComposition`.
Its proof is complete relative to the named base-change range obligation below;
this is a decomposition, not a claim that the target closure is axiom-free.

Proved, without any new holes in their modules:
`etaleModuleGerm_zero`, `etaleModuleSection_closedSupport`,
`sectionHasProperSupport_iff`, `etaleModuleGerm_restrict_zero`,
`etaleObjectPullbackSquare`, `proper_iso_image`, `properSupportSectionLocality`,
`properSupportSectionCalculus`, `properSupportPresheaf_isSheaf`,
`properSupportLowerStarInclusion_range`, `properSupportLowerStarInclusion_isIso`,
`module_section_zero_of_germs`, `properSupportSectionImage`, `properSupportComposite_range`, and
`openExtensionProperSupport_range` (all in `AlgebraicGeometry.Etale`).

Exactly one new sorry remains:
`AlgebraicGeometry.Etale.properSupportExchange_range`, node
`lem-cbc-proper-support-exchange-range`. It asserts only the injectivity and image of
the restricted ordinary exchange, not the original functor construction, composition,
open comparison, mate formula or pasting coherence. Its proof still needs the
proper-support pullback section map and normalized comparison on geometric fibres.
The complete intended argument and source are in its docstring and node.

Original holes closed: 1. New holes added: 1. Net holes closed in these delivered files:
0. Existing dependencies such as `properSupport_geometricStalk` and
`closed_proper_support_locality` remain their owners' obligations.

## No longer needed

Removed these direct proof imports from the item:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Sheaf.EtaleCohomology.EtaleSectionZeroOpen`
- `WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties`
- `WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.ClosedProperSupportLocality`
- `Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`

Most former dependencies are used inside the new proved modules or remain relevant to
the base-change proof, so removing their direct imports does not claim global pruning.
The two `Sheaf` wrappers for inverse-image composition units and module exactness are
unnecessary for this route: the existing source-library interfaces provide the needed
operations. No pre-existing Lean module is withdrawn. Removed the unused direct
zero-open import from the composition module once the closed-image theorem encapsulated
that argument. Closed-support lemmas and the support calculus are proof-only imports
where the public signatures do not need them. The main node now lists exactly its
immediate comparison obligations
and ordinary mate-pasting dependency; the lower nodes record the moved geometry.

The original explicit affine/permanence verification step is unnecessary:
`def-weil-closed-immersion`, `def-weil-finite-type-morphism`,
`lem-weil-pbc-closed-immersion-base-change` and
`lem-weil-pbc-separated-base-change` already have Mathlib interfaces and instances;
there is no new affine algebra proof to do. The old presheaf-sheafification comparison
step (`def-weil-pbc-sheafification`) is replaced by the open adjunction and its unit.
The separate closed-image invocation (`lem-weil-pbc-proper-closed-image`) is subsumed
by the image clause of `closed_subset_proper_over_base_properties`, used directly.
These are already foundational definitions or Mathlib leaves, so this saves planned
steps rather than withdrawing further Lean modules. The old direct composition-unit
invocation (`lem-weil-pbc-sets-etale-inverse-image-composition-units`) is encapsulated
by the existing module-valued `upperStarComp` and ordinary mate-pasting interfaces.
The geometric-stalk, inverse-image, pullback-section, adjoint and fibre-compatibility
obligations are retained in the exchange-range plan; they are not declared pruned.

The open-extension module no longer needs its duplicate zero-germ proof or its direct
`Sheaf.EtaleCohomology.EtaleSectionZeroOpen` import. It imports
`Sheaf.AlgebraicGeometry.ProperSupportSectionImage` for the single shared theorem.
The support-image module retains the zero-open import used by that proof.

The composite-range module no longer needs its duplicate `support_iso_image` proof.
It uses the one `proper_iso_image` theorem from the locality module; no import is added
or removed for this repair because the locality import was already needed.

## Where the brief, the DAG or earlier work was wrong

The current return correctly identified a second identical pair: `support_iso_image`
in the composite-range module and `proper_iso_image` in the locality module. The
repair removes the former and shares the latter by import, with no changed binders.

The previous delivery duplicated the zero-germ detection helper as private declarations
in two modules. The return correctly identified identical statements. This repair
keeps one public proof in the support-image module and uses it by import.

Two declared dependencies have Lean records but their recorded files are absent in
this checkout: `lem-cbc-proper-support-pullback-section-map`
(`Sheaf.SecSmoothPurity.ProperSupportPullbackSectionMap`) and
`lem-cbc-proper-support-fibre-restriction-compatibility`
(`Sheaf.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility`). They therefore
cannot be imported as the brief promises. Their intended work remains explicitly in
the exchange-range node and its proof, rather than being assumed to exist.

The support-image argument needs actual zero neighbourhoods and the Cartesian
restriction square; ordinary direct-image stalk base change would not justify it.
The composition converse uses the proper-preimage lemma on the reduced source and
its closed image; it does not assume factorization through the reduced image.
No mathematical statement was found false. Checked zero and empty supports, proper
and identity maps, and the inside/outside cases for an open immersion.

## New nodes

`lem-cbc-etale-module-section-closed-support`: detects zero germs after forgetting
module scalars and proves the closed-support criterion for all separably closed points.

`lem-cbc-proper-support-section-locality`: proves restriction stability and covering
locality by Cartesian support pullback and closed proper-support locality.

`lem-cbc-proper-support-section-calculus`: constructs literal support submodules,
their sheaf, functor and inclusion, and proves linear closure and proper specialization.

`lem-cbc-proper-support-section-image`: proves that the closed image of the original
proper support is exactly the support of its section of the support subsheaf.

`lem-cbc-proper-support-composite-range`: proves the composite inclusion has exactly
the required support image, transporting sections along the actual pullback compositor.

`lem-cbc-open-extension-proper-support-range`: proves the open comparison by adjunction,
the restriction unit, zero stalks outside the open, and geometric stalk detection.

`lem-cbc-proper-support-exchange-range`: isolates the still-open base-change range
calculation, with its source and complete proof plan. This is the only new hole.

No change record is needed: no existing statement or definition was changed, and no
existing module other than the assigned item was adapted.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
