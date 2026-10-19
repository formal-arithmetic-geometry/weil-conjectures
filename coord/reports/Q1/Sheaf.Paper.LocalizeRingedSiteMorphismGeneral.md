## What changed

Proved `SheafOfModules.localize_ringed_site_morphism_general` with its original statement
and definitions unchanged. The proof constructs the canonical set, ring and module
inverse mates of the sectionwise identity direct-image squares, proves their invertibility,
and verifies the required ring adjunct and module adjunct equations.

The three new comparison modules are `LocalizedSetPullbackComparison`,
`LocalizedCommRingPullbackComparison`, and `LocalizedModulePullbackComparison`, under
`Sheaf.CategoryTheory.Sites`. Their comparisons are explicit mate constructions, with
proved unit equations and uniqueness lemmas; no definition chooses an arbitrary
isomorphism from an existence theorem.

The set proof constructs the representable inverse-image isomorphism by Yoneda, the
induced over-category adjunction, and its normalized fibre comparison. Product preservation
gives the geometric restriction comparison. Its unit equation identifies it with the
specified inverse mate. Transport through the slice equivalences also proves localized
finite-limit preservation, without invoking the existing sorried slice remainder theorem.

The ring proof lifts the set adjunction to internal commutative ring objects, constructs
its unit and counit, proves the adjunction identities, and transports the resulting
forgetful comparison by uniqueness of left adjoints. The normalized set comparison and
reflection of isomorphisms then prove the ring comparison invertible.

The module proof constructs the free-sheaf-module adjunction. Continuous cocontinuous
restriction commutes with sheafification and free modules. Its unit equation and mate
pasting prove the module comparison invertible on free sheaf modules. The canonical
free-module counit coequalizer presents every module by free modules; both comparison
functors preserve it, so the comparison is invertible on every module.

Added fully proved arbitrary-topology interfaces
`CategoryTheory.exists_localizedSheavesOverRepresentable_general` and
`CategoryTheory.overPost_isContinuous` to the existing localized-sheaf module. Existing
signatures, definitions, visibility and public imports are unchanged; consumers need no
adaptation. The change record is `coord/changes/over-post-continuity.md`.

Retained the earlier sandbox work, repaired its unfinished set and free-presentation
proofs, removed its remaining holes, and updated the proof routes in the DAG.

## Proved and sorry left

Original holes closed: 1 of 1, `SheafOfModules.localize_ringed_site_morphism_general`
(`lem-weil-pbc-localize-ringed-site-morphism`). New holes added: 0. No sorry remains in
any of the five delivered Lean modules.

The previously unfinished separate results are now proved:

- `CategoryTheory.sliceSetPullbackMap_isIso`
  (`lem-weil-pbc-slice-set-pullback-isIso`).
- `CategoryTheory.sliceSetPullback_preservesFiniteLimits` (same node).
- `CategoryTheory.sliceCommRingPullbackMap_isIso`
  (`lem-weil-pbc-slice-commRing-pullback-isIso`).
- `SheafOfModules.sliceModulePullbackMap_isIso`
  (`lem-weil-pbc-slice-module-pullback-isIso`).

Also proved the arbitrary-topology equivalence and continuity interfaces, all comparison
unit equations and uniqueness lemmas, and both adjunct identities. The module-section
identity in the main theorem is reflexivity. These proofs use the library's stated
ring-object lifting and sectionwise ring-object equivalence results; this delivery makes
no assertion that all imported library dependencies are free of the hole axiom.

Edge cases checked: arbitrary Grothendieck topologies, without subcanonicity or products
on the underlying sites; identity functors; zero coefficients and modules; empty covering
sieves, handled by separatedness. The presentation argument uses faithful underlying-set
forgetfulness and the abelian sheaf-module category, and does not assume the existence
of global free generators.

## No longer needed

Removed original proof imports `Sheaf.Paper.SliceSiteLocalization`,
`Sheaf.CategoryTheory.SiteCoveringAxioms`,
`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`, and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` from the assigned module.
The route uses neither the precoverage slice wrapper nor cochain tensor constructions.

The assigned proof no longer needs `lem-weil-pbc-slice-site-localization`,
`lem-weil-pbc-ringed-topoi-module-adjunction`, `def-pur-sheaf-tensor-product`,
`def-pur-localized-ringed-site`, or `def-weil-sheaf-of-modules-category` as proof lemmas.
Definition nodes remain in the unchanged statement dependencies.

Removed `Sheaf.CategoryTheory.Sites.SliceSheafInverseImageEquivalence` and its node
`stage3-slice-sheaf-inverse-image-equivalence` from the main and ring proof routes.
Both the canonical set comparison and localized finite-limit preservation are now proved
in this delivery, so the sorried remainder theorem is unnecessary here.

The module comparison route no longer needs `lem-weil-pbc-geometric-module-transport`,
`lem-weil-pbc-module-sheafification-restriction`, or
`lem-weil-pbc-ringed-topoi-module-adjunction` as intermediate proof lemmas. It uses the
proved canonical slice module-sheafification comparison
`lem-weil-pbc-slice-module-sheafification`, exact restriction
`lem-weil-pbc-finite-type-restriction-exact`, and the proved set comparison instead.

The ring route uses the already proved ring-only
`lem-weil-pbc-lifted-comm-ring-branch` instead of the larger
`lem-weil-pbc-adjunction-lifts-group-ring-objects`.

The ring proof avoids importing
`WeilConjectures.AlgebraicGeometry.EtaleRingDirectImageOperations`; its elementary
operation-transport equality argument is proved locally for arbitrary sites.
Removed unused private exploratory helpers `restrictionExtensionIso`,
`localizedRestrictionExtensionIso`, and `rawFreeRestrictionIso`.
No unit statement or realized unit step is bypassed, and no file is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original precoverage `SliceSiteLocalization` interface adds covering-closure hypotheses
absent from this item. The existing localized-sheaf implementation already had a complete
arbitrary-topology fibre/extension proof privately; the added general interface exposes
it without changing the old theorem.

An invertible direct-image square can have a noninvertible inverse mate. The set proof
therefore constructs the geometric comparison and checks its unit normalization explicitly.
The module argument likewise uses normalized mate pasting and a genuine free presentation.
It does not infer invertibility from the direct-image identity alone.

The earlier sandbox report described two remaining holes and a decomposition. That report
is superseded: both separate comparisons are proved here, with no new holes. Existing
Challenge target statements are unchanged. There are no forced adaptations of modules
held by another group.

## New nodes

- `lem-weil-pbc-over-post-continuous-general`: proved continuity on arbitrary slices.
- `lem-weil-pbc-slice-set-pullback-isIso`: proved normalized set comparison and localized
  finite-limit preservation.
- `lem-weil-pbc-slice-commRing-pullback-isIso`: proved normalized ring comparison.
- `lem-weil-pbc-slice-module-pullback-isIso`: proved normalized module comparison.

Each new node has its source, proof description, Lean attachment and recorded searches.
The existing main and localized-sheaf nodes are updated to match the actual proof route.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
