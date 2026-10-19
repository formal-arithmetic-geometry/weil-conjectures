## What changed

Proved `AlgebraicGeometry.Scheme.clopenSectionComponent` with its original signature and
all three existing definitions unchanged. All proof helpers are private in the assigned
module; no support module or split-off theorem remains in this delivery.

The restriction pair is an equivalence with inverse given by the biproduct of the two
extensions. Existing disjoint-open vanishing and local conservativity prove its inverse
laws. Full faithfulness lifts differentials and homotopies, and exactness detects homology
componentwise. The existing clopen extension/direct-image comparison and exact-restriction
adjunction prove preservation of unbounded K-injectives.

The direct-image isomorphism is explicitly normalized: restriction along the section arrow
composes with the open counit to the canonical direct-image composition isomorphism. The
pullback projection identities prove that equality. Transport through the existing uniquely
normalized coefficient comparison proves the required section formula; degreewise mapping
and naturality prove all complex and homotopy compatibilities.

Added proof-only imports of the source library's pro-etale clopen comparison, direct-image
coherence, K-injective transport, and Mathlib exact-functor homology API. The resumed single-file
compile succeeds in 8.3 seconds against the current shared build (resumed verification). Removed a duplicate
local instance attribute from the retained attempt. The delivery probe checks all
introduced constants.

Repair of returned head `60ae96e839`: removed `set_option warn.sorry false`.
The source ledger had counted the `sorry` component of that option name as an
unattributed hole at line 31, character 1308. Warning suppression is unnecessary
for the completed proof. No proof or public signature changes in this repair.

The dry-run interface gate also requires a change record for the generic private helper
section variables and local biproduct-preservation instance attribute. The record
`coord/changes/A6-clopen-section-private-helper-commands.md` lists all transitive consumers.
No consumer adaptation or public mathematical change is needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.clopenSectionComponent`
(node `lem-sp-clopen-section-component`). Added 0 holes; 0 split-offs; no sorry remains in
the delivered module. The proof uses the existing section-normalized realization theorem
`sfIntrinsicDirectImageComparison_existsUnique`; its existing upstream hole is unchanged.

## No longer needed

Removed these unused proof imports:
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`,
`Sheaf.CategoryTheory.SiteCoveringAxioms`,
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`,
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, and
`Sheaf.CategoryTheory.RingedSiteModules`.
The last three remain available transitively through the unchanged public imports.

Removed direct proof dependencies `lem-weil-pbc-open-immersion-base-change`,
`lem-weil-pbc-weakly-etale-composition-base-change`,
`lem-weil-proetale-weakly-etale-localization`,
`def-weil-pbc-sites-and-cohomology`, and `def-weil-sheaf-of-modules-category`.
The proved fixed-scalar restriction API supplies the disjoint-open decomposition directly;
no fresh localization or sheaf-gluing theorem is needed. Removed the first three obsolete
entries from the node's `tool_uses`, retaining the extension-by-zero adjunction approval.
Definitions of sites and module sheaves remain used through the existing statement interfaces.

The retained sandbox's proposed Core, Complex, Tail, Comparison and Base support modules and
three provisional nodes were never delivered. Their proof content is now private and fully
proved in the assigned module; they are absent from this delivery. No existing repository
module is withdrawn. No module can be claimed globally pruned solely from these import
removals, since the unchanged public imports may still reach it.

## Where the brief, the DAG or earlier work was wrong

The earlier report describing three remaining holes was stale. All three component proofs
and the section-normalized comparison now compile without new holes. The source library
already proves the clopen comparison, cross-component vanishing and local conservativity,
so rebuilding the sheaf gluing and localized-site equivalence was unnecessary. The unit
record has no realized statement or proof-step nodes; its route is not bypassed.

The landing return identified the inherited warning-suppression command as an
unattributed source hole. The command is now removed; the module contains no
`sorry` token, including in option names.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
