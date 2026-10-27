## What changed

Replaced the hole in `WeilConjectures.PodRawReconstruction.reconstruction_identityCompactSupport`
by a proof assembling the strict identity-tower comparison, normalized right-derived limit,
fully faithful constructible restriction, and scalar localization. The theorem's signature
and the already proved `reconstructionRawRationalNaturality` are unchanged.

Added `Sheaf.Paper.CompactSupportNormalizedTowerLimit`. Its comparison uses uniqueness of
right-derived inverse limit normalized by the derived units. The projection equation is
proved on K-injective representatives and extended by naturality, retaining the original
Roos projections. It does not infer uniqueness from a triangulated limit cone.
Three local elaboration blocks form projection and application terms directly, avoiding
repeated expansion of the large realization predicate; the resulting terms are checked
by Lean's kernel. The realization comparison has a short explicit local type,
so subsequent composition does not repeatedly unfold its existential specification.

Added `Sheaf.Paper.PodIdentityReductionTower`, containing the remaining strict-system
comparison. Moved `finiteOpenIdentity`, `finiteIdentity`, and `finiteRestrictedIdentity`
there verbatim, retaining their fully qualified names and public reexport from the item.
This avoids an import cycle. Their current external direct consumer,
`Sheaf.Paper.PodReconstructionCommonStageData` (unclaimed in local claims), continues
to see the same declarations in `IdentitySupport`. Its downstream coherence and
scalar-realization modules need no adaptation.

Validation: all three delivery modules passed compilation. The item passed its
single-file check in 46.0 seconds. An ordered item-and-consumer compile also passed,
including three `rfl` checks against the original finite-constructor bodies and a
check of the new public declaration. The consumer's common-stage data and scalar
realization dependencies were built in the private overlay. Temporary verification
sources are excluded from the delivery.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PodRawReconstruction.reconstruction_identityCompactSupport` using the
new smaller strict-system statement. The item has zero holes left. The new normalized
limit theorem `WeilConjectures.compactSupportNormalizedTowerLimit` is proved.

Added exactly one hole:
`WeilConjectures.PodRawReconstruction.identityReductionTower`, node
`lem-pod-identity-reduction-tower`. This isolates the identity compactification on strict
coefficient systems and its finite evaluation normalization. It contains no constructible
restriction, right-derived limit comparison, integral realization, or rationalization.
This is a decomposition of one original hole into one smaller hole, not a net hole closure.
The private categorical and localization helpers are proved; no definition has a hole.

## No longer needed

Removed the item's direct proof imports
`Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`,
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`,
`Sheaf.Paper.SfDerivedDirectImage`, and
`Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`.
The item retains its two private exposure imports (`import all`) of
`Sheaf.Paper.CompactSupportReductionTower` and
`Sheaf.Paper.CompactSupportRepresentativeIndependence`: its existing `ambientLinear`
proof uses their canonical scalar action and `normalizedDerivedLinear` APIs.
The normalized limit module also uses the latter module's private derived-unit API.
The required finite constructions remain available through the public dependencies and
the new strict-tower module. No module is withdrawn, and no old dependency is declared
globally unnecessary: the strict-tower subproblem still needs the finite operations.
The unit route and all target statements are retained.

## Where the brief, the DAG or earlier work was wrong

The original step 3 combines two distinct coherence problems. The existing
`exists_compactSupportReductionTower` supplies its chosen strict tower and evaluations,
but does not directly state the normalized comparison with the arbitrary calculus `A`.
That comparison is now the strictly smaller pending statement. Its proof must expose
the whole-system construction and its witness normalization, rather than treat an
existential specification or an unnormalized levelwise isomorphism as that construction. Merely identifying
levelwise derived functors would not supply a map of derived strict systems.

The published realization uses a separately recorded right-derived inverse limit. Its
comparison with `coefficientConstantTowerLimit` must preserve the unit and projection
normalizations; an arbitrary isomorphism of limit objects is insufficient. The delivery
proves this part by the actual universal property of right-derived functors.

Searches used leanfinder, loogle, grep, and leansearch. Mathlib supplies
`Functor.rightDerivedUnique`, `Functor.rightDerivedNatTrans_app`, fully faithful
preimage isomorphisms, and natural-isomorphism assembly, but no project-specific
strict identity-tower comparison. Edge cases checked when formulating the new statements:
zero integral objects and their zero scalar localization; every transition including
`m = n`; the generic normalized-limit theorem allows empty schemes. No completeness or
invertibility of completion on arbitrary derived objects is asserted by the split lemma.

## New nodes

`lem-pod-identity-reduction-tower` records the strict-system part of original step 3.
Its source is the blueprint's identity compact-support argument and Bhatt--Scholze
Definition 6.7.6, with the whole-system normalization argument explained in the docstring.

`lem-pod-compact-support-normalized-tower-limit` records the proved transport from the
published integral action to coefficient total limit, preserving all Roos projections.
The parent node's proof and proof dependencies now follow these two steps and the
categorical and rational assembly. The moved constructors remain attached to a node.

Change record: `coord/changes/Y8-pod-finite-identity-constructors.md`.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
