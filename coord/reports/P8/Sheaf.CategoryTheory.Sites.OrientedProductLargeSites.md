## What changed

Replaced the single sorry in `CategoryTheory.OrientedProduct.universalWithLargeSites`
by a Lean proof assembling the actual projection construction, the orientation, compatible
lift existence and rigidity, and a proved comparison of universal cones. Its entire
signature is textually identical to the original, including all universes and structural maps.

The original explicit definitions moved verbatim to
`Sheaf.CategoryTheory.Sites.OrientedProductLargeSiteData`, publicly re-exported by the item.
Only their blueprint docstring attachments changed. Added `LargeOrientationFormula`, exactly
the final orientation conjunct of the existing theorem. This prevents an import cycle with
the two separate lift lemmas. The change record is
`coord/changes/P8-large-oriented-site-data.md`, including all 41 downstream modules and the
item, their current holders, and the unchanged-interface assessment. No consumer is adapted.
No module or declaration under `lean/WeilConjectures` is changed.

The following substantive parts have complete Lean proofs:

- Projection finite-limit preservation, using explicit right adjunctions to the two component
  functors; projection cover preservation by the type-(a)/(b) generators.
- Local equalizers of parallel arrows over a type-(c) arrow, singleton descent and bijectivity
  of restriction, and invertibility of the associated type-(c) map.
- `largeSiteMorphism`, using Mathlib's continuous site pullback and flatness; the associated
  representable comparison `largeAssociatedComparison` from uniqueness of left adjoints.
- `largeDirectImageFromRepresentables`, a unique extension of any transformation on
  inverse images of associated representables to direct images, proved by adjunction/Yoneda
  and the conjugate-unit identity; this also supplies the generic density step for rigidity.
- `largeOrientationExists`, using that extension and its calculation of the inverse-image mate.
- `universalComparison`, using both universal properties and the compatible composition
  calculation to exhibit inverse equivalences.
- The assembly of `universalWithLargeSites`, including its pullback formula and unique
  site-independence comparison, conditional on the two named lift lemmas below.

Validation: the full sandbox compiled cleanly, including `universalWithLargeSites` and
the three unchanged direct consumers `OrientedAffineNeighbourhoodLimit`,
`OrientedConstructibleSheaf` and `QcqsOrientedTriplePresentation`. The final seven-module run also compiled the extracted
representable-comparison helper, its orientation consumer, and the main theorem cleanly
after that refactor. A subsequent full run also compiled the isomorphism-extension
consequence and all seven modules without diagnostics. The actual hole count is given below; normal axioms/probes are checked by
the delivery preflight.

The two lift lemmas are separate parts of ILO XI 1.6, rather than copies of the assigned
statement: one asserts existence only, given the projections and their orientation; the other
asserts the formula and uniqueness for lifts already given, and asserts no existence. The
assigned theorem constructs the projections and orientation itself and proves the comparison
of site presentations. The remaining work is the site-extension calculation for the explicit
pullback functor and the structural pullback/density calculation in Lemma 1.5 and 1.6; neither
existing specialized site theorem states either complete result in the required universes.
Their source arguments, precise structural hypotheses and complete proof steps are recorded
in their docstrings and nodes.

Edge cases checked in the source argument: identity functors on the punctual site give the
usual pullback formula; no subcanonical-site assumption is used because every representable
is sheafified; empty covering families are handled by the actual sheaf axiom; local equalizers
do not require a type-(c) arrow to be a monomorphism. The latter avoids assuming that its
underlying diagonal is available in the original site.

## Proved and sorry left

Original item: one hole, in `CategoryTheory.OrientedProduct.universalWithLargeSites`.
Its body now contains zero sorry. The delivery adds exactly two holes:

- `CategoryTheory.OrientedProduct.largeCompatibleLiftExists`, node
  `lem-trf-large-oriented-lift-existence`.
- `CategoryTheory.OrientedProduct.largeCompatibleLiftRigidity`, node
  `lem-trf-large-oriented-lift-rigidity`.

These are named public theorems, each in its own module with proof exactly `by sorry`.
Every definition and every private helper has a complete body. The projection, representable-comparison and universal
comparison modules contain zero sorry and compiled cleanly in the final full-sandbox run. Thus the original
theorem is reduced from one hole to
two strictly separate results: this is a decomposition, not a net proof or a claim of positive
hole-ledger progress (one closed, two added). Existing holes outside the delivery, including
the small-universe `OrientedProduct.universal`, are untouched and are not used as proofs.

## No longer needed

Removed an unused `Mathlib.CategoryTheory.Sites.CoverPreserving` import from the new
projection module. Removed these five direct private imports from the assigned item:

- `Sheaf.CategoryTheory.RingedToposMorphism` and
  `Sheaf.CategoryTheory.SiteCoveringAxioms`: already available through the preserved public API.
- `Sheaf.CategoryTheory.SiteInverseImageTensor`: its coefficient-specific and size-specific
  theorem is unnecessary; the generic set-valued Mathlib site pullback is used directly.
- `Sheaf.CategoryTheory.SiteOfSheafGenerators`: needed only in the source argument for the
  separate existence lemma, not by the Lean assembly of the assigned theorem.
- `Sheaf.CategoryTheory.Sites.GrothendieckTopos`: the triple sheaf category is shown to be a
  topos directly by transporting along `AsSmall.equiv`.

The item no longer directly uses the old proof-dependency nodes
`lem-weil-pbc-left-exact-site-inverse-image-tensor`,
`lem-weil-pbc-pretopology-sheaf-condition`,
`lem-weil-pbc-site-of-sheaf-generators`,
`lem-weil-pbc-sheafification-sets-exact`,
`lem-weil-pbc-site-sheaf-sets-epi-kernel-pair-coequalizer`,
`lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`, and
`lem-weil-pbc-site-sheaf-sets-limits-sectionwise`.
The tensor theorem and the full pretopology-stability construction are unnecessary for this
route. The other generic facts remain dependencies where appropriate in the separate lift
nodes, and exact sheafification is also recorded for the projection construction. The
item's obsolete five top-level `tool_uses` approvals are removed; the separate nodes declare
the generic tools they use in their `split_report.tool_uses` for independent review.

No whole module is withdrawn or claimed pruned. In particular the public import of the small
oriented-product API is preserved, together with its existing proof imports. Moving these
definitions or changing the large theorem does not remove that upstream declaration or its
dependencies. The unit's normal-cone specialization route is preserved.

## Where the brief, the DAG or earlier work was wrong

The launcher resume reset the reference metadata: the earlier sandbox start was
1792749607 (2026-10-23 10:00 UTC), while the current `.budget` records
1792775636.9048166 (2026-10-23 17:13:56 UTC), budget 7200, session 86400.
The first delivery attempt at about 18:13 UTC refused the split at 59 minutes of
that reset clock (72-minute reference), before compiling or pushing. I continued
proof work, adding the isomorphism consequence of the representable comparison.
This packet continues the same dispatched item and earlier proof work. I did not edit
that metadata or wait merely to satisfy its clock. The pause was launcher-requested
to shorten the compile queue.

The old lean.note called `universalWithLargeSites` a transparent abbreviation to the small
universal theorem. It is actually the genuine theorem with independent object/hom universes
and had its own sorry, as the earlier reviewed_lean record already explains. The note now
matches the declaration and proof. Its statement has not changed.

The coefficient-specific `siteInverseImage_tensor` does not directly apply to all these
independent universes, and proves substantially more about modules than needed. The generic
Mathlib construction supplies the projections without that detour. The existence lemma's
source proof uses a small presenting generator site in the containing universe, making the
universe reduction explicit instead of applying the specialized theorem with unavailable
smallness assumptions on the original sites.

## New nodes

`def-trf-large-oriented-site-data` attaches the existing explicit definitions to their new
module and records the orientation predicate; it adds no proof hole. The move is documented
in `coord/changes/P8-large-oriented-site-data.md`.

`lem-trf-large-oriented-projections` records the proved site morphism construction,
representable comparison and orientation calculation (ILO XI 1.3, Stacks 00X6).

`lem-trf-large-oriented-lift-existence` records the existence-only part of ILO XI 1.6,
with the explicit pullback functor, cover checks, site extension, and cone compatibility.

`lem-trf-large-oriented-lift-rigidity` records ILO XI Lemma 1.5 and the formula/uniqueness
part of 1.6 for already-given lifts. It constructs no projection or lift.

`lem-trf-oriented-universal-comparison` records the proved formal comparison of any two
universal oriented cones, realizing Definition 1.7 after Theorem 1.4.

Each new node has a source, proof steps where applicable, the Lean attachment, three kinds
of Mathlib search, blueprint ancestry and its exact place in the retained unit route.

`lem-trf-large-oriented-representable-comparison` records the proved unique extension
from inverse-image maps on associated representables to direct-image transformations.
It is used in the orientation proof and in the source calculation of lift rigidity.
The same module proves `largeDirectImageIsoFromRepresentables`: extending an isomorphism
and its inverse gives inverse direct-image isomorphisms, by uniqueness and mate composition.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
