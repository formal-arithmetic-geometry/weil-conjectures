## What changed

Repair of returned delivery 78f937a7247: corrected the exchange change record's
`## Users` inventory to include the two omitted current consumers,
Sheaf.AlgebraicGeometry.HigherDirectImagesLimits and
Sheaf.AlgebraicGeometry.RelativeHigherImageContinuityPreorder. Recorded their
current unclaimed status and the exact uses of the preserved exchange. Removed
the stale assertion that the item had zero downstream modules. Neither consumer
needs a source adaptation: the exchange is re-exported with its original body,
signature and attributes. This repair adds or closes no additional theorem holes.

Repair validation: all nine retained modules compiled against the current server
build; the slowest took 27.5 seconds. Unchanged current-source copies of both
reported consumers also compiled against the sandbox: HigherDirectImagesLimits
in 40.3 seconds and RelativeHigherImageContinuityPreorder in 52.4 seconds.
These temporary copies were byte-checked against the repository and removed
from the delivery. The current downstream.py scan reports nine downstream
modules and exactly the item plus these two consumers as exchange users.
The moved exchange signature/body and original continuity theorem statement
were checked verbatim against the current source.

Replaced the single sorry in
AlgebraicGeometry.Etale.higherDirectImage_relative_continuity by a complete
geometric-stalk filtered-colimit argument. Its signature is unchanged. The
proof uses the specified colimit cocone and actual exchange/coefficient legs;
its coprojection equation is hcH.fac, not an unspecified object isomorphism.

Moved relativeHigherDirectImageExchange verbatim into
Sheaf.AlgebraicGeometry.RelativeHigherDirectImageExchange and publicly
re-exported it. Added the concrete relativeHigherDirectImageDerivedMap and a
canonical, irreducible raw-section functor and derived-Hom-to-homology comparison
with a proved API. The functor caches both its abelian groups and its maps, so
consumers avoid conversions between expanded derived Hom and point-fibre groups.
The exact-pullback homology comparison is also named and irreducible, with an
equation identifying the original degreewise exchange.
This keeps the comparison constructions available to the supporting lemmas
without an import cycle, and avoids unfolding the free-sheaf and inverse-image
constructions throughout their proofs.

Proved finite-stage germ representatives from local factorization of raw
classes and the comparison's naturality. Proved affine-section eventual
vanishing from finite-family raw vanishing: a first local lift represents the
homology section, a second local refinement kills its raw derived image, then
a finite affine cover and sheaf separatedness give the section equality.
Proved germ eventual vanishing by representing a germ, refining its zero
limit image, and applying this affine-section result.

The two retained cohomological statements are separate parts of Stacks 0EYM:
local factorization of raw derived classes (without H, cH or the colimit-isomorphism
conclusion), and the raw cohomological kernel mapping to zero in the sheaf
colimit. They are not renamed copies of the item. Finite-stage zero detection
and finite common-codomain assembly are proved from the second statement. The
formal passage through homology, two local refinements, finite covers, germs
and the colimit universal property is proved in the delivery. The finite-family
result uses the existing abelian filtered-section zero theorem after reindexing
by the final AsSmall equivalence to align its index universes; filteredness then
provides one common killing arrow.

The unit's affine localization, affine etale descent, coefficient continuity,
cohomology continuity and actual mate/chart comparison remain in these two
nodes' source proofs. In particular the degree-zero section formula of unit
step 3 remains in the cohomology-kernel node; it is not discarded by using
stalks for the final conservative isomorphism test.

## Proved and sorry left

Original item: 1 hole closed, 0 holes left, by
AlgebraicGeometry.Etale.higherDirectImage_relative_continuity.
This is a decomposition: 2 new holes are retained, so it is not a net
sorry-free proof of continuity.

The delivery also proves these new public theorems:

- AlgebraicGeometry.Etale.relativeHigherDirectImageExchange_eq_homology
  (lem-kun-relative-higher-image-exchange-homology).

- AlgebraicGeometry.Etale.derivedHomologySectionsComparison_spec
  (lem-kun-derived-homology-sections-comparison).
- AlgebraicGeometry.Etale.relativeHigherDirectImage_germ_descent
  (lem-kun-relative-higher-image-germ-descent).
- AlgebraicGeometry.Etale.relativeHigherDirectImage_finite_raw_eventually_zero
  (lem-kun-relative-higher-image-finite-raw-vanishing).
- AlgebraicGeometry.Etale.relativeHigherDirectImage_affine_section_eventually_zero
  (lem-kun-relative-higher-image-affine-section-vanishing).
- AlgebraicGeometry.Etale.relativeHigherDirectImage_germ_eventually_zero
  (lem-kun-relative-higher-image-germ-vanishing).

Every remaining sorry, each exactly a named public theorem body:

- AlgebraicGeometry.Etale.relativeHigherDirectImage_raw_local_factorization,
  in RelativeHigherDirectImageRawLocalDescent,
  node lem-kun-relative-higher-image-raw-local-descent.
- AlgebraicGeometry.Etale.relativeHigherDirectImage_cohomology_kernel,
  in RelativeHigherDirectImageCohomologyKernel,
  node lem-kun-relative-higher-image-cohomology-kernel.

No definition contains sorry, and no arbitrary witness is selected from an
unproved existence theorem. All four new data constructions have explicit
bodies. Private helpers are proved.

Validation: the full sandbox compiled in dependency order through
lcompile.py. The revised chain, including the proved finite-family theorem,
compiled without warnings. The longest consumers took 30.0 s (affine-section
vanishing) and 45.8 s (germ descent), within the unchanged 60-second file limit. Mechanical
checks confirm the original theorem signature and moved exchange definition
are verbatim, all public declarations have matching nodes, and no changed-node
dependency cycle was introduced. The shorter AsSmall universe adapter also compiled separately in 6.2 s.
There are exactly two retained theorem holes. The first server preflight
found missing LeanSearch records and definition-signature modifier mismatches;
these metadata issues are corrected, and every new node's signature and three
search kinds were checked against the delivery parser. That preflight noted
that the affine-section module's axiom probe timed out at 60 s; its normal
compile succeeded, and the merge will retry the axiom probe.

## No longer needed

No module is withdrawn, and no mathematical dependency is claimed globally
unnecessary. The affine-etale/cohomology source dependencies remain under the
two new cohomological nodes. The original pending DAG parents are preserved.
The item itself remains needed.

The main theorem no longer directly imports:

- Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
- WeilConjectures.AlgebraicGeometry.LimitAffineTransition
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
- WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
- WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
- WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos
- Sheaf.AlgebraicGeometry.AffineEtaleSiteColimitStatement
- WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
- Sheaf.CategoryTheory.CohomologyColimitSites
- WeilConjectures.CategoryTheory.ColimitSites
- WeilConjectures.CategoryTheory.FilteredColimitCategories
- Sheaf.CategoryTheory.SiteCoveringAxioms
- WeilConjectures.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
- Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs

Removed main-node tool_uses entries (their needed mathematics remains in the
retained cohomological nodes):

- lem-weil-pbc-derived-inverse-image-composition
- prop-weil-pbc-derived-inverse-image-adjunction
- prop-weil-pbc-inverse-image-exact
- lem-weil-pbc-limit-affine-transition
- lem-weil-pbc-etale-inverse-image-restriction
- sbc-lem-higher-direct-image-presheaf
- lem-weil-pbc-site-sheafification-sections-local
- lem-weil-pbc-affine-etale-site-topos
- lem-weil-pbc-affine-etale-site-colimit
- lem-weil-pbc-cohomology-colimit-of-sites
- def-weil-pbc-sites-and-cohomology
- lem-weil-pbc-etale-cohomology-limit-of-schemes
- lem-weil-pbc-exact-functor-complex-cohomology
- lem-weil-pbc-etale-limit-tail-open-coefficients
- lem-kun-derived-exchange-cube

Its proof now directly imports the two germ results and filtered colimits of
abelian groups. The old direct proof dependencies and their tool approvals
are removed from the main node; the needed source dependencies are recorded
on the appropriate new nodes. No existing upstream declaration is removed,
weakened, or changed to sorry. The public BaseChange.Derived import is preserved
transitively through the new public construction module. No public dependency
from the old module is lost.

## Where the brief, the DAG or earlier work was wrong

The previous change record's zero-user claim was stale. The landing tools at
returned head 78f937a72 correctly required HigherDirectImagesLimits and
RelativeHigherImageContinuityPreorder in `## Users`. Both are now listed and
their source uses inspected; the repair preserves the retained proof packet.

No false original statement was found. The existing CartesianHigherImage*
results were checked as possible shortcuts, but they fix a field, a morphism
and a single coefficient sheaf; they do not cover the varying, possibly
non-cartesian systems and varying coefficients here. The fixed-base
HigherDirectImageLimitSystem theorem likewise does not cover varying bases.

The local raw descent statement permits a pointed refinement. One cannot
silently assume that an arbitrary affine etale object is finitely presented
over the unrestricted, possibly non-quasi-separated base. Localization on
inverse images of stage affine opens precedes finite-presentation descent.
The retained nodes explicitly include this localization and do not add a
qcqs-base, cartesian-square, torsion, or bounded-degree hypothesis.

Edge cases checked in the source arguments: q=0, zero coefficients, empty
affine test objects, empty finite families, empty schemes (no point to check),
and a nonempty directed index with no least element. The finite-family result
uses the same finite filtered common-codomain lemma for an empty family. The second local refinement in
the kernel argument is explicit Lean, not a claim that a raw class is globally
zero merely because its homology section is zero.

## New nodes

- def-kun-relative-higher-image-derived-map: the actual derived mate followed
  by the coefficient map, in the new construction module.
- def-kun-relative-higher-image-exchange: attachment of the verbatim moved
  degreewise exchange construction.
- def-kun-relative-higher-image-homology-iso: the named, irreducible exact-pullback
  homology comparison, with its concrete construction.
- lem-kun-relative-higher-image-exchange-homology: the unfolding equation for
  the original exchange through the named derived mate and homology comparison.
- def-kun-derived-homology-sections-functor: the concrete raw-section functor,
  with cached presheaf abelian groups and natural maps.
- def-kun-derived-homology-sections-comparison: the concrete represented-generator
  comparison, with no choices of sections or derived representatives.
- lem-kun-derived-homology-sections-comparison: local bijectivity and naturality
  API, proved from the existing abelian comparison.
- lem-kun-relative-higher-image-raw-local-descent: source finite-stage
  factorization of a raw class after pointed refinement; retained hole.
- lem-kun-relative-higher-image-germ-descent: the proved passage from raw
  factorization to stage germs by exact-pullback homology and naturality.
- lem-kun-relative-higher-image-cohomology-kernel: the chart-cohomology kernel
  maps to zero in the higher-image sheaf colimit; retained hole.
- lem-kun-relative-higher-image-finite-raw-vanishing: proved finite-stage
  detection and common-index assembly from that cohomological kernel.
- lem-kun-relative-higher-image-affine-section-vanishing: the proved two-refinement
  and finite-cover argument from raw kernel detection to section vanishing.
- lem-kun-relative-higher-image-germ-vanishing: the proved passage from affine
  section vanishing to germ vanishing.

Change record: coord/changes/H5-relative-higher-image-exchange-interface.md.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
