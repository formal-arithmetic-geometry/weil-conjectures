## What changed

Proved `AlgebraicGeometry.ProEtale.proetale_scalar_local_model_representatives`
without changing its statement or either existing definition. The representative
argument works directly with internal modules: cover pullbacks detect equality,
adjunction embeds a locally modelled module into a product of direct images, and
well-poweredness bounds its subobjects. Covers indexed in Type u themselves form
a type in Type (u + 1), so they directly provide small codes without converting to
support sets in the site. Proved theorem instances seal products and
well-poweredness at the category boundary. A private abstract categorical helper
keeps the counting proof from repeatedly unfolding concrete sheaf constructions.
It reuses the proved private subobject
counting helper of `LocallyPrescribedModulesSmall`.

Added `Sheaf.Paper.ContinuousScalarFinitePresentation`, constructing the actual
scalar-extension functor and proving its finite-presentation classification. Maps
between finite free condensed modules lift to scalar matrices because continuous
functions on the point are scalars. Cokernel preservation supplies both directions.
The coefficient proof uses direct adjunction calculations and does not import
`FiniteConstantLocalModel` or `FiniteDiscreteScalarConstantModels` merely for
private point-section facts. The item also uses the exact source theorem in
`WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian` through a local instance,
rather than importing relative closed tensor constructions. The main theorem then
uses Mathlib's finite-presentation quotient description and
finite generation of the range of a finite free source.

Updated the item node to record this direct internal-module route and added the
coefficient comparison node. All added helpers are proved; there are no statement
repairs, definition repairs, consumer adaptations or source-library changes.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.proetale_scalar_local_model_representatives`.
Added zero holes. The new
`AlgebraicGeometry.ProEtale.continuousScalarFinitePresentation`
(`lem-sfb-continuous-scalar-finite-presentation`) is also proved.
Actual remaining hole count in the two delivered modules: zero.
No unfinished statements were split off. The item compiled cleanly in 11.9 seconds
after replacing the support-set conversion by direct cover codes. The combined import-order check also passed for both modules without warnings.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
and `Sheaf.Paper.CartesianCoefficients`. Removed the redundant proof import
`Mathlib.Algebra.Module.FinitePresentation`, supplied by the new comparison module.
The proof uses the existing abelian
localization comparison and invertibility instance of the actual coefficient map.
It does not transport all module structures to slice ringed sites.

The route does not need `def-pc-fibre-product` to establish finite limits of a
chosen site, nor `lem-weil-proetale-weakly-etale-localization` to transport the
entire module category to a slice. The latter obsolete `tool_uses` entry was
removed. The scheme pullback and cover facts already in the library suffice.
`sk-prop-sfb-cartesian-coefficients` and
`def-weil-pbc-internal-abelian-sheaf-module-equivalence` are not proof dependencies
of the new route. The existing public imports are preserved because they belong
to the item's public interface; none of those modules is withdrawn.

`lem-sfb-locally-prescribed-modules-small` remains needed for its proved private
subobject-counting helper, though its full sectionwise/slice theorem is not applied.
`lem-sfb-coefficient-sections-localization` and weakly-etale stability remain needed
for joint faithfulness of cover pullbacks. No whole module is withdrawn or claimed
unreachable from all targets.

## Where the brief, the DAG or earlier work was wrong

The statements are unchanged. The DAG's suggested passage through sectionwise
modules and slice coefficient rings is unnecessary: the same product/subobject
argument applies to the existing internal pullback/direct-image adjunctions.

The launcher reference clock in `.budget` now starts at 2026-10-23 16:37:30 UTC,
although the original claim and search record begin at 12:41 and 12:52 UTC. This
was observed after the provider/queue resumptions; no budget metadata was edited.

The scalar classification needs a comparison between the definition's finite
presentations over the continuous condensed coefficient ring and ordinary scalar
finite presentations. The new proved coefficient lemma makes this step explicit.
It holds for every commutative topological ring, without finiteness, discreteness,
flatness, or separation assumptions on that ring.

Zero ranks and the zero ring are included by the finite-free cokernel argument.
Torsion is retained. The joint-faithfulness proof uses sheaf separatedness on the
original cover after base change, so repeated objects and empty covers require
no separate support-cover assertion.

## New nodes

`lem-sfb-continuous-scalar-finite-presentation`, in
`dag/nodes/sec-six-functors-basics/`, records the proved coefficient-only finite
presentation comparison. It is a strictly separate algebraic step, with no scheme,
cover or representative-smallness assertion. Its module is
`Sheaf.Paper.ContinuousScalarFinitePresentation`. Three Mathlib searches found no
matching internal continuous-coefficient statement. No change record is needed:
all existing signatures, definitions and public imports are preserved.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
