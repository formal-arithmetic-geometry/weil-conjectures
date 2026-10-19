## What changed

Completed `AlgebraicGeometry.proEtale_discreteNoetherian_constructible_serre` with its
signature unchanged. The already proved étale theorem and its helpers are retained. Private instances cache
étale sheafification, its local-bijectivity interface, and the abelian structure to avoid
repeated instance reconstruction during elaboration.
The pro-étale proof intersects the two finite stratifications on each affine open,
pulls the finite constant local models to their common strata, and applies local
kernel, cokernel and extension closure. Exact canonical constant-coefficient inverse
image identifies the resulting objects with the restricted kernels and cokernels.
The trivial stratification and zero constant module supply the zero clause.

Four new supporting modules define the local finite-presentation predicate, prove its
comparison with the existing finite-type constant-module predicate on AsSmall, prove
preservation under arbitrary scheme pullback, and apply the existing arbitrary-site
local Serre theorem. The comparison is proved on every localized site using module
sheafification and full faithfulness of restriction to constant scalars. The same
module values survive scalar restriction and site transport. The pullback proof pulls
an actual covering family back twice and uses the cartesian scheme identities.
There is no finite coefficient-set assumption or use of geometric points.

All new imports of the item are proof imports. No existing public signature,
definition, visibility, target, or consumer is changed. The DAG now records the
implemented proof, and each supporting module has a matching node.

## Proved and sorry left

Closed the sole remaining original hole:
`AlgebraicGeometry.proEtale_discreteNoetherian_constructible_serre`
(node `lem-sfb-discrete-noetherian-constructible-serre`).

The previously proved `AlgebraicGeometry.etale_discreteNoetherian_constructible_serre`
is retained. Added zero holes and left zero holes in all five delivered modules.
The three supporting theorems `proEtale_fp_localModels_comparison`,
`proEtale_fp_localModels_pullback`, and `proEtale_fp_localModels_serre` and every
helper are proved. No theorem is split off with `sorry`.

## No longer needed

Removed the following unused proof imports from the current item module:
`Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules`,
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
`Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre`,
`Sheaf.CategoryTheory.RingedSiteModules`,
`Sheaf.CategoryTheory.SiteInverseImageTensor`,
`Sheaf.CategoryTheory.SitePullbackAbelianExact`,
`Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`,
`WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`,
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`,
`WeilConjectures.CategoryTheory.SiteMorphismComposition`, and
`WeilConjectures.ConstructibleSheaf.Pullback`.
The surviving public imports and concrete proof dependencies supply the retained
étale proof. The local-model modules supply the pro-étale interfaces.

The old pro-étale plan's direct
uses of `lem-weil-pbc-etale-inverse-image-algebraic-structures`,
`lem-weil-pbc-left-exact-site-inverse-image-tensor`,
`lem-weil-pbc-site-pullback-abelian-exact`,
`lem-weil-pbc-site-morphism-composition`,
`lem-weil-pbc-etale-covering-base-change`, and
`lem-weil-pbc-localize-ringed-site-morphism` are removed from this node's proof
and obsolete tool-use list. Concrete pro-étale scalar restriction, pullback encoding,
weakly étale localization, composition and exactness interfaces provide these steps.
This does not claim those modules are absent from other targets or transitive imports.
The old direct pro-étale site and finite-presentation steps are now dependencies of
the supporting comparison nodes. The generic local Serre theorem remains needed
through the new local-model Serre theorem. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan suppresses two necessary comparisons:
its finite-type predicate uses a small site with equal object and morphism universes,
and its constants are global constant-ring module sheaves restricted to slices.
The intrinsic predicate uses sheafification directly on each slice after forgetting
commutativity of the constant coefficient ring. These predicates agree by the proved
scalar sheafification and AsSmall slice comparisons; they are not definitionally equal.
The existing pullback encoding theorem has a general clause assuming the canonical
coefficient map invertible. The existing arbitrary-ring coefficient comparison
supplies this assumption, so the finite-ring specialization is unnecessary.

The unit and chapter routes remain intact; the common finite partition and local
weak Serre argument are the original planned route. Supporting definitions are actual
constructions. The equivalence chosen from `constant_ring_module_sheaves` is fixed
by its specified restriction functor, hence unique up to the natural isomorphism
used by the proof; no arbitrary object is chosen from an unproved existence theorem.

## New nodes

- `def-sfb-proetale-fp-local-models`: the finite-presentation local-model clause,
  together with proved invariance under isomorphism and the zero case.
- `lem-sfb-proetale-fp-local-models-comparison`: comparison of intrinsic constants,
  fixed module-valued constants and constants on the AsSmall equivalent site.
- `lem-sfb-proetale-fp-local-models-pullback`: arbitrary scheme inverse image
  preserves these finite local models; this is Tag 093R with the models retained.
- `lem-sfb-proetale-fp-local-models-serre`: the local Tag 093U (3) closure clauses
  transported through that comparison, before any stratification is chosen.

All four are in `dag/nodes/sec-six-functors-basics/` and their modules are under
`lean/Sheaf/AlgebraicGeometry/`. No change record is needed because no existing
statement or definition is changed.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
