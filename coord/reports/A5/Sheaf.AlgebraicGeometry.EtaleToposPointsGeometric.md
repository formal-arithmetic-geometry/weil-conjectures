## What changed

The statement, universes, visibility, public imports and existing docstrings of
`AlgebraicGeometry.Scheme.etaleToposPoint_isGeometric` are unchanged. Its proof now
combines a natural geometric comparison, componentwise bijectivity, and a proved
extension theorem on sheaves. The geometric arguments are split into two strictly
smaller statements following steps 1--8 of the original node. No existing module
besides the assigned item is changed.

Three new modules define the actual lifted-representable functor, state the two
remaining geometric lemmas, and prove the categorical reconstruction step.
`etalePointFiberFunctor` is constructed directly by composing `uliftYoneda`,
sheafification and `p.inverse`; it contains no choice from an unproved theorem.
The reconstruction proof identifies geometric fibers of lifted representables,
uses Mathlib's `Presheaf.uniqueExtensionAlongULiftYoneda`, and descends the
isomorphism through sheafification with `Localization.liftNatIso`. There is no
new geometric-point or stalk construction chosen from a mere existence theorem.

All four modules compile without errors or warnings through `lcompile.py --all`.
The last compilation took 3.3, 3.2, 3.4 and 3.1 seconds respectively. All new Lean
lines fit the 100-character limit and all new modules disable auto-implicit
variables. The original node's proof and dependency list follow the implemented
argument; the original mathematical statement is preserved.

## Proved and sorry left

Original hole replaced by a complete proof from the stated intermediate lemmas:
`AlgebraicGeometry.Scheme.etaleToposPoint_isGeometric`
(`lem-trf-etale-topos-points-geometric`). The assigned module has zero remaining
holes, from one originally.

Two holes are added, both public named theorems in their own new modules, with
source citations and full proofs in words:

- `AlgebraicGeometry.Scheme.exists_etale_point_comparison`
  (`lem-trf-etale-topos-point-fiber-comparison`): constructs the geometric point,
  its support equivalence, and a natural comparison; asserts no bijectivity.
- `AlgebraicGeometry.Scheme.etale_point_comparison_bijective`
  (`lem-trf-etale-topos-point-comparison-bijective`): proves componentwise
  bijectivity for an already supplied comparison and support equivalence;
  constructs no point or comparison and asserts no isomorphism on all sheaves.

`AlgebraicGeometry.Scheme.etale_point_fiber_iso_to_stalk`
(`lem-trf-etale-topos-point-stalk-reconstruction`) and its private
`geometricRepresentableFiberIso` helper are proved completely using Mathlib.
The public functor definition also has no hole. There are no other sorries in
the packet. This is a decomposition: one old hole closed and two lower holes
added, not an axiom-free proof of the classification theorem or a reduction in
the total number of holes.

## No longer needed

Removed proof imports from the assigned module:

- `Mathlib.AlgebraicGeometry.Properties`
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`
- `Mathlib.CategoryTheory.CofilteredSystem`
- `Sheaf.AlgebraicGeometry.GeometricStalkToposPoint`

The first four provide infrastructure still needed by the geometric argument in
the remaining comparison lemma; their removal from this module is not claimed
as pruning that mathematics. The geometric dependency records are retained in
the new nodes.

The route no longer needs `lem-trf-site-point-reconstruction-sets` or
`Sheaf.Paper.SitePointReconstructionSets`: finite-limit preservation and the
cover condition follow directly from sheafification and the geometric morphism,
and the final reconstruction is proved from Mathlib density and localization.
It also no longer needs `lem-fix-geometric-stalk-topos-point` or
`Sheaf.AlgebraicGeometry.GeometricStalkToposPoint`: the conclusion already names
Mathlib's actual sheaf fiber, whose skyscraper adjunction and localization
comparison supply the required API. The original node's obsolete `tool_uses`
entry for this lemma is removed. These are route-level removals; no claim is
made that other targets stop using these modules. No module is withdrawn and
no source-library declaration is removed or altered.

All other original geometric proof dependencies are retained where needed in
the split nodes. The unit route is preserved: support, affine splitting,
coherent choice, affine-cover descent, then stalk reconstruction.

## Where the brief, the DAG or earlier work was wrong

The generic `site_point_reconstruction_sets` declaration fixes its coefficient
universe to the site's hom universe. Here the hom universe is `u` and the
statement uses sets in `Type (u+1)`. Applying that declaration verbatim therefore
does not provide the required reconstruction. The new directly defined functor
uses lifted representables, and the proved reconstruction uses the explicit
universe-polymorphic Mathlib API. No shared statement is repaired or weakened.

The original docstring describes the earlier generic reconstruction route;
it is preserved as existing documentation. The updated node and new proved
reconstruction theorem record the actual categorical route taken by this proof.

Edge cases checked in the proof plans: the empty scheme cannot admit such a
geometric morphism; empty affine fibers give empty values and empty bijections;
no surjectivity of cofiltered transition maps is assumed; arbitrary etale
objects are handled by affine covers. For injectivity their overlaps are
refined by affine covers, so separatedness or affine overlaps are not assumed.
All affine splitting is performed after restricting to an affine neighborhood
of the support, so the base scheme need not be separated. Bijectivity uses only
naturality and the stated support condition, not any hidden assumption that
the comparison already comes from an isomorphism.

## New nodes

`lem-trf-etale-topos-point-fiber-comparison`, in
`Sheaf.AlgebraicGeometry.EtaleToposPointFiberComparison`, covers the original
support, finite-fiber and coherent-choice steps. It includes the real definition
`etalePointFiberFunctor` and the first remaining hole. Source: Stacks Tag 04HU.

`lem-trf-etale-topos-point-comparison-bijective`, in
`Sheaf.AlgebraicGeometry.EtaleToposPointComparisonBijective`, isolates affine
splitting and descent to arbitrary objects for a given natural comparison.
It is the second remaining hole. Sources: Stacks Tags 04HU and 04HM.

`lem-trf-etale-topos-point-stalk-reconstruction`, in
`Sheaf.AlgebraicGeometry.EtaleToposPointStalkReconstruction`, is fully proved.
It isolates extension from lifted representables and descent through
sheafification. Sources: the reconstruction step of Stacks Tag 04HU and the
Mathlib point, presheaf density and localization APIs named in its proof.

All three records include source, proof, dependency unions, three kinds of
Mathlib search, blueprint ancestry, Lean attachment and the original unit and
chapter. No change record is required: no existing definition, statement or
public import is changed.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
