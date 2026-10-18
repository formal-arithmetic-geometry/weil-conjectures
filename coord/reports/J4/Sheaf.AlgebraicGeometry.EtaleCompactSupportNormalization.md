## What changed

Repaired reviewer C-fef35's duplicate-definition finding. The data module now publicly imports
`Sheaf.AlgebraicGeometry.EtaleCompactificationGraphMap` and uses F7's canonical
`etaleCompactificationGraphMap`. The duplicate graph, projection, and sheaf-comparison
definitions and their two immersion instances were removed from
`EtaleCompactSupportNormalizationData`; `refinementOpenCompactification` and
`identityEtaleCompactSupportComparison` remain. The unused FlatMono and Whiskering imports
were removed.

The graph sheaf normalization, finite graph isomorphism, geometric base-change, and derived
isomorphism modules now use `etaleCompactificationGraphMap` at every occurrence. The copied
DAG records were updated with the F7 statement dependency, the duplicate definition node now
records `compactSupportDerivedComparison`, and its statement identifies `Da` as built from
F7's `a_c`.

Repair C-30a0f: the current sheaf-dag checkout has neither the canonical graph-map
source module nor its node. The retained F7 source is therefore delivered as a real
dependency in this set, together with `def-f7-etale-compactification-graph-map`. This
closes the missing-source import at landing without restoring the duplicate graph
definitions removed in the preceding repair. All eight modules compile successfully
on the project server through `lcompile.py --all`. The delivery tool rebases the set
on its freshly fetched sheaf-dag base. The unchanged direct consumer
`EtaleAmbientAdjointLocality` also compiles against the public reexport. Source
comparison confirms all eight relocated helper signatures and bodies are identical,
and the original structure and theorem signatures are preserved.

## Proved and sorry left

Relative to the reviewed return at 30a0f75ae, this repair closes zero additional holes
and adds zero holes. The canonical graph-map module has zero holes. Relative to current
sheaf-dag, the delivery closes the original hole
`AlgebraicGeometry.Etale.nonempty_etaleCompactSupportNormalization` by decomposition
into the same three smaller geometric obligations already present in the reviewed return:

- `AlgebraicGeometry.Etale.compactSupportGraphSheafComparison_normalization`
  (`lem-asd-compact-support-graph-sheaf-normalization`): graph/component calculation
  under the sum adjunction remains;
- `AlgebraicGeometry.Etale.compactSupportGraphDerivedComparison_geometric_baseChange`
  (`lem-asd-compact-support-graph-geometric-base-change`): graph transpose calculation
  and localization descent remain;
- `AlgebraicGeometry.Etale.etaleCompactSupportGraph_coherence`
  (`lem-asd-compact-support-graph-coherence`): base-change graph transpose, proper/open
  refinement projection and identity unit/compositor calculations remain.

The constructor proof and the proved finite-etale and general derived-isomorphism
declarations are retained unchanged. One upper hole closes and three lower holes are
added relative to sheaf-dag (net -2); this is a decomposition, not a completed proof of
the entire geometric theorem. No definition contains `sorry`.

## No longer needed

The duplicate declarations
`clopenSectionProjection`, `compactSupportGraph`,
`compactSupportGraph_isOpenImmersion`, `compactSupportGraph_isClosedImmersion`,
`compactSupportGraphCompositionIso`, `compactSupportGraphProjection`, and
`compactSupportGraphSheafComparison` are no longer needed: F7's
`etaleCompactificationGraphMap` supplies the canonical map and its construction.
The FlatMono and CategoryTheory.Adjunction.Whiskering imports are no longer needed.
No additional existing module was withdrawn.

Relative to current sheaf-dag, the original module removes these direct proof imports;
tools needed below the new obligations remain there:

- `Sheaf.EtaleCohomology.SepClosedFieldVanishing`.
- `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`.
- `Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`.
- `Sheaf.AlgebraicGeometry.OpenSectionClopen`.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`.
- `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`.
- `Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct`.
- `Sheaf.AlgebraicGeometry.ProperSupportSheafComposition`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.

The parent node's direct proof now uses the four new construction/core nodes plus exact
sum adjunction, termwise derived adjunction and adjunction conjugacy. The original proper
base-change, stalk, mate-pasting and proper/open refinement dependencies remain needed below the new derived-isomorphism and coherence nodes; they are not claimed as globally
pruned. The parent node's unused tool approvals are removed, retaining their old order.
The removed direct approvals are listed below; many are still used below the new nodes
and are not claims of global pruning:

- `lem-kun-0ezp`.
- `lem-kun-proper-base-change-torsion-ring`.
- `lem-weil-pbc-etale-base-change-finite-limits`.
- `lem-weil-pbc-etale-shriek-base-change-modules`.
- `lem-weil-pbc-exact-functor-derived-factorization`.
- `lem-weil-pbc-exact-functor-derived-functor`.
- `lem-weil-pbc-extension-by-zero-stalks`.
- `lem-weil-pbc-geometric-point-pullback-stalk`.
- `lem-weil-pbc-localization-universal-property`.
- `lem-weil-pbc-mate-pasting`.
- `lem-weil-pbc-open-immersion-base-change`.
- `lem-weil-pbc-open-section-clopen`.
- `lem-weil-pbc-proper-base-change`.
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`.
- `lem-weil-pbc-unbounded-derived-iso-cohomology`.
- `lemma-weil-pbc-geometric-stalk-conservative`.
- `prop-weil-pbc-geometric-stalks-exact`.
- `lem-weil-pbc-etale-sheaf-clopen-product`.
- `lem-cbc-proper-support-sheaf-composition`.
- `prop-weil-pbc-inverse-image-modules-exact`.
- `lem-pc-quasi-compact-base-change`.
- `prop-weil-pbc-kinjective-resolutions-exist`.
- `lem-amb-unbounded-proper-open-interchange`.


The following dependencies are unnecessary for this route:

- `lem-kun-0ezp` / `Sheaf.EtaleCohomology.SepClosedFieldVanishing`: finiteness of the
  geometric fibre now follows directly from Mathlib's quasi-finite/Artinian-base theorem,
  rather than decomposition into geometric field points. Other users remain in the DAG.
- `lem-weil-pbc-open-section-clopen` / `Sheaf.AlgebraicGeometry.OpenSectionClopen`:
  the graph geometry is proved with Mathlib's section/immersion API, and the finite case
  uses closed range of the compactification immersion of a proper morphism. No separate
  geometric open-section lemma is needed.

- `lem-asd-clopen-geometric-sections-derived-evaluation` /
  `Sheaf.AlgebraicGeometry.ClopenGeometricSectionsDerivedEvaluation`: the proved finite-etale
  theorem replaces this separate unbounded evaluation obligation. It has only this parent
  in the existing DAG, so this route removes its sole use.
- `thm-amb-etale-exceptional-adjoint` /
  `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`: the field quantifies over any chosen
  adjunction, so conjugacy proves it directly without a theorem supplying an adjunction.
- `lem-cbc-proper-support-sheaf-composition` /
  `Sheaf.AlgebraicGeometry.ProperSupportSheafComposition`: the required sheaf equation is reduced to graph transposition and the canonical
  comparison into direct
  image, without choosing a second proper-support functor package.

Clopen-product and open-section results are unnecessary for constructing the graph map:
Mathlib proves its open/closed immersion properties, and the existing clopen extension
comparison supplies the projection. The clopen-product node remains below the graph sheaf
calculation. The separate
open-section-clopen lemma is not used: Mathlib proves the graph immersion instances,
and IsFinite.of_locallyQuasiFinite supplies finite geometric fibres directly.

## Where the brief, the DAG or earlier work was wrong

The earlier C-fef35 return duplicated the graph-map construction provided by
`def-f7-etale-compactification-graph-map`, creating a second definition of the same notion.
The DAG definition node consequently listed those duplicate declarations and named the old
sheaf map as its primary declaration. This repair makes the F7 map the sole canonical
construction and records the derived comparison as the data node's declaration.

C-30a0f passed that mathematical repair, but landing exposed that its canonical
graph-map dependency had no source at the landing base. Bundling that retained source
and its definition node repairs the actual missing-source defect; compiling against a
cached artifact alone would not repair it.

## New nodes

The definition node `def-f7-etale-compactification-graph-map` is bundled because it is
absent from current sheaf-dag. It records the unchanged canonical F7 definition, source,
explicit graph/adjunction construction, edge cases, searches and exact Lean signature.
Its ID was already referenced by the returned delivery; no alternate definition, new
theorem statement or new `sorry` is introduced by this repair.

Six further nodes are retained from the reviewed return, and are also new relative
to current sheaf-dag:

`def-asd-compact-support-graph-comparison` records the derived graph comparison,
localization component formula, core/coherence structures and unchanged helpers.
It uses the canonical F7 graph map rather than defining another graph map.

`lem-asd-compact-support-graph-sheaf-normalization` states the sheaf graph-extension
identity; its graph/component verification is one of the three remaining holes.

`lem-asd-compact-support-finite-graph-isomorphism` records the proved finite-etale
case, using the canonical sheaf map, K-injectives and derived-unit cancellation.

`lem-asd-compact-support-graph-geometric-base-change` states the forward graph-map
identity at geometric changes of base; its transpose calculation remains a hole.

`lem-asd-compact-support-graph-derived-isomorphism` records the proved reduction
from finite geometric fibres and proper base change to invertibility of the
specified graph comparison, and its uniquely determined canonical inverse.

`lem-asd-compact-support-graph-coherence` records the three remaining equations for
the fixed comparison; the coherence theorem is the third remaining hole.

The existing parent node `lem-asd-etale-compact-support-normalization` retains the
reviewed proof route. The change record is
`coord/changes/J4-etale-compact-support-graph-construction.md`.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
