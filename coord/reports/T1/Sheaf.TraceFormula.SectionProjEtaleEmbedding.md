## What changed

Replaced the sorry in AlgebraicGeometry.AlgebraicSpace.section_proj_etale_embedding with
an explicit reduction along the original section-algebra / generation / canonical-map
route. Its signature and every conclusion are unchanged. No target or adopted source
module is changed.

Moved SectionProjModel, with identical signature and fields, into the new public
Sheaf.TraceFormula.SectionProjModel definition module. The item publicly reexports it.
This prevents cycles between the item and its new presentation/comparison lemmas.
The change record is coord/changes/T1-section-proj-model-location.md.

The main proof obtains the existing normalized section algebra, presents it, compares
it with each supplied local model, chooses the coefficient data, and applies canonical
map descent. It proves etaleness of the local scheme charts by relative-morphism-property
base change. It constructs the final representing scheme by testing the resulting
representable open immersion over the identity of its scheme target: the projection to
X is an isomorphism, and the pullback equation is exactly the required Yoneda equation.

SpaceLineProjEtaleDescent is proved rather than left as another hole. It applies the
existing space_line_module_proj_map. Its private subsheaf argument lifts each covering
arrow by the given Cartesian square, then uses Subfunctor.isSheaf_iff to prove the
whole generation open is top. The proof converts canonical-map specifications into
test-map specifications and uses the existing space_line_test_base_change to obtain
the local morphism equations. Only the open-immersion property remains in a separate
lemma about an arbitrary compatible map, with no line module or canonical evaluation.

Four remaining steps have public theorem statements in separate modules, each with
its source, a full proof in words, and a matching new node. None restates the item:
two concern affine presentations/comparisons only; one concerns arbitrary maps and
open-immersion descent only; one concerns restriction of a cartesian line presentation
only. The proof combines them with the existing section-algebra and Proj-map theorems.

## Proved and sorry left

Original hole removed: AlgebraicGeometry.AlgebraicSpace.section_proj_etale_embedding
(lem-trf-section-proj-etale-embedding). The item has zero textual sorry. Its proof is a
decomposition, not a complete proof independent of the four new steps. Holes closed: 1;
holes added: 4; net change: -3. Existing dependency holes are used as intended by stage 3.

The new theorem AlgebraicGeometry.AlgebraicSpace.space_line_proj_etale_descent is proved,
including descent of the full generation locus and the local canonical-map equations.
Its remaining open-immersion input is the third theorem below. All private helpers in
the delivery are proved; there are no private or anonymous holes or hollow definitions.

Every sorry added:

- AlgebraicGeometry.AlgebraicSpace.section_proj_model_presentation, node
  lem-trf-section-proj-model-presentation, in SectionProjModelPresentation.
- AlgebraicGeometry.AlgebraicSpace.section_proj_model_comparison, node
  lem-trf-section-proj-model-comparison, in SectionProjModelComparison.
- AlgebraicGeometry.AlgebraicSpace.space_map_open_proj_base_change, node
  lem-trf-space-map-open-proj-base-change, in SpaceMapOpenProjBaseChange.
- AlgebraicGeometry.AlgebraicSpace.etaleLinePresentation_schemeRestriction, node
  lem-trf-etale-line-presentation-scheme-restriction, in
  EtaleLinePresentationSchemeRestriction.

Edge cases were checked in the statements and proof plans: the cover index type may
be empty or live in an arbitrary larger universe; no point or cover member is chosen
globally. Empty tests and opens use their unique section maps. Degree zero is retained
with its base-ring unit and is not identified with the base ring. No finite generation
or degree-one generation is assumed. The comparison theorem applies to arbitrary local
presentations, not only the one returned by the section-algebra existence theorem.

Validation: all seven delivery modules compiled on the server through lcompile.py.
Final changed proof modules: SpaceLineProjEtaleDescent 16.9 seconds and
SectionProjEtaleEmbedding 14.9 seconds, exit 0. The other five modules compiled in
11.3-13.7 seconds each. No file exceeds the 60-second limit. Source checks confirm the
main theorem signature and the relocated structure are byte-identical to the originals,
all Lean lines are at most 100 characters, and exactly four public named theorem holes
remain. There are no current direct importers requiring adaptation. No local Lake
invocation or full-library build was run.

## No longer needed

Removed direct imports from the item:

- Sheaf.TraceFormula.GradedEvaluationZariskiEtaleComparison.
- Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers.
- Sheaf.AlgebraicGeometry.SpaceOpenImmersionEtaleLocal.
- The public Sheaf.TraceFormula.SpaceLineModuleProjMap import. The statement uses the
  input types already exported by SectionProjModel; the proved descent module imports
  the canonical-map theorem privately.

The original SpaceSectionAlgebraEtaleBaseChange public import is replaced by the public
SectionProjModel import, which itself publicly imports that same section-algebra API.
The section-algebra dependency is still used.

The parent proof no longer directly needs lem-trf-graded-evaluation-zariski-etale-comparison
or lem-trf-graded-pushforward-etale-restriction: the supplied SpaceSectionAlgebra already
specifies homogeneous products, units, normalized evaluations, their cartesian behavior,
and the sections universal property. The normalized base-change theorem already supplies
the comparison to a local section algebra. The new model-comparison step transports this
to the local model in the theorem's actual binders.

The existing relative-Proj existence/affine-restriction, fibre-product cover and
open-immersion locality nodes are still needed below the new adapter/descent steps;
their removal as direct imports is not a claim that they can be withdrawn. In particular
lemma-nagata-relative-proj-exists remains an approved transitive tool. No module or node
is withdrawn. The blueprint unit's realized arrays are empty, and its route is preserved.

## Where the brief, the DAG or earlier work was wrong

The first delivery preflight found a new-node metadata mismatch: the definition node
recorded the entire SectionProjModel body as its lean.statement. It is corrected to
the structure header, as required by the signature scanner. No Lean change was needed.

No false statement or changed mathematical hypothesis was found. A source-only graph
check encountered the pre-existing cycle between lemma-nagata-relative-proj-exists,
lem-nagata-proj-affine-restriction, lem-nagata-affine-proj-scalar-extension and
prop-nagata-relative-proj-functoriality. Those nodes are unchanged. A separate reachability
check found no cycle containing any node changed or added by this delivery. No rework/return entry
for this item was present, and the source existed at the assigned path.

The original five-step DAG is a mathematical plan, but its named Lean interfaces do not
supply all its adapter glue. In particular the section-algebra theorem returns some local
section algebra, while the item quantifies over arbitrary local presentations. Its universal
property must be used to compare those presentations and to normalize the affine coefficient
maps. The plan also does not expose a theorem identifying an etale line presentation with
the concrete schemeRestriction functor. Those are now separate recorded steps.

The existing isOpenImmersion_of_etale_cover takes an index in Type u, while this item's
cover index is in Type v. The remaining arbitrary-map descent lemma records the required
small affine refinement rather than strengthening the item's universe hypothesis. The
proved generation descent itself works directly with the original arbitrary index type.

## New nodes

- def-trf-section-proj-model: owns the existing, unchanged adapter structure after its
  relocation. It has no sorry and introduces no additional hypothesis.
- lem-trf-section-proj-model-presentation: affine-basis presentation of one already
  specified section algebra. Source: Stacks 01LH and the section algebra in 0D3C.
- lem-trf-section-proj-model-comparison: transports a normalized base-change comparison
  to arbitrary local presentations. Source: 03LX, 01LH and the evaluation sentence in 0D3C.
- lem-trf-space-map-open-proj-base-change: open-immersion descent for an arbitrary map
  compatible with the source and Proj Cartesian squares. Source: 0D3C and 03M4.
- lem-trf-space-line-proj-etale-descent: the proved combination of generation-open descent,
  canonical test-map comparison and the preceding arbitrary-map descent input.
- lem-trf-etale-line-presentation-scheme-restriction: identifies a coherent cartesian
  realization on an etale test with the actual Zariski restriction. Source: 03G7, 03DX, 03FH.

Change record: coord/changes/T1-section-proj-model-location.md. The presentation proof uses
lem-nagata-proj-affine-restriction as its affine-data tool; the restriction proof uses the
existing new-etale-tensor-open-section-iso and new-etale-tensor-open-section-naturality
nodes as generic tensor/open-section tools. These do not bypass any unit route. Searches
used Lean Finder, LeanSearch, Loogle and source grep, with results in each new node.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
