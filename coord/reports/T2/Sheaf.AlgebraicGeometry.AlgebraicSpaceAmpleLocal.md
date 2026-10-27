## What changed

Replaced the single hole in `AlgebraicGeometry.AlgebraicSpace.representable_and_ample_of_etale_cover`
by an explicit assembly of the existing arbitrary-test line preparation and section-Proj embedding.
The original theorem signature and both public imports are unchanged.

The proof converts literal open restriction to tensor pullback using the existing natural
isomorphism and `isAmple_iff_of_iso`, obtains the prepared fibre product on every scheme test,
chooses local canonical models, and applies `section_proj_etale_embedding`. Yoneda preimage
supplies the scheme projection; `IsPullback.of_iso'` transports the actual cartesian square.
For etale tests it uses the preparation's specified line-module comparison and the reverse
ordinary-ampleness adapter.

Added three modules: `Sheaf.AlgebraicGeometry.EtalePointCoverFppfLifting`,
`Sheaf.TraceFormula.AmpleChartSectionProjModel`, and
`Sheaf.TraceFormula.SectionProjEmbeddingOrdinaryAmple`.
Validation: `lcompile.py --all` compiled all four delivered modules without errors or
warnings: cover equivalence 4.1 s, forward adapter 14.3 s, reverse adapter 13.9 s,
and item 17.8 s. The original theorem signature is byte-identical to the shared source.

The first proves the cover-interface equivalence directly from scheme residue-field tests
and the existing fppf-cover point lemma. The other two isolate forward and reverse
ordinary/etale canonical-Proj comparisons. No other existing Lean module changes.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.AlgebraicSpace.representable_and_ample_of_etale_cover`
(node `lem-trf-algebraic-space-ample-local`). No sorry remains in the item.

Also proved the new theorem
`AlgebraicGeometry.AlgebraicSpace.isJointlySurjective_iff_fppf_lifting`
(node `lem-trf-etale-point-cover-fppf-lifting`).

Added exactly two holes, each in its own public theorem and module:

- `AlgebraicGeometry.AlgebraicSpace.exists_sectionProjModel_of_ample_chart`
  (`lem-trf-ample-chart-section-proj-model`). This is only the forward canonical-Proj
  comparison on a single scheme chart, without any descent conclusion.
- `AlgebraicGeometry.AlgebraicSpace.ordinary_ample_of_sectionProj_embedding`
  (`lem-trf-section-proj-embedding-ordinary-ample`). This is the reverse comparison,
  assuming a global canonical open embedding and a specified representing scheme,
  without any cover or local-ampleness hypothesis.

This is a decomposition: one original hole closed, two lower holes added. It is not a
net sorry reduction. The item also uses the already stated preparation and embedding
results; their existing holes are unchanged. Each added hole has a source, a full proof
in words, a DAG node, and a signature strictly describing one part of the original argument.

## No longer needed

Removed the following direct proof imports from the item:

- `WeilConjectures.AlgebraicGeometry.TensorPullback`
- `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Universal`
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceInvertibleDescent`
- `Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion`
- `Sheaf.AlgebraicGeometry.SchemeRelativeAmpleBaseChange`
- `Sheaf.AlgebraicGeometry.SpaceOpenImmersionEtaleLocal`
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`
- `Sheaf.TraceFormula.SpaceLineModuleProjMap`
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`
- `Sheaf.TraceFormula.SpaceSectionAlgebraEtaleBaseChange`

These modules are still used through the preparation, embedding, or the planned comparison
steps, so no global mathematical branch is claimed pruned and no module is withdrawn.
The parent's direct quasi-separatedness, properness, and canonical-Proj-criterion dependency
entries are replaced by the adapter nodes, which retain the required mathematics.

Removed the parent's obsolete direct tool-use entries `lemma-nagata-relative-proj-exists`,
`lem-weil-pbc-etale-covering-base-change`, and `lem-weil-pbc-invertible-pullback-tensor`.
The preparation and embedding still carry those constructions below the parent.

## Where the brief, the DAG or earlier work was wrong

The original module imported the older unsplit proof dependencies. The current node instead
uses the preparation and embedding modules under `Sheaf.TraceFormula`; the Lean proof now
uses those actual declarations.

The preparation's covering hypothesis uses field-extension point lifting, while the item's
hypothesis uses a covering sieve. The embedding requires local lifting in the ordinary
scheme fppf topology. The proved cover-interface equivalence and the private
`scheme_cover_lifting` helper supply these conversions rather than identifying the
predicates by definitional equality. The helper uses the existing `schemeSpace` construction
from `EnlargedEtaleRingedSite` to apply the equivalence to a scheme base; this is an
additional private proof import and a recorded dependency on
`lem-trf-space-enlarged-etale-ringed-site-model`, used solely for the representable scheme
sheaf construction, not its enlarged-site comparison theorem.

The original ample hypothesis uses `restrictFunctor`, while preparation uses `tensorPullback`.
These are naturally isomorphic, rather than definitionally equal. Their existing comparison
and ampleness invariance supply the conversion. The remaining SectionProjModel adapters are
not direct applications of the ordinary scheme criterion: their homogeneous sections and
canonical evaluations must be transported across the normalized ordinary/etale comparisons.

Edge cases checked: empty chart and test schemes; empty index; unrestricted cover-index
universe; degree zero and arbitrary positive degrees; no degree-one generation assumption;
no assumption that the base is affine, quasi-compact or separated. The unit's recorded route
is not bypassed. A read-only DAG audit found an already existing cycle
`prop-nagata-relative-proj-functoriality` / `lem-nagata-affine-proj-scalar-extension`
below the shared Proj dependencies. This packet does not edit those nodes; no cycle
passes through any added or changed node.

## New nodes

`lem-trf-etale-point-cover-fppf-lifting` records the proved equivalence between the two
covering interfaces, using representable etale base changes and residue-field points.
Its statement includes every arbitrary scheme test, including empty tests.

`lem-trf-ample-chart-section-proj-model` records the single-chart forward adapter from
ordinary relative ampleness and its ordinary/etale identification to an actual section model
with everywhere generation and open canonical map. Its proof follows 01VJ (1) implies (5)
and the canonical section/evaluation comparisons. One hole remains.

`lem-trf-section-proj-embedding-ordinary-ample` records the reverse adapter on an existing
representing scheme. Its proof follows 01VJ (5) implies (1), followed by the specified etale
pullback and Zariski restriction comparisons. One hole remains.

No change record is needed: no existing statement, definition, visibility, public import,
attribute or instance changes. The existing node's proof, proof_deps and proof_origin follow
the Lean assembly; its obsolete direct tool-use entries are withdrawn.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
