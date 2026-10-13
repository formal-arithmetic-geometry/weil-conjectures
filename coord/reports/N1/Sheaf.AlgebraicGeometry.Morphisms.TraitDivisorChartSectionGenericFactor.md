## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.GaloisCover.trait_divisor_chart_section_generic_factor` without changing its signature or public imports. It now obtains an unramified trait lift, constructs `FractionRing A` and the uniformizer unit explicitly, base changes the supplied product root chart, and composes its factor inclusion with the generic normalization comparison.

Added three modules, each with one theorem and one node:

- `Sheaf.AlgebraicGeometry.Morphisms.EtaleTraitSectionLift`: the general pointed etale trait-lift statement. Its witnesses include the ring maps and the coefficient and scheme-map compatibilities needed downstream.
- `Sheaf.AlgebraicGeometry.Morphisms.RootProductChartBaseChangeFactor`: proved using `AdjoinRoot.tensorAlgEquiv`, `AdjoinRoot.mapAlgEquiv`, `Algebra.TensorProduct.piRight`, the affine pullback isomorphism, and the open immersion of a finite-product factor.
- `Sheaf.AlgebraicGeometry.Morphisms.TraitNormalizationGenericSectionComparison`: proved by extending the injective trait map to `S.functionField` and pasting the supplied pullback squares with `Hom.pullbackFromNormalizationIso`.

All four modules compile through lcompile.py. The target's DAG proof now records these three components. No definitions, existing signatures, or visibility were changed, and no adaptations are needed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.GaloisCover.trait_divisor_chart_section_generic_factor` (node `lem-sbc-trait-divisor-chart-section-generic-factor`). The target module contains no remaining sorry.

Proved the new declarations `AlgebraicGeometry.Scheme.rootProductChart_baseChange_factor` (node `lem-sbc-root-product-chart-base-change-factor`) and `AlgebraicGeometry.Scheme.GaloisCover.trait_normalization_generic_section_comparison` (node `lem-sbc-trait-normalization-generic-section-comparison`).

Added exactly one hole: `AlgebraicGeometry.Scheme.etale_trait_section_lift` (node `lem-sbc-etale-trait-section-lift`). This statement contains no normalization, Galois cover, generic fibre, product chart, or root factor: it supplies just a local unramified DVR extension and its commuting maps. This is a decomposition with one upper hole closed and one strictly smaller hole added, net zero holes; the two remaining components are fully proved. The target still depends on this named hole.

The remaining lemma is sourced to Stacks 0EYI and 0AP2. Its docstring gives the full local-ring argument. Edge cases were checked: the point over the trait's closed point excludes a field localization, and no rational point over the base residue field is required. In the root-factor theorem an empty index set has no k, and its algebraic proof works even for zero exponents; positivity is unnecessary for that intermediate statement. All existential data are used inside proofs; the fraction field and unit are explicit constructions.

## No longer needed

No existing proof import was present to remove. The second reader removed the unused
`Mathlib.RingTheory.AdjoinRoot` public import from the new generic-comparison module
and the redundant proof import `Mathlib.AlgebraicGeometry.Limits` from the new
root-factor module; no existing library module is pruned. No existing nodes or modules are claimed as pruned. The target imports exactly its three new proof dependencies; all original public imports remain as required by the existing signature.

The generic comparison avoids the plan's appeal to smooth ascent of normality and a new localization-of-normalization theorem: normalization over the open finite model already has a proved comparison in `WeilConjectures.AlgebraicGeometry.FundamentalGroup.ExtendOverInertia`. No extra modules for those arguments were introduced. The unit's trait/section route is retained.

## Where the brief, the DAG or earlier work was wrong

No existing statement was changed or disputed. The node had a single non-elementary proof paragraph and no proof dependencies. The delivery exposes its trait-lift component and proves the two generic-chart components. The final proof needs a compatible chart-to-DVR map; mere existence of a DVR with a uniformizer would not suffice, so the new trait-lift statement explicitly includes both maps and both compatibilities.

## New nodes

`lem-sbc-etale-trait-section-lift` in `EtaleTraitSectionLift.lean` is the remaining pointed etale trait-local-ring construction from 0EYI and 0AP2. It is strictly the local trait part of the argument, with no generic-cover conclusion.

`lem-sbc-root-product-chart-base-change-factor` in `RootProductChartBaseChangeFactor.lean` is the proved affine product/root base-change argument and projection identity. It is independent of the scheme's normality and the Galois-cover setup.

`lem-sbc-trait-normalization-generic-section-comparison` in `TraitNormalizationGenericSectionComparison.lean` is the proved comparison of two generic section pullbacks. It is independent of the root chart and its exponents, and uses the proved normalization-over-open isomorphism.

No change record is needed: all existing signatures and public imports are preserved; the new statements live in new modules, imported only for the target's proof.

## Second reading by N1

1. Compared the sole existing delivered module with the repository using `diff`
   and the declaration parser: its entire theorem signature is byte-for-byte
   unchanged, as are all existing public imports and visibility. There are no
   definitions, adaptations, or statement changes. Verdict: pass.
2. Read all four complete modules. The target combines the trait lift with an
   explicit fraction field and uniformizer unit, then composes the root factor
   with the generic comparison. The root-factor proof uses the tensor and
   polynomial quotient equivalences, the product projection, and pullback
   pasting; the comparison uses the injective fraction-field lift and the proved
   `Hom.pullbackFromNormalizationIso` from ExtendOverInertia. No arbitrary
   existential witness defines public data. Exactly one `sorry` remains, in
   `AlgebraicGeometry.Scheme.etale_trait_section_lift`; no forbidden declarations
   occur. Local compilation and axiom checks are recorded below. Verdict: pass
   subject to that explicitly reported remaining hole.
3. Read Stacks Tags 0EYI and 0AP2 at
   https://stacks.math.columbia.edu/tag/0EYI and
   https://stacks.math.columbia.edu/tag/0AP2. The remaining trait-lift theorem is
   strictly the pointed local construction, with no cover or generic root-factor
   conclusion. Base change of the etale chart is etale over the trait; the
   compatible points have a point in their fibre product. Its local ring is
   noetherian and flat over the DVR with zero-dimensional reduced local closed
   fibre, so the maximal ideal is generated by the base uniformizer. Flatness
   makes the uniformizer regular and the local map faithfully flat and injective;
   the resulting local ring is a DVR. The two maps and their compatibilities
   come from the pullback. This checks every claimed witness. In particular, a
   field localization cannot be chosen at a point above the closed point; the
   residue field may be a proper separable extension. For B=R and the identity
   chart the conclusion is realized by A=R. For an empty root-factor index set
   there is no k; zero exponents in the separate root-factor theorem cause no
   problem because tensor products preserve these quotients, including zero
   rings. Repeated leanfinder, loogle, and grep searches with different queries
   are appended to the lift's node; no direct replacement was found. Verdict:
   the remaining statement is true, needed, and strictly simpler.
4. Checked the two proved helpers from their top-level conclusions through the
   used equivalences. They use existing proved algebra and normalization APIs
   directly. The old target node had no proof dependencies, so there are no old
   dependencies missing from `No longer needed`. Read
   `dag/units/sk-prop-input-spreading.json`: its trait and section route is kept;
   its realized statement and steps are empty in the baseline, and no unit
   realization is bypassed. Removed two unused/redundant helper imports, named
   above. Verdict: pass; no library nodes or modules claimed as pruned.
5. Checked each node against its Lean declaration, source, chapter, unit,
   blueprint ancestry, creation and lean records, and its proof steps. The
   target's three proof dependencies are exactly the three helpers applied in
   its proof. The helper nodes have no project-node proof dependencies and
   record the local-ring construction or the proved API calculations used.
   Their signatures match the Lean. Verdict: pass.

Changes by this second reader: removed the unused AdjoinRoot import in
TraitNormalizationGenericSectionComparison and the redundant Limits import in
RootProductChartBaseChangeFactor; appended fresh trait-lift searches to its node;
clarified the pruning report and added this independent reading. No proof,
statement, definition, or remaining-hole changes were necessary.

Validation: all four final modules compiled without warnings in the successful
`deliver3.py --no-push` run, which printed OK and passed preflight and its axiom
probes. Explicit `#print axioms` scratch checks show only propext,
Classical.choice, and Quot.sound for rootProductChart_baseChange_factor and
trait_normalization_generic_section_comparison; etale_trait_section_lift and
the target additionally show sorryAx, exactly as expected from the reported
remaining hole. One intermediate recompile timed out during high machine load;
the unchanged edited module subsequently passed both the scratch check and
successful dry run. Scratch sources were removed before delivery.
