## What changed

Replaced the sole sorry in `AlgebraicGeometry.Scheme.exists_closed_fiber_power_series_test`
with a complete Lean proof from two separate geometric constructions and the existing
`IsLocalRing.depth_eq_add_of_flat_local` theorem. Added proof-only imports of
`SmoothClosedPointLocalSection`, `SmoothSectionPowerSeriesChart`, and `FlatLocalDepthFormula`.
The original theorem signature and public imports are unchanged.

The first construction supplies the flat local base change through the prescribed point,
including reflection of the closed fibre. The second completes a smooth section and
supplies a generic prime and a nonempty open of the original fibre specialized from its image.
The combining proof uses dense-open intersection and stability under generalization, proves
`0 < n` by identifying the zero-variable prime with the origin, propagates depth through the
flat local depth formula, and proves the away-from-closed-point clause from the commuting square.

All three sandbox modules compile together through lcompile.py, without compiler warnings.
The unit record sk-prop-input-spreading has no populated realized entries. The local computation
and completion route of its last mathematical step are preserved.

## Proved and sorry left

Closed in the original module:
`AlgebraicGeometry.Scheme.exists_closed_fiber_power_series_test`
(node lem-sbc-closed-fiber-power-series-test). No sorry remains in that module.

Added holes, each in its own new module, with its source and full proof in words:

- `AlgebraicGeometry.Scheme.exists_smooth_closed_point_local_section`
  (node lem-sbc-smooth-closed-point-local-section).
- `AlgebraicGeometry.Scheme.exists_smooth_section_power_series_chart`
  (node lem-sbc-smooth-section-power-series-chart).

This is a decomposition, not a sorry-free proof of the underlying geometry: one original
hole closed, two new holes added (net -1). Neither new theorem mentions U, density, hout,
a positive variable count, or depth. The first does not construct any power-series chart;
the second assumes the already supplied local section and does not choose the base ring.
No definition or arbitrary chosen data was added.

Edge cases checked against the sources: the first lemma allows inseparable residue extensions,
which are realized using the finite-free lift before applying the étale slice to a rational
point. Its closed fibre is a singleton because the lift has a field closed fibre and the
localized étale slice has zero-dimensional local fibre. The chart lemma allows n=0 and does
not assume L is quasi-compact. Smooth fibres are locally Noetherian; an affine neighbourhood
of the image generic point has finitely many components, so avoiding the other components
supplies its nonempty open W. In zero variables the ideal equality and bijectivity of C are
proved in Lean to identify v with the origin; positivity is deduced only in the original
lemma, using hout. The trivial ring cannot carry IsLocalRing. A field base has insufficient
depth for the original theorem, but both geometric lemmas allow it. Disconnected fibres are
allowed: only one irreducible component and a nonempty open of it are needed.

## No longer needed

None. No existing proof dependencies or imports were removed: the old node had an empty
proof_deps list. All original public imports are required by the unchanged signature.
The new proof uses exactly the three proof dependencies now recorded in the original node.
No cover, finite-extension purity, or Galois-action module is imported by this construction.

## Where the brief, the DAG or earlier work was wrong

The old node records one non-elementary step with uses=[] despite containing residue lifting,
étale slicing, completion and depth propagation. There are therefore no named geometric
inputs to import directly. This delivery makes the two geometric parts explicit rather than
moving the original statement under a new name. The general flat-local prescribed-residue-field
lemma already in Sheaf does not give a Noetherian or finite extension, so it cannot substitute
for the finite-free residue lift required here. The existing Noetherian-completion-flat node
is a Mathlib leaf; it does not identify a smooth section completion with a power-series ring.
The upstream slicing module gives an étale slice only after the residue extension becomes
separable; it does not supply the preceding finite local lift.

Read Stacks Tags 0EYB, 07NE, 057G, 05D5, and 00MB online. LeanSearch returned Internal Server
Error, recorded as unavailable. LeanFinder and grep ran successfully and found no exact
geometric construction. Loogle found C_surjective in zero variables, used in the Lean proof.
The blueprint ancestor tool prints None because the created.item chain includes module
names. The new nodes preserve the existing item's explicit nearest blueprint ancestor
sbc-thm-spreading-finite-etale-galois and add the current node to its via chain. Whole-blueprint
searches for smooth section completion and flat local residue found only unrelated definitions.

## New nodes

lem-sbc-smooth-closed-point-local-section: the finite flat residue lift followed by the localized
étale slice through the rational lift. New module
lean/Sheaf/AlgebraicGeometry/Morphisms/SmoothClosedPointLocalSection.lean.

lem-sbc-smooth-section-power-series-chart: completion along an already supplied smooth section,
including the origin, commuting square and generic-prime specialization into a nonempty
original-fibre open. New module
lean/Sheaf/AlgebraicGeometry/Morphisms/SmoothSectionPowerSeriesChart.lean.

No statement or definition changed; no change record or forced adaptation is needed.

## Second reading by G1

1. Compared the delivered original module with the repository using diff, and checked
   its theorem signature byte for byte. PASS: only three plain proof imports and the
   proof body changed; public imports, docstrings, declarations and definitions agree.
   Both other modules are new. No existing interface changed and no change record is needed.
2. Compiled all three modules in import order with lcompile.py: no errors or warnings.
   A scratch module printed axioms for all three declarations: exactly propext,
   Classical.choice, Quot.sound and sorryAx. PASS as a decomposition, not as a theorem
   free of sorry dependencies. The original module contains no sorry; each new module
   contains exactly its reported named theorem hole. There are no definitions choosing
   arbitrary witnesses, hollow definitions or forbidden declarations. Existential
   elimination occurs solely inside the proof of a proposition.
3. Independently read Stacks [0EYB](https://stacks.math.columbia.edu/tag/0EYB),
   [07NE](https://stacks.math.columbia.edu/tag/07NE),
   [057G](https://stacks.math.columbia.edu/tag/057G),
   [05D5](https://stacks.math.columbia.edu/tag/05D5), and
   [00MB](https://stacks.math.columbia.edu/tag/00MB). PASS: the section construction
   and the completion construction are true, needed and strictly partial arguments,
   rather than restatements of the original item. For an inseparable finite residue
   extension, 07NE uses a tower of monic polynomial lifts, not an unjustified primitive
   element assumption; its field closed fibre makes the finite algebra local. The
   rational lifted point meets 057G's separability hypothesis. Localization of the
   étale slice is Noetherian and has a singleton closed fibre. For the completion
   step, an open containing the section's closed point contains the whole local
   spectrum; hence the chart really has a global augmentation. Its conormal module
   is finite free over B, so 05D5 applies without requiring B to be complete. Since
   m_B is finitely generated, quotienting the series ring by its extended ideal
   gives the series domain over the residue field. On the closed fibre the resulting
   map is flat (completion base change followed by a field extension), so the
   contraction of this minimal prime is minimal. In an affine neighbourhood of its
   image, remove the finitely many other components to obtain the required nonempty
   open W; global quasi-compactness is unnecessary. The case n=0 is allowed in this
   lemma and excluded by the original proof using density and hout. Identity families,
   field bases, disconnected smooth fibres and purely inseparable closed points
   give no counterexample.

   Repeated LeanFinder searches with different queries: "finite free local ring
   extension realizing a finite residue field extension" and "smooth augmented algebra
   completion is multivariate formal power series over a local ring". Results supply
   residue finiteness and formal-smooth lifting facts, not either new statement.
   Targeted Mathlib grep for conormal freeness and completion/series equivalences
   found MvPowerSeries.toAdicCompletionAlgEquiv, which concerns the polynomial ring,
   not an arbitrary smooth augmented chart. Searched lean/Sheaf and the upstream
   geometry sources as well. Upstream Smooth.exists_etale_comp_of_etale_residueFieldMap
   gives the étale slice after separability, not the finite residue lift or the whole
   section theorem. FlatLocalExtensionGivenResidueField lacks the Noetherian control
   required here. No exact duplicate was found; neither geometric hole can be closed
   in a few minutes from the available declarations.
4. Read the proof downward and checked each of its three added imports is used.
   PASS: the dense-open intersection, specialization, zero-variable ideal calculation,
   depth inequality and commuting-square argument genuinely combine the two partial
   constructions. The original node had no proof dependencies to prune, so "No longer
   needed: None" is complete. The unit sk-prop-input-spreading has empty realized
   entries; its local section/completion route is preserved, with no unit bypass.
5. Checked all three node signatures against their Lean declarations verbatim, and
   checked proof_deps equals the union of proof-step uses. PASS: the original node's
   three dependencies match the actual applications. The new nodes have their source,
   proof in words, origin, search records, creation record, blueprint provenance,
   chapter, unit and Lean record, with distinct modules and matching docstring tags.

Changes by the second reader: appended this independent review and its search/source
checks to the report. No Lean or node repair was necessary. One original hole closed,
two holes added, net -1; no additional hole was closed during the second reading.
