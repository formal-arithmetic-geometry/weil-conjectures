## What changed

Proved `AlgebraicGeometry.Etale.exists_cyclicDerivedHom_cohomology_comparison` from two
strictly separate obligations: bijectivity of an explicit abelian-coefficient comparison
map, and its restriction identity for cyclic coefficients. The final proof constructs an
additive equivalence by composing bijections, applies the restriction identity, uses
additivity to preserve zero, and uses injectivity to reflect zero.

Added `Sheaf.AlgebraicGeometry.CyclicDerivedHomComparisonMap`. The free representable
abbreviates the existing `AlgebraicGeometry.etaleOpenFreeSheaf`,
and its Hom equivalence reuses `EtaleOpenComparison.sectionsEquiv`. All its data is constructed:
the representable section comes from the inverse-image/direct-image adjunction unit,
pullback symmetry, localization restriction, and the constant-sheaf adjunction. Derived Hom
is converted to Ext by the fully faithful D+ inclusion, its shift comparison, and
`Ext.homAddEquiv`. The comparison then pulls back Ext and precomposes with this section.
Cyclic coefficients are converted by `Scheme.upperStarConstantSheafIso`.
There is no chosen witness of an unproved existence assertion.

Added proof-only imports of `CyclicDerivedHomComparisonBijective` and
`CyclicDerivedHomComparisonNaturality` to the assigned module. Existing signatures and
public imports stay identical. Updated the assigned DAG node to follow the actual proof.

## Proved and sorry left

Closed the assigned hole:
`AlgebraicGeometry.Etale.exists_cyclicDerivedHom_cohomology_comparison`
(node `lem-sbc-cyclic-derived-hom-cohomology-comparison`). There is no sorry in that module.

Added two holes, each in its own module:

- `AlgebraicGeometry.Etale.abelianRepresentableCohomologyMap_bijective`
  (`lem-sbc-abelian-representable-cohomology-map-bijective`): bijectivity of the explicit map
  for arbitrary abelian coefficients; no restriction/naturality assertion.
- `AlgebraicGeometry.Etale.cyclicRepresentableCohomologyMap_naturality`
  (`lem-sbc-cyclic-representable-cohomology-map-naturality`): an equality of the explicit
  comparison maps under restriction; no bijectivity/existence assertion.

This is a decomposition, not a completed proof of the mathematical comparison:
one upper hole closed and two lower holes added. All definitions in the new map module
are fully constructed and compile. The two remaining theorems carry complete proof
sketches. Edge cases checked in their arguments: e=0 means integer coefficients,
q=0 uses the ordinary adjunction, identities obey the unit equations, and empty fibre
products require no additional hypothesis.

## No longer needed

No original Lean import or library module is pruned. The following old dependencies are
removed from the assigned node's direct `proof_deps`:

- `def-weil-pbc-derived-categories`: now used by the explicit map and lower obligations.
- `def-weil-pbc-direct-image`: now used by the universal section and lower obligations.
- `def-weil-pbc-inverse-image`: now used by the explicit map and lower obligations.
- `def-weil-pbc-sheafification`: now used by the free representable and bijectivity obligation.
- `lem-weil-pbc-etale-restriction-injectives`: its recorded declarations concern module
  coefficients; the abelian bijectivity proof instead uses the exact localization
  adjunction described in `injective_upperStar_obj_of_etale_addCommGrp`.

These are not claims that the underlying infrastructure is unnecessary. No unit statement
or realized unit step is bypassed: `sk-lem-failure-field.realized` has an empty statement
list and an empty list for its sole step. In the new map module, the explicit import of
`TopologicalInvariance` is replaced by the existing `EtaleOpenCohomologyComparison`, which
already imports it and supplies the free-representable and sections constructions.

## Where the brief, the DAG or earlier work was wrong

The existing restriction-injectives node records the module-coefficient declaration,
whereas this item uses abelian sheaves. The source library also proves
`injective_upperStar_obj_of_etale_addCommGrp` in
`WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic`; this is the applicable API when
proving the bijectivity obligation by injective resolutions. The module-coefficient
free-sheaf comparison is an analogue, not an exact match for the abelian statement.

Mathlib's sheaf-cohomology file lists comparison of representable Ext with restricted
cohomology as unfinished infrastructure. LeanFinder found the definitions of Sheaf.H,
the cohomology presheaf, and resolution computations, but no comparison under restriction.
The logged grep search found no match; LeanSearch was unavailable (HTTP Internal Server
Error). Local source searches found the module-valued FreeSheaf argument, which guides the
remaining bijectivity and naturality proofs.

## New nodes

`def-sbc-abelian-representable-cohomology-map` records the explicit comparison construction,
including its free representable, universal section, D+-to-Ext conversion and cyclic
coefficient conversion; its module has no sorry.

`lem-sbc-abelian-representable-cohomology-map-bijective` records the remaining exact
extension-by-zero/derived-adjunction comparison for arbitrary abelian coefficients.

`lem-sbc-cyclic-representable-cohomology-map-naturality` records the remaining restriction
identity, including the constant-coefficient map. These obligations are independent parts
of the original plan, not renamed copies of the assigned theorem. No change record is
required: no existing statement, definition, visibility or public import changed.

## Second reading by T2

1. Interface check: diffed the assigned module against the repository. The sole existing
   theorem signature is byte for byte identical, as are its docstring and three public
   imports. Only its proof and two private-to-importers proof imports changed. The three
   other modules and nodes are new. No existing definition, target or statement changed,
   so no change record or forced adaptation is needed. Verdict: pass.
2. Proof and construction check: all four delivered modules compile without errors or
   warnings through lcompile.py, in import order, after the repairs. A scratch copy with
   `#print axioms` checks all ten declarations. All seven construction declarations use
   only propext, Classical.choice and Quot.sound. The two explicitly reported lower
   theorems and the assigned theorem additionally use sorryAx. Exactly two named theorem
   bodies are `by sorry`; none is inside data, an anonymous proof or a definition. No
   forbidden declaration or attribute occurs. AddEquiv.ofBijective chooses only the
   uniquely determined inverse of the explicit map, as permitted. Verdict: pass as a
   decomposition, not as an axiom-free proof of the comparison.
3. Lower-statement check: bijectivity has no restriction assertion; naturality has no
   bijectivity or existential assertion. They are separate parts of the old argument,
   combined by an actual injectivity proof, rather than renamed copies of the assigned
   theorem. The universal section is the identity representable generator, transported
   by the adjunction unit, pullback symmetry and localization comparison. In degree zero
   the bijection is the ordinary sections adjunction and the restriction identity is
   evaluation naturality. For e=0 the coefficients are integers; for e=1 both cyclic
   sides are zero; an empty fibre product gives zero sections and cohomology. Identity
   arrows give the unit/naturality identities. Exact extension by zero and restriction
   justify the passage to all degrees. Both statements retain sourced proof docstrings
   and matching nodes. Independent LeanFinder, Loogle and grep searches with different
   wording found generic Ext and resolution APIs, but no theorem closing either entire
   obligation. The existing open-object comparison requires an open immersion; W is
   only etale here. Verdict: both obligations are mathematically valid and needed.
4. Route and pruning check: read the source FreeSheaf argument, Mathlib's explicit TODO
   for representable cohomology over a localized site, the library's open-object
   comparison and its exact Ext adjunction. Reused the existing free-sheaf and sections
   constructions; closing either remaining obligation still requires substantial
   adjunction-unit/coherence work. The final proof takes their direct comparison route.
   The report now enumerates every old proof dependency absent from the new direct
   proof_deps. No library module is pruned. The unit sk-lem-failure-field has empty
   realized statement and step lists and its route is unchanged. Public imports in the
   new modules provide types or construction data; the added imports of the assigned
   module are proof-only. Verdict: pass after the reuse and reporting repairs.
5. DAG check: each proof_deps is exactly the union of its proof steps' uses; the assigned
   node records bijectivity, coefficient conversion, naturality and injectivity exactly
   as the Lean proof does. Only proof, proof_deps and proof_origin change on the existing
   node. New nodes have their statements, Lean records, sources, creation and blueprint
   data, and three original search kinds plus the independent reader's search record.
   Corrected the definition node's proof_origin to null and removed the inapplicable
   module-coefficient restriction lemma from the abelian bijectivity plan. Verdict:
   pass after metadata repair.

Second reading changed the new free-representable abbreviation and Hom equivalence to
reuse AlgebraicGeometry.etaleOpenFreeSheaf and EtaleOpenComparison.sectionsEquiv; replaced
one redundant direct import in the new map module; corrected the abelian bijectivity plan
and definition-node proof_origin; and completed the pruning report and search records.
The original upper proof is unchanged. No additional hole was closed or added in the
second reading: one upper hole closed, two lower holes added, net -1; decomposition.

Source check: [Stacks 03Q8](https://stacks.math.columbia.edu/tag/03Q8) describes the
restricted-cohomology presheaf and cites [Stacks 072W](https://stacks.math.columbia.edu/tag/072W),
whose injective-resolution computation supports the localization argument. The free
representable identification and its explicit unit are supplied by the library
adjunctions rather than asserted to be literal statements of those Stacks lemmas.
