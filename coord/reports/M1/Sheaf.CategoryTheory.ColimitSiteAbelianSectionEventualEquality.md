## What changed

The signature of `CategoryTheory.colimit_site_abelian_section_eventual_equality` is unchanged.
Its proof now reduces arbitrary inverse-image sections to a source-stage section `x - y`.
The fully proved private lemma `comparison_kernel_iff` uses the composite adjunction,
`Adjunction.leftAdjointUniq`, its unit equation, injectivity of the hom equivalence, and
componentwise cancellation of an isomorphism. It identifies the kernel of each supplied
comparison with that of the corresponding adjunction unit. The first application converts
`hxy` to unit vanishing in the sheaf at `t.right`; the second application converts later
unit vanishing back to the required equality under `θ`. The proof explicitly constructs
`t' = Under.mk (t.hom ≫ d)` and `b = Under.homMk d`.

Added the proof-only imports `Mathlib.CategoryTheory.Adjunction.Unique` and
`Sheaf.CategoryTheory.ColimitSiteFiniteUnitZeroDetection`. The latter is a new module
containing only the source-unit zero-detection step with the finite covering axioms actually
available here. Updated the item's DAG route to this proof. No definition, existing
statement, public import, or downstream module was changed.

## Proved and sorry left

Closed the item's one hole:
`CategoryTheory.colimit_site_abelian_section_eventual_equality`
(node `lem-weil-pbc-colimit-site-abelian-section-eventual-equality`).
Its comparison-map and reindexing argument is complete Lean, with no internal `sorry`.

Added one named hole:
`CategoryTheory.colimit_site_finite_unit_zero_detection`
(node `lem-weil-pbc-colimit-site-finite-unit-zero-detection`, module
`Sheaf.CategoryTheory.ColimitSiteFiniteUnitZeroDetection`). This is a decomposition,
not a complete proof of the mathematical eventual-equality theorem: one upper hole is
closed and one lower hole added, for net zero holes. The lower statement is the
source-section/identity-presentation part of the argument. It has no `α`, `θ`, unit
compatibility equations for comparison maps, `Under` object, or section in an already
pulled-back sheaf. The two comparison-kernel arguments, subtraction, and construction of
the required refinement are proved in the assigned module, not moved into the new hole.

Both sandbox modules compile together through `lcompile.py --all`, without errors or
warnings. No arbitrary object is chosen in a definition. Edge cases checked for the new
statement: zero source sheaf and zero section (identity transition suffices), empty source
stage (no object X), singleton indexing category (the cocone leg is an equivalence), and
empty covers (the presentation sheaf has zero sections on such an object).

## No longer needed

No existing import or globally reachable module is pruned. The original statement imports
are retained: an attempted removal of `Mathlib.Algebra.Category.Grp.FilteredColimits`
failed because it supplies `HasWeakSheafify` needed by the theorem signatures, so it was
restored.

The nodes `lem-weil-pbc-filtered-colimit-sets-elementwise`,
`lem-weil-pbc-filtered-colimits-commute-finite-limits`, and
`lem-weil-pbc-initial-functor-cofiltered-criterion` are no longer direct proof dependencies
of the assigned theorem. They remain needed by the new source-unit lemma; this is moving
those dependencies to the precise remaining step, not global pruning. Likewise the
presentation-presheaf/sheaf argument is no longer performed for arbitrary supplied `α`
and `θ` in the assigned theorem. No abelian-section diagram, universality, representatives,
or set-section presentation module is imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was established. The original plan is sufficient in principle but
rebuilds a presentation formula for supplied comparison maps. Adjunction uniqueness proves
that compatibility argument independently of all filteredness and covering hypotheses,
leaving only detection of a source section.

The existing `CategoryTheory.colimitSite_unit_zero_detection` is related but not applicable:
it requires unrestricted indexed covering composition/base change, finite-limit preservation
of set inverse images for every transition and cocone leg, and additional finite-colimit
instances. The assigned theorem supplies finite indexed covering axioms and continuity,
not those finite-limit assumptions. The set-section eventual-equality theorem also requires
finite-limit preservation of transition inverse images. Neither was imported or applied
with missing hypotheses, and neither was adapted without authorization.

The new statement is therefore a source-unit variant under the current finite hypotheses,
not a renamed copy of the assigned comparison-map statement. Its docstring contains the
presentation, finite-cover sheaf equalizer, adjunct identification and identity-representative
argument. Sources read: Stacks Tags 0A35 and 03CO on the official Stacks site; the named local
TeX files are absent on this machine. Mathlib searches were performed by LeanFinder, Loogle
and grep; LeanSearch was attempted and reported an Internal Server Error. Library and DAG
search found the stronger unit-zero theorem above, but no applicable finite-axiom variant.

The unit `sk-thm-p1` has been read: the assigned node is not one of its `realized` statement
or step nodes. All changes stay below that unit; its route is unchanged.

## New nodes

`lem-weil-pbc-colimit-site-finite-unit-zero-detection` records vanishing of a source section
under the colimit-site inverse-image unit being detected by a later transition unit. It is
stated in `lean/Sheaf/CategoryTheory/ColimitSiteFiniteUnitZeroDetection.lean`. It inherits
chapter `sec-proper-base-change` and unit `sk-thm-p1`, with the source formula, full proof
steps, existing dependency nodes, search records, and verbatim Lean signature. There is no
change record because no existing interface is changed.

## Second reading by M1

1. Compared the delivered eventual-equality module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports, private proof code, and the proof DAG route changed. The new source-unit module and node are additional split-off material with matching signatures.

2. Compiled both sandbox modules with `lcompile.py --all`; both compile without errors or warnings. The target proof has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The only remaining `sorry` is the named public theorem `colimit_site_finite_unit_zero_detection`, documented and represented by its DAG node.

3. Checked the split-off theorem against its hypotheses and edge cases recorded above. It is strictly weaker than the target: it concerns one source section and canonical units, with no supplied comparison maps or eventual equality conclusion. Searches found no existing declaration with this statement.

4. Read the proof top-down. The private kernel comparison uses the composite adjunction and cancellation of an isomorphism; the target then invokes only the source-unit criterion and additive cancellation. The imports retained by the proof are needed, and the three former direct dependencies remain below the new source-unit node. No hollow definition or arbitrary witness was introduced.

5. The target node proof steps and `proof_deps` match the Lean route, and the new node records its theorem, source, proof steps, dependencies, and unit `sk-thm-p1`. The unit route is preserved: the source-unit theorem realizes the presentation and identity-representative step while the assigned theorem realizes the comparison and refinement steps.

Changed during second reading: appended this review section only; no Lean code or statements required repair.
