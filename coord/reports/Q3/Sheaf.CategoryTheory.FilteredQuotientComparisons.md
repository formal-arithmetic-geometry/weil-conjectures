## What changed

Replaced the sorry in `CategoryTheory.filteredQuotient_comparisons_rest` with a
complete proof from the existing quotient-image and representative-epimorphism
lemmas and one new, strictly smaller map-restriction statement. Existing public
signatures are unchanged; the already proved `filteredQuotient_comparisons` stays
unchanged. Six private helpers are fully proved: `comparison_on_representatives`,
`first_page_comparison`, `normalized_homology_naturality`,
`normalized_image_naturality`, `step_restriction_square`, and `quotient_descent`.

The proof constructs both comparison isomorphisms with their representative
normalizations, proves first-page compatibility, constructs the step and quotient
maps, and proves both naturality squares by monic and epic cancellation. Its choice
of comparison maps is justified by uniqueness from the normalization equations;
no arbitrary data is selected from a mere existence assertion. Step restrictions
are unique after their monic inclusions, and quotient maps after epic projections.

Added `Sheaf.CategoryTheory.FilteredQuotientMapRestrictions`, containing only the
remaining restriction and descent step. It assumes already constructed step and
graded maps, and concludes cycle maps, boundary quotient maps, page-one maps, and
a map on unquotiented representatives. It contains no comparison isomorphism or
homology/image naturality assertion. All imports added for proofs are non-public. The new module imports only its
statement dependencies; its redundant HomologicalComplex import was removed in
second reading.

Both sandbox modules compile with `lcompile.py --all`, without warnings.

## Proved and sorry left

Closed the original hole `CategoryTheory.filteredQuotient_comparisons_rest`
(node `lem-sp-filtered-quotient-comparisons-rest`). The existing proved declaration
`CategoryTheory.filteredQuotient_comparisons` remains proved. No sorry remains in
the assigned module.

Added one hole: `CategoryTheory.filteredQuotient_map_restrictions`
(node `lem-sp-filtered-quotient-map-restrictions`), in its own new module. This is a
decomposition: one upper hole closed, one strictly smaller lower hole added, net
zero holes. The quotient comparison constructions and all comparison naturality
arguments are actual Lean proofs, not part of the new hole.

## No longer needed

Removed the direct proof import
`Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries` and the dependency
`lem-sp-filtered-complex-firstPage-cycles-boundaries` from this argument: the first
page comparison is obtained by specializing the quotient-image comparison to the
identity transition, without identifying the graded cycle and boundary subobjects.
Other target paths may still need that module; no global pruning count is claimed.

Removed the redundant direct import `Sheaf.CategoryTheory.Filtration`; its
statement definitions remain available through the unchanged public import of
`FilteredComplexSubquotients`. The filtration definition node remains needed.

Removed the earlier uncommitted `FilteredQuotientComparisonsRemainder` module and
its `lem-sp-filtered-quotient-comparisons-remainder` node: they merely renamed the
pre-existing remaining theorem and are not part of this delivery. The original
quotient-image and boundary-containment dependencies remain used, and the
representative-epis module is now used directly.

## Where the brief, the DAG or earlier work was wrong

The prior attempt closed no new hole: the boundary-containment assembly was
already proved in the repository, and its new remainder duplicated the existing
`filteredQuotient_comparisons_rest`. This delivery works on that actual remaining
hole and proves its objectwise construction and both naturality arguments.

The DAG's vague instruction to use quotient-image comparison and cokernel
cancellation concealed the cycle/boundary restriction step. The new node isolates
exactly that step, with a complete categorical proof in words from Stacks Tag 012K,
Lemma 12.24.4. Its hypotheses determine all restriction and descent maps uniquely.
Edge cases checked: zero objects and filtration steps, r=1, and arbitrary p,q
(including negative values); all inequalities derive from r >= 1, and no additional
boundedness or splitting assumption is introduced. The unit record has no realized
statement or proof step bypassed by this reduction, and no unit route is changed.

## New nodes

`lem-sp-filtered-quotient-map-restrictions` records the restriction of a filtered
morphism to the explicit cycle representatives and boundary quotients. Its Lean
statement, source, proof steps, searches, and blueprint origin are recorded in
`dag/nodes/sec-abelian-varieties/lem-sp-filtered-quotient-map-restrictions.json`.
The existing rest node's proof metadata is updated to match the actual Lean proof.
No signatures, definitions, target statements or other held modules were changed;
there are no forced adaptations or change records.

## Second reading by Q3

1. Compared the delivered module with the read-only repository using diff and
   exact substring comparisons. Both existing theorem signatures are byte for
   byte unchanged; the entire existing filteredQuotient_comparisons declaration
   is unchanged. Public imports of the existing module are unchanged. No existing
   definition or target statement changes. Verdict: pass.
2. Compiled both modules in import order with lcompile.py --all, then compiled a
   scratch copy with #print axioms for filteredQuotient_comparisons_rest,
   filteredQuotient_comparisons and filteredQuotient_map_restrictions. Each reports
   only propext, Classical.choice, Quot.sound and sorryAx. The sole delivered sorry
   is the named restriction theorem listed above; no forbidden declaration form
   or hollow definition is present. Read every helper and the main cancellation
   argument. Step maps, representative restrictions, cycle maps and quotient maps
   are uniquely determined by monic inclusion or epic projection equations.
   The normalized comparison isomorphisms are likewise uniquely determined by
   their representative equations, not arbitrary witnesses. Verdict: pass as
   a decomposition, with its documented remaining proof dependency.
3. Read the split theorem against the explicit definitions of representatives,
   cycles and boundaries and Stacks Section 12.24, displayed formulas and Lemma
   12.24.4 (https://stacks.math.columbia.edu/tag/012K). Its chain-map, pullback,
   image and cokernel argument is valid in an arbitrary abelian category. Checked
   r=1, zero filtration steps, zero complexes, identity and zero morphisms, and
   negative indices: no extra assumption is needed. The statement omits all
   comparison isomorphisms and their homology/image naturality, so is strictly
   smaller than the old hole. Its docstring gives the construction and its node
   records it. Independent leanfinder search for filtered-complex cycle and
   boundary maps found general cyclesMap results, not this restriction theorem;
   loogle found no exact project-subobject match, and rg/msearch grep across the
   library found no existing equivalent. The general Mathlib cyclesMap does not
   construct the concrete filtered cycle/boundary restrictions. Closing the
   remaining hole requires those subobject calculations, rather than a short
   direct application of an existing theorem. Verdict: pass.
4. Checked the route top down: existing quotient-image comparison and proved
   representative epimorphisms supply the normalized comparisons; the identity
   transition supplies page one without a separate cycles-boundaries lemma.
   The parent module genuinely proves both naturality assertions. All original
   rest-node proof dependencies are retained, and the report lists removed
   direct imports. The existing assembly node still uses boundary containment
   and the rest theorem. Read dag/units/sk-prop-av-pqf-finite.json: neither the
   changed node nor the removed dependency realizes a unit statement or step;
   the unit route is untouched. No whole-module pruning is claimed. Verdict: pass.
5. Compared the existing node JSON: only proof, proof_deps and proof_origin differ.
   Its three steps follow the objectwise comparisons, map constructions and
   cancellation arguments in Lean. The new node has source, complete proof steps,
   dependency union, search records, creation and blueprint provenance, chapter,
   unit and a verbatim normalized Lean statement. Verdict: pass.

Second-reading changes: removed the redundant public import of
Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex from the new restriction
module, confirmed both modules still compile, and added this review record.
No proof, statement, definition or DAG change was necessary. Holes closed: one;
holes added: one; net zero (decomposition).
