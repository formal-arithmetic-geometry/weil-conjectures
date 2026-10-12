## What changed

Proved the unchanged theorem `AlgebraicGeometry.Etale.etale_limit_affine_degree_zero_kernel`
from a smaller fixed-coefficient continuity step. The original module adds proof-only imports of
`EtaleCohomologyFilteredColimit`, `EtaleCohomologyPullbackFunctorial`, and the new
`EtaleFixedAffineDegreeZeroKernel`, together with Mathlib's affine limits and concrete filtered
colimits. No definition, existing signature, or public import changes.

The private proved helper `hZeroColimit` specializes the existing filtered-cohomology theorem
at zero and transports its canonical cocone through the derived/global-section and H^0/section
isomorphisms. It does not duplicate the module-to-abelian sheaf-colimit proof. The private proved
helper `pullback_comp` specializes existing cohomology pullback functoriality to a specified
commuting triangle. The main proof detects zero in H^0(G_j), explicitly cancels the eG maps,
uses the new lemma on F_j, and combines the two stage arrows using hcomposition and naturality.
The identity hypothesis is retained unchanged; the supplied functor G already encodes its laws.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Etale.etale_limit_affine_degree_zero_kernel`
(node `lem-weil-pbc-etale-limit-affine-degree-zero-kernel`). There are no sorries left in the
assigned module, including its private helpers.

Added one hole in `AlgebraicGeometry.Etale.fixed_affine_degree_zero_kernel`
(node `lem-weil-pbc-fixed-affine-degree-zero-kernel`), in its own new module. This is a
decomposition: one original hole closed, one strictly smaller hole added, net zero.
The new theorem has a single stage sheaf and class, with no varying F, coefficient transition
maps, coherence hypotheses, pulled-back diagram G, eG, hG, or sheaf colimit L. Its conclusion
is just pullback vanishing. The filtered-colimit detection and the combination of the stage
arrows are proved in Lean, not moved into the new hole.

Both modules compiled with lcompile.py. The empty scheme and zero coefficients have zero
sections. For a singleton directed index the limit projection is an isomorphism and its
pullback detects zero. The upper tail is nonempty even if x is already zero, so the new
statement does not exclude these edge cases. No arbitrary object is chosen from an unproved
existence theorem, and no data definitions were introduced.

## No longer needed

No original imports removed and no globally pruned modules claimed. Second reading removed
the redundant added import `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic` from the
assigned module and the redundant new-module public import
`Mathlib.AlgebraicGeometry.Morphisms.Affine`. The original eight
immediate proof dependencies have been replaced in the item's node by the filtered-cohomology
colimit theorem, filtered equality detection, pullback functoriality, and the new fixed-sheaf
kernel. Affine-site presentation, affine-topos comparison, and tail cofinality remain needed
for the new geometric item; moving them down is not global pruning. Limit affineness in the
main proof is supplied directly by Mathlib `Scheme.isAffine_of_isLimit`.

For completeness, the old proof-dependency edges absent from the new immediate list are:
`lem-weil-pbc-limit-affine-transition` (replaced here by Mathlib),
`lem-weil-pbc-affine-etale-site-colimit`, `lem-weil-pbc-affine-etale-site-topos`,
`lem-weil-pbc-colimit-initial-full-subcategory`, and
`lem-weil-pbc-colimit-of-sites-sections` (geometric obligations now below the fixed-sheaf
kernel), plus `def-weil-pbc-etale-cohomology` and `def-weil-pbc-cohomology-pullback`
(still used as definitions and retained in stmt_deps, rather than claimed pruned).
`lem-weil-pbc-filtered-colimit-sets-elementwise` remains an immediate proof dependency.

## Where the brief, the DAG or earlier work was wrong

The assigned module did not import its proof dependencies, as the current machine brief
anticipated. Existing fixed-base continuity in GlobalSectionsLimitComparison and Gabber cannot
be used as a shortcut: import_direction.py rejects both because they already reach this item.
FixedPullbackDegreeZeroDescent only gives representatives, not detection of zero.

The existing ColimitSiteSections Lean signature concerns a diagram of sheaves already on
one colimit site. It does not directly expose the varying-stage comparison of Sites 09YN.
Thus the geometric transport and comparison cannot be completed by simply applying that
signature to the original coefficient system. The remaining fixed-coefficient kernel states
that geometric step explicitly, with the source proof in its docstring and node.

Blueprint ancestry lookup follows created.item as a node id and prints None for this item,
whose created.item is a module name. The new node records the actual ancestry already present
in the parent affine-eventual-zero node. Searches of the whole blueprint for fixed degree-zero
kernels and section continuity found no duplicate. The finite-stage-killing blueprint assertion
requires a henselian pair, positive degree and torsion, so it is not this degree-zero statement.
The sk-thm-p1 realized statements and steps remain untouched.

## New nodes

`lem-weil-pbc-fixed-affine-degree-zero-kernel`, module
`Sheaf.AlgebraicGeometry.EtaleFixedAffineDegreeZeroKernel`: fixed stage-sheaf degree-zero
vanishing after pullback to a later affine stage. Source: Stacks 09YQ, degree-zero argument
through 0EYL, 04HR and 09YN. LeanSearch was unavailable (HTTP 500), LeanFinder returned
structure-sheaf continuity only, and the logged Mathlib grep returned no matching declaration.
No change records or forced adaptations are needed.

## Second reading by X2

1. **Interface: pass.** Compared the assigned module by `diff -u` with the repository.
   Its sole existing theorem signature is byte for byte identical, including every
   coherence hypothesis, the specified colimit leg in hx, and the existential conclusion.
   Its existing public import and docstring are unchanged. The only additions are private
   proved helpers, proof-only imports and the proof. There are no definitions or change
   records, and no other existing Lean module is delivered.
2. **Proof and trust: pass, with the declared remaining hole.** Both modules compile
   through `lcompile.py --all`, also after import cleanup. In scratch copies, `#print axioms`
   shows exactly propext, Classical.choice and Quot.sound for hZeroColimit and pullback_comp;
   the main theorem and fixed_affine_degree_zero_kernel additionally have sorryAx.
   The only syntactic sorry is the named fixed-sheaf theorem. There are no data definitions,
   arbitrary chosen witnesses, axiom declarations, unsafe/opaque or implementation escapes.
   The main proof first detects zero in H^0(G_j), cancels eG on both sides using hG,
   uses pullback composition and coefficient naturality to obtain p_j^*(y)=0, applies
   the fixed kernel, and proves the desired result for f followed by g using hcomposition.
3. **Split-off statement: pass as a decomposition.** Read
   [09YQ](https://stacks.math.columbia.edu/tag/09YQ),
   [0EYL](https://stacks.math.columbia.edu/tag/0EYL),
   [04HR](https://stacks.math.columbia.edu/tag/04HR), and
   [09YN](https://stacks.math.columbia.edu/tag/09YN). The fixed theorem is precisely the
   equality-with-zero part of degree-zero continuity for the inverse images of one stage
   sheaf on its upper tail. Affineness supplies qcqs; transitions are affine; no torsion,
   finite generation or surjectivity hypothesis is needed. The tail is nonempty and
   directed, and its limit is the same scheme. Composition identifies all limit sheaves
   with p_i^*F; their connected constant cocone is a colimit. The source section comparison
   then gives eventual equality with zero, with the stated cohomology maps by the unit
   formula. This is strictly smaller than the varying-coefficient/colimit statement:
   that additional filtered-colimit and coherence argument is implemented in the main proof.
   Checked x=0, zero sheaves, empty stage schemes and singleton indices; in the singleton
   case the projection is an isomorphism, and x=0 always has the identity-stage witness.
   A limit that becomes empty is covered by the same finite-stage equality criterion.
   Independent LeanFinder search using inverse-system/section/vanishing wording found only
   structure-sheaf results (exists_appTop_map_eq_zero_of_isLimit and variants), which do
   not apply to arbitrary etale sheaves. A new Mathlib grep query returned no match.
   Repository searches found FixedPullbackDegreeZeroDescent (only representatives),
   GlobalSectionsLimitComparison and Gabber (downstream through this item). None supplies
   a usable shorter proof. The new theorem has its full prose argument and matching node.
4. **Route and pruning: pass after report/import repair.** hZeroColimit uses the existing
   proved filtered-cohomology theorem at zero, transported by natural isomorphisms; its
   point is the canonical cocone, not an unspecified group isomorphism. The existing
   functoriality theorem supplies the commuting-triangle calculation. The geometric hole
   cannot be closed by applying ColimitSiteSections alone: its actual signatures concern
   sheaves already on one site, and omit the varying-site inverse-image comparison.
   Read sk-thm-p1.json and its realized statement/step lists: this item is below those
   unit realizations, and none is replaced or bypassed. The unit's separately named
   literature _section.md is absent on this machine; its text is available in that record.
   The report now explicitly accounts for all seven removed immediate dependency edges;
   no globally pruned module or positive ledger net is claimed.
5. **DAG: pass.** The existing node changes only proof, proof_deps and proof_origin.
   Its three steps match filtered H^0 detection, eG cancellation, and fixed-coefficient
   vanishing followed by coefficient composition. Both node Lean signatures occur verbatim
   in their modules. The new node has the chapter/unit, statement dependencies, source,
   three search records, created/blueprint ancestry, split status and complete Lean record.
   Its planned geometric dependencies are retained below the new hole. Neither target
   statements nor unit realized records change.

Changed on second reading: removed the two redundant imports named above and completed the
immediate-dependency accounting in this report. No theorem statement, proof body or node
needed repair. One original hole is closed and one smaller hole added: net zero, decomposition.
