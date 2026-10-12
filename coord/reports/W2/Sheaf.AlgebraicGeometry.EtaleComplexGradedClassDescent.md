## What changed

Replaced the sorry in `AlgebraicGeometry.Etale.exists_etale_complex_graded_class_rep`
with a complete Lean proof, preserving its signature and its two public imports.
The proof applies the existing `CategoryTheory.spectral_sequence_finite_page_comparison`
to a page-one comparison, forms the finite-page cocone explicitly, uses its isomorphism
and Mathlib filtered-colimit representatives to choose a stage, lifts through the stage
quotient, and uses the kernel equation to prove that the difference is in the next step.

The geometric construction is split into the new module
`Sheaf.AlgebraicGeometry.EtaleComplexFirstPageAbutment`. Its theorem supplies a directed
spectral diagram, comparison on page one, and compatible stage/target abutment quotient
models on common finite pages. It does **not** assert a comparison isomorphism on these
finite pages or a stage representative for a target class. Those assertions are obtained
in the original module using the existing finite-page theorem and a genuine lifting proof.
The new statement is therefore a proper construction part of the argument, rather than
renaming the original graded-lifting conclusion.

The main node now records these actual dependencies. The new construction follows the
same Stacks 0EZM/015J spectral-sequence route. Its coordinate order is
(resolution degree, complex degree), matching the existing finite-page tool's shape
(1-r,r). The graded term in degree p at step a+n is (p-a-n,a+n).

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.Etale.exists_etale_complex_graded_class_rep`
(node `lem-weil-pbc-etale-complex-graded-class-descent`). No sorry remains in the item.

Added one hole: `AlgebraicGeometry.Etale.exists_etale_complex_first_page_and_abutment`
(node `lem-weil-pbc-etale-complex-first-page-abutment`), in its own new module. Its entire
proof is `by sorry`; its docstring and node describe the construction step by step.
This delivery is a decomposition, not a claim of an unconditional sorry-free proof.

The existing `CategoryTheory.spectral_sequence_finite_page_comparison` is used as the
intended stage-3 dependency and remains sorry in its existing module. It is not added or
modified by this delivery. Existing holes below the construction are likewise unchanged.

Both delivery modules compile locally without warnings. The main proof uses no axioms
other than standard Lean axioms and the expected sorry dependencies. Final mechanical
validation is the deliver3.py --no-push dry run.

Edge cases checked mathematically: p<a gives N=0 and a zero abutment, so both filtration
bounds occur at S 0 and there is no lifting clause; p=a gives one graded piece; n=N-1
uses the zero terminal step; a zero stage diagram has zero page-one and all later pages.
Cofilteredness excludes an empty original category, and the selected directed index is
explicitly nonempty. The universe enlargement of the directed index is necessary to use
the existing finite-page theorem with AddCommGrpCat.{u+1}; it does not change the schemes'
universe or the original signature. Antitonicity makes the subgroup difference well typed.

## No longer needed

Removed direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes`.
- `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`.
- `Sheaf.CategoryTheory.HypercohomologyFirstPage`.
- `Sheaf.CategoryTheory.KInjectiveBridge`.
- `Sheaf.CategoryTheory.ExistsDirectedReindexing`.
- `Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial`.
- `Mathlib.Algebra.Category.Grp.AB`, replaced by the narrower `FilteredColimits` module.

The geometric dependencies remain needed in the new construction's subtree; some are
imported directly there and others through pullback functoriality. Thus these removals
prune the item's direct imports, but do not justify claiming that any geometric module
or node is globally unreachable. No unit statement or realized unit step is bypassed.
No whole module is claimed pruned from the targets' closure.

All nine old direct `proof_deps` are replaced in the main node:
`def-sp-etale-dictionary`, `def-sp-kinjective-bridge`,
`def-weil-pbc-etale-cohomology`, `lem-weil-pbc-filtered-colimit-abelian-groups-exact`,
`lem-weil-pbc-etale-cohomology-limit-of-schemes`,
`lem-weil-pbc-filtered-category-directed-cofinal`,
`lem-weil-pbc-hypercohomology-e1-pullback-functorial`, `thm-sp-if-e1`, and
`thm-sp-spectral-object-yields`. They are no longer direct dependencies of the lifting
proof. The construction still uses continuity, directed reindexing, first-page/convergence,
K-injective and derived-cohomology identifications, and pullback functoriality; filtered
exactness is used by the finite-page comparison. The dictionary identification is provided
by the existing termwise presentation. This is dependency factoring, not global pruning.


## Where the brief, the DAG or earlier work was wrong

No mathematical error in the original statement was found. The existing generic
finite-page comparison tool has the reverse coordinate order and requires a directed
preorder at the same universe as the abelian groups. The new construction explicitly
swaps the coordinates and raises the cofinal index to fit these requirements.
The original proof plan's filtered-colimit page induction is already isolated as
`lem-weil-pbc-spectral-sequence-finite-page-comparison`; using it avoids duplicating that
argument. The missing part is assembling compatible first-page and abutment models from
the existing étale presentations, not proving the generic page induction in this module.

LeanSearch returned an internal server error and is recorded as unavailable. LeanFinder,
Loogle, Mathlib grep and repository/blueprint searches were performed. No duplicate of
the new construction was found. Stacks' lemma-colimit-variant-complexes source was read
from an existing fetched etale-cohomology.tex; it explicitly omits finite-comparison
details, which the node and Lean lifting proof make explicit.

## New nodes

`lem-weil-pbc-etale-complex-first-page-abutment`:
`dag/nodes/sec-curve-estimates/lem-weil-pbc-etale-complex-first-page-abutment.json`, realized
by `Sheaf.AlgebraicGeometry.EtaleComplexFirstPageAbutment`. It isolates the geometric
first-page continuity and compatible abutment quotient models before any page-r colimit
comparison or representative choice. It inherits the item's chapter/unit and blueprint
ancestor and carries the executed searches, source, signature, and full construction plan.
There are no changed existing statements/definitions and no change records.

## Second reading by W2

1. **Signatures and visible data: pass.** Read the full two modules and diffed the original
   module against the repository. The only differences are proof imports and the body of
   `AlgebraicGeometry.Etale.exists_etale_complex_graded_class_rep`. Its complete signature,
   existing docstring, public imports and conclusion are byte-for-byte unchanged. There
   are no existing definition changes or change records. The new module states a theorem
   and introduces no definitions.

2. **Lean proof and axioms: pass, with the declared construction hole.** Both modules
   compile through lcompile.py in import order with no errors or warnings. Scratch-copy
   `#print axioms` checks for both delivered declarations report precisely `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is expected from the new
   construction and existing finite-page comparison. The main proof has no sorry; the
   new theorem's entire body is `by sorry`, matching the report. Checked for axioms,
   unsafe/opaque declarations, extern/implemented_by, and kernel-check bypasses: none.
   The cocone naturality follows from hv; its canonical descent map satisfies hψ.
   The finite-page theorem supplies IsIso ψ. Surjectivity, Concrete.colimit_exists_rep,
   and ht successively choose z, j/w, and a subgroup element y. hcompat places its image
   in S n. Applying hker to the subgroup difference and rewriting its q-image closes
   exactly the original conclusion.

3. **Split construction: pass after clarifying the universe order.** Read Stacks
   etale-cohomology.tex, lemma-colimit-variant-complexes (0EZM), and derived.tex,
   lemma-two-ss-complex-functor (015J), including the functorial paragraph (015K).
   Also read homology.tex, lemma-spectral-sequence-filtered-complex-functorial and
   its induced-cohomology-filtration formula. Matched qcqs, affine transitions,
   common lower bound, unital/composite transitions, the degreewise colimit, and
   canonical derived maps against the new theorem. Read the actual statements of
   exists_directed_reindexing, nonempty_isColimit_etale_cohomology_of_isLimit,
   exists_hypercohomology_firstPage, the termwise presentation and
   exists_etaleHypercohomology_pullback_functorial. They supply, respectively,
   one common reindexing, termwise continuity, the pages and derived identification,
   and filtered/graded naturality with identity/composition laws. The construction
   does not assert later-page comparison or lift any target class from a stage.
   The finite-page comparison and representative lifting remain separate, substantive
   arguments in the original module. This is a proper decomposition with net zero
   holes closed, not a sorry-free proof of continuity.

   Checked p<a (N=0, zero degree-p abutment, vacuous models), p=a (one piece),
   n=N-1 (quotient by the terminal zero step), zero complexes, and a constant
   one-object system. At (t,s), outgoing target (t+1-r,s+r) vanishes for r>t+1;
   incoming source (t+r-1,s-r) vanishes for r>s-a. The common bound
   max(t+1,s-a)+1 is independent of the stage and persists on later pages. The
   quotient models use this stationary-page identification and natural convergence,
   rather than taking a maximum over infinitely many stage-dependent thresholds.
   Continuity must be applied on the directed index A of universe u, before the
   equivalence J=ULift A raises it to u+1. Repaired the new docstring and corresponding
   node steps to specify this order, since the continuity API fixes Scheme.{u} and
   AddCommGrpCat.{u+1} together with the smaller index.

   Independently searched with LeanFinder query "spectral sequence convergence natural
   filtration quotient bounded below hypercohomology" and Loogle query
   `"SpectralSequence", "page"`; results were generic complex/T-structure and page
   declarations, with no construction matching this lemma. Searched lean/Sheaf,
   lean/WeilConjectures and the upstream WeilConjectures tree for first-page/abutment,
   hypercohomology continuity and quotient/abutment terms. No duplicate construction
   or shorter already-proved graded descent declaration was found. This construction
   cannot be closed in a few minutes: its remaining work is assembling the geometric
   and convergence witnesses, not an elementary quotient calculation.

4. **Route and pruning: pass after completing the report.** Checked
   dag/units/sk-prop-h2.json: its realized statement and sole step are empty, so this
   change replaces no realized unit step. The 0EZM spectral-sequence route remains.
   Mathlib's epi_iff_surjective and Concrete.colimit_exists_rep already give the
   shortest representative lift after the finite-page comparison. Public imports
   describe signature types; proof dependencies are plain imports. The narrower
   FilteredColimits import supplies representatives without importing Grp.AB directly.
   Added the complete list of all nine removed old direct proof_deps under
   No longer needed, explicitly distinguishing factoring from global pruning.

5. **DAG/Lean agreement: pass.** Compared the existing-node diff: only proof,
   proof_deps and proof_origin change. Its two proof dependencies match the two
   non-Mathlib theorem applications. The elementary final step is the explicit
   three lifts and additive kernel calculation in Lean using the cited Mathlib
   APIs. The new node records the exact geometric inputs, directed index, page-one
   universal comparison, filtration bounds, common-page maps, kernel, stage
   surjectivity and compatibility clauses in the new Lean signature. Checked its
   creation/source/search/blueprint/unit/Lean fields and docstring proof. Its proof_deps
   are the union of its step citations. Corrected its reindexing/continuity steps as
   described above; no existing statement was altered.

Changes by the second reader: clarified small-index continuity before universe lifting
in the new construction's docstring and node, completed the removed-dependency inventory,
and added this independent review. The original lifting proof needed no repair.
