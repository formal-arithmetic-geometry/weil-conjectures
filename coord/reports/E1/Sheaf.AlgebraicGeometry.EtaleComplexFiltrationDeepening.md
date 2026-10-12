## What changed

Replaced the sorry in `AlgebraicGeometry.Etale.exists_etale_complex_class_in_next_filtration`
by a complete Lean reduction to two separate substeps: the functorial first/stable-page
filtration dictionary and termwise first-page continuity. The target signature and
its existing docstring are unchanged. Both new statements compile. The target compiles
without warnings in 21 seconds; the new modules compile in 31 and 46 seconds.

A private proved helper reindexes a general filtered category through Mathlib's
`AsSmall` and `IsFiltered.exists_directed`, so the existing finite-page comparison
can be applied at the universe of the abelian groups. Finality transports the page-one
hypothesis and finite-page comparison back. The target constructs the comparison cocone,
uses the resulting isomorphism to obtain a zero colimit representative, applies
Mathlib's concrete filtered-colimit equality criterion, and concludes using the
stable graded-class kernel equivalence. No class-vanishing/continuity theorem above
this item is imported, so the reduction is not circular.

The page-data module defines `complexTermCohomologyMap` explicitly (no postponed data)
to give the termwise map fixed endpoints. Existential witnesses avoid the expensive
kernel-generated declarations of an initially tested dependent structure. The intermediate
existence statement does not assume a scheme limit or affine/qcqs hypotheses: those
belong only to the independent continuity statement.

## Proved and sorry left

Decomposition, not a completed proof: closed one local hole and added two lower holes
(net local holes: -1). Reduced `AlgebraicGeometry.Etale.exists_etale_complex_class_in_next_filtration` (the
item's one sorry). Its proof has no sorry. The private `finite_comparison_filtered`
is proved from the existing `CategoryTheory.spectral_sequence_finite_page_comparison`.
That existing theorem is still sorry in the shared library and is not modified here.

The delivery leaves exactly two public named sorries:

- `AlgebraicGeometry.Etale.exists_etaleComplexFiltrationPageData`, node
  `lem-weil-pbc-etale-complex-filtration-page-data`.
- `AlgebraicGeometry.Etale.etale_complex_first_page_continuity`, node
  `lem-weil-pbc-etale-complex-first-page-continuity`.

Each has its source and full natural-language proof in its docstring. Neither restates
the target: the first constructs pages and graded representatives without comparison
injectivity; the second proves only first-page continuity, with no stable filtration
or eventual-membership conclusion. Edge cases checked: a zero class projects to zero;
negative resolution degrees require zero pages; p < q forces the q-step to be zero;
the category is nonempty by cofilteredness; q below the common bound may have zero graded
piece, which the dictionary permits. Finite-page comparison requires no abutment data.

## No longer needed

Removed direct proof imports of `Mathlib.Algebra.Homology.HomologicalComplexLimits`,
`Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes`,
`Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`,
`Sheaf.CategoryTheory.HypercohomologyFirstPage`, `Sheaf.CategoryTheory.KInjectiveBridge`,
`Sheaf.CategoryTheory.SpectralSequenceComparison`,
`Sheaf.CategoryTheory.ExistsDirectedReindexing`, and
`Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial` from the item.

`lem-weil-pbc-complex-spectral-sequence-comparison` and its module
`Sheaf.CategoryTheory.SpectralSequenceComparison` are not needed on this route:
only `lem-weil-pbc-spectral-sequence-finite-page-comparison` is used. Consequently this
proof does not require full abutment isomorphisms or finite-filtration induction.
The other removed imports are used in the plans of the two intermediate nodes and
remain imported there; they are moved dependencies, not globally pruned modules.
`def-sp-etale-dictionary` is a reading convention without a declaration and needs no
additional module. `def-weil-pbc-etale-cohomology` remains in the public statement imports.
No unit statement or realized unit step is bypassed (sk-prop-h2 has empty realization).

## Where the brief, the DAG or earlier work was wrong

The original dependency list has no declaration identifying the existential image
filtration predicate with functorial stable-page classes, nor one packaging termwise
sheaf continuity as first-page comparison for this general cofiltered index. These
are now explicit independent substeps. The full comparison theorem asks for much more
abutment data than this kernel-deepening proof needs; finite-page comparison suffices.

Initially the compiled snapshot lacked the item's already-imported filtration module
and the finite-page comparison module. The normal snapshot refresh restored both;
no build or script workaround was used. LeanSearch returned Internal Server Error;
LeanFinder, Loogle and source grep were used and the unavailable search is recorded.

## New nodes

`lem-weil-pbc-etale-complex-filtration-page-data`, in
`lean/Sheaf/AlgebraicGeometry/EtaleComplexFiltrationPageData.lean`, isolates the
functorial first-page dictionary and the uniform stable graded-class identification.
Its proof plan uses existing hypercohomology and pullback-functorial declarations.

`lem-weil-pbc-etale-complex-first-page-continuity`, in
`lean/Sheaf/AlgebraicGeometry/EtaleComplexFirstPageContinuity.lean`, isolates termwise
continuity and canonical first-page cocone identification. Its proof plan uses sheaf
continuity and cofinal directed reindexing. It takes only the first-page part of the
dictionary, so the two statements can be proved independently.

No statement or definition of an existing declaration was changed; no change record.


## Second reading by E1

1. Compared the original module by diff and separately compared the entire existing
   theorem signature byte for byte: identical. Its docstring and every existing
   definition are unchanged. The existing node changes only proof, proof_deps and
   proof_origin. The other two modules and nodes are new. Verdict: no accidental
   public-statement change and no change record required.
2. Compiled all three modules in import order with lcompile.py: clean (30.1, 44.6,
   17.8 seconds). A scratch copy with #print axioms checked the target, the private
   reindexing helper, both new theorems and complexTermCohomologyMap. Only propext,
   Classical.choice, Quot.sound and sorryAx occur; the explicit definition has no
   sorryAx. The helper's sorryAx comes from the existing finite-page comparison;
   the target additionally uses the two listed open lemmas. There are exactly two
   local sorries, both public named theorem bodies; no hollow definitions or banned
   declarations. Verdict: kernel-checked reduction, with open dependencies, not an
   axiom-free completed target proof.
3. Read Stacks 015J (derived.tex, lemma-two-ss-complex-functor), 09YQ
   (etale-cohomology.tex, theorem-colimit) and 0EZM
   (lemma-colimit-variant-complexes), in /home/ubuntu/c1-stacks-review. The common
   lower bound is what makes stabilization uniform: after exchanging coordinates,
   the differential has displacement (1-N,N), so N greater than both p-q+1 and q-a
   removes outgoing and incoming terms. Page-data needs no limit-cone or qcqs
   hypothesis: it constructs spectral sequences for bounded-below complexes at the
   stages and the cocone vertex. Inverse image preserves zero objects and evaluation
   preserves the complex colimit, so the limit complex has the same lower bound.
   Chain maps from complexes zero below q factor through the stupid truncation;
   its inclusion supplies the reverse containment, identifying the image predicate.
   The quotient projection gives precisely the next-step kernel; functoriality and
   hP/hH identify the transition and limit maps. First-page continuity uses the
   limit, qcqs and affine assumptions exactly in the termwise application of 09YQ.
   Its negative-degree case follows from zero source and target objects. Tested zero
   complexes, a singleton identity diagram, q>p (zero filtration), q<a (zero graded
   piece), and negative resolution degrees. Cofilteredness excludes an empty index.
   Neither lemma includes eventual kernel vanishing, nor does either restate the item.
   Independently searched LeanFinder for functorial E1/stable-filtration data, Loogle
   for colimit.pre, msearch grep for associated graded/firstPageIso, and rg over the
   upstream and Sheaf sources. Read HypercohomologyFirstPage,
   EtaleHypercohomologyPullbackFunctorial and EtaleCohomologyLimitOfSchemes: they
   supply ingredients, not these packaged conclusions. EtaleComplexGradedClassDescent
   concerns lifting limit graded classes, a different assertion. Verdict: true,
   strictly partial substeps; neither can be closed by a short existing application.
4. Read the proof top down. The private helper transports first-page cocone equations
   through a final directed reindexing, applies the existing finite-page theorem, and
   cancels the finality isomorphism. The target then uses mono injectivity and the
   concrete colimit eq_iff' criterion with x and zero at the same stage; the returned
   arrow has precisely the required opposite orientation. No full abutment comparison
   is used. Removed redundant direct proof import Mathlib.CategoryTheory.Limits.Final
   (already supplied by Presentable.Directed). Public imports of the new files provide
   objects/instances needed by their signatures or the explicit definition. Verdict:
   no shorter noncircular available route found. The unit sk-prop-h2 has realized
   statement [] and steps [[]], so no realized step is bypassed.
   All old proof_deps absent from the new list are accounted for: def-sp-etale-dictionary
   is a convention, def-weil-pbc-etale-cohomology remains a statement dependency,
   lem-weil-pbc-complex-spectral-sequence-comparison is pruned from this route, and
   def-sp-kinjective-bridge, lem-weil-pbc-etale-cohomology-limit-of-schemes,
   lem-weil-pbc-filtered-category-directed-cofinal,
   lem-weil-pbc-hypercohomology-e1-pullback-functorial, thm-sp-if-e1 and
   thm-sp-spectral-object-yields are moved to the new substeps, not globally pruned.
5. Matched the existing node's three steps with the Lean reduction and the three new
   proof dependencies. Read both new nodes, checked their proof-dependency unions,
   creation/source/blueprint/chapter/unit fields and natural-language proofs against
   the signatures. Corrected both lean.statement records from whitespace-flattened
   text to the actual verbatim multiline signatures and added the independent search
   records. Verdict: nodes agree with the Lean and retain the unit route.

Second reading changed: one redundant proof import removed; new-node verbatim signatures
and search evidence repaired; report explicitly classifies the result as a decomposition
and records every displaced old proof dependency. No mathematical signature or proof
body was changed.
