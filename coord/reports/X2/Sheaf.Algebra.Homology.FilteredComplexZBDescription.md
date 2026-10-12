## What changed

Proved `CategoryTheory.DecreasingFiltration.filteredComplex_ZB_description` from the
existing `CategoryTheory.filteredComplex_associated_spectralSequence` and two strictly
smaller new statements. The original theorem's signature and existing public imports
are unchanged. Both new modules are proof-only imports of the item's module.

The proof constructs one spectral sequence using the existing construction, supplies
the first-page cycle and boundary equalities, and supplies the natural comparison for
each page using the construction's own boundary-inclusion witness. It derives the
first-page homology isomorphism by specializing the natural comparison to r=1: both
quotient complexes become the graded complex, the projection square and epimorphic
projection force the comparison map to be the identity, and its homology image is
isomorphic to the graded homology. Thus no additional first-page homology theorem is
left to prove.

Stabilization is proved directly in a private helper. From finite bounds a,b with
F(a)=top and F(b)=bottom, choose R=max(1,max(b-p,p+1-a)). Antitonicity makes both tails
constant for r≥R. Equality of filtration steps is transported to degreewise image
subobjects with congrArg, then the cycle and boundary definitions are rewritten.
A second private helper transports cokernels of inclusions under equality of both
subobjects, using proof irrelevance. The page isomorphisms complete stabilization.
Neither private helper contains a postponed proof.

Updated the parent node's proof, proof_deps and proof_origin to this exact argument.
The existing construction remains used. No unit or chapter statement or route changed;
the item's unit record has no realized bindings for this auxiliary node.

Validation: all three delivered modules compile together in import order without
warnings through lcompile.py. The import-direction check accepts the existing
construction import. The required deliver3.py --no-push run is the final check.

## Proved and sorry left

The item's single original sorry is removed:
`CategoryTheory.DecreasingFiltration.filteredComplex_ZB_description` now has a complete
Lean proof from the named dependencies. This is a reduction, not a claim that the
transitive proof is already free of postponed proofs. Both stabilization helpers are
fully proved, and the first-page homology conclusion is fully derived.

This delivery is a decomposition: one original hole closed and two holes added (net -1
before any later pruning or closure accounting). It does not establish an axiom-clean
proof of the original theorem.

Exactly two new sorry declarations remain, each in its own module, with the whole
proof `by sorry`, a complete proof in words, and its own DAG node:

- `CategoryTheory.DecreasingFiltration.filteredComplex_firstPage_cycles_boundaries`
  in `Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries`, node
  `lem-sp-filtered-complex-first-page-cycles-boundaries`. This states just the two
  first-page subobject equalities; it has no spectral sequence or stabilization clause.
- `CategoryTheory.DecreasingFiltration.filteredComplex_quotient_image_comparison`
  in `Sheaf.Algebra.Homology.FilteredComplexQuotientImageComparison`, node
  `lem-sp-filtered-complex-quotient-image-comparison`. This states the quotient-complex
  map and natural image comparison on representatives for given p,n,r and B≤Z. It
  constructs no spectral sequence, assumes no finiteness, and states no stabilization.

The existing imported construction theorem is still an upstream obligation; its
module is not changed by this delivery.

Checked the new statements on r=1, where the quotient map is the identity and the
image is the entire graded homology; on zero complexes and constant filtration
steps, where the graded quotient is zero; and on zero differentials, where the
representatives and the natural map reduce to the indicated filtration projections.
The image comparison is stated only for r≥1, so both required quotient inequalities
hold, including at the endpoint r=1. No boundedness is used in either new statement.

## No longer needed

Removed the direct proof import `Sheaf.CategoryTheory.Filtration`: its definitions
are already provided by the public subquotient import. Its node `def-sp-filtration`
is still needed for the actual finite-tail stabilization proof, and its module is
still needed transitively. The old direct proof dependency `def-sp-abelian` is removed from the parent
`proof_deps`: its general abelian-category facts remain available through the statement
imports and are needed in both new nodes. No existing DAG node or module is claimed
unreachable. The second reader also removed the redundant public import
`Mathlib.Algebra.Homology.ShortComplex.Abelian` from the new comparison module; its
required instances are already supplied transitively by the subquotient import.
The existing spectral-sequence construction remains imported and used.

During development the separate first-page quotient-to-homology obligation was
eliminated: the natural image comparison at r=1 already supplies it. No such node or
module is delivered. The new first-page module needs only the public subquotient
import; unnecessary homology imports were removed before delivery.

## Where the brief, the DAG or earlier work was wrong

The existing construction theorem supplies page subquotient isomorphisms, but not the
first-page subobject identities or the representative-level natural comparison.
Those were not consequences obtainable just by applying its stated declaration;
they are the two new obligations below.

The parent node marked its natural image argument elementary. It is a genuine
kernel-image comparison in a general abelian category, including surjectivity from
representatives and the equality specifying the induced isomorphism. The new node
and docstring state that argument explicitly and mark the unfinished calculation
non-elementary. The finished assembly and the finite-tail stabilization are real
Lean proofs.

The cited local `literature/stacks-project/homology.tex` is not present on this
machine. Read the primary source at https://stacks.math.columbia.edu/tag/012K instead;
its current numbering is Section 12.24 and Lemma 12.24.2, whereas the parent records
12.19.2. This is a numbering/source-location observation, not a statement change.

LeanSearch was attempted for each new statement but returned Internal Server Error.
LeanFinder, Loogle and source rg searches were also performed and recorded in the
new nodes. Their results supply general homology/image tools, no independent theorem
for these filtered-complex subobject calculations. Searches of both project roots
found definitions, the existing construction and downstream users of the parent,
not another theorem giving either new statement.

## New nodes

`lem-sp-filtered-complex-first-page-cycles-boundaries` is the r=1 kernel-image
calculation from Tag 012K. Its source, proof in words, searches and verbatim Lean
signature are recorded in
`dag/nodes/sec-abelian-varieties/lem-sp-filtered-complex-first-page-cycles-boundaries.json`.
Its module is `Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries`.

`lem-sp-filtered-complex-quotient-image-comparison` is the natural quotient-complex
comparison from the parent's third proof step. Its source, full kernel/image
argument, searches and verbatim Lean signature are recorded in
`dag/nodes/sec-abelian-varieties/lem-sp-filtered-complex-quotient-image-comparison.json`.
Its module is `Sheaf.Algebra.Homology.FilteredComplexQuotientImageComparison`.
Both nodes inherit the parent's chapter and unit and introduce no cycle.
There are no statement/definition changes and no change records.


## Second reading by X2

1. PASS. Compared the item against the repository with `diff`; the only existing
   declaration's signature is byte for byte identical, and its docstring is unchanged.
   No definition, target, public import of the existing module, or change record changed.
   The two other Lean modules are new. The existing node changes only proof metadata.
2. PASS as a decomposition. Compiled all three files in import order through lcompile.py
   without warnings. Source scan finds exactly the two reported whole-theorem sorries,
   no forbidden declarations and no holed definitions. A scratch module explicitly
   imports all three modules and prints axioms for all three public declarations:
   only propext, Classical.choice, Quot.sound and sorryAx occur. The original proof
   correctly uses the construction's own inclusion witness, the epic projection at
   r=1, equality transport of cokernels, and the finite bounds in stabilization.
3. PASS. Independently checked both new signatures and their complete docstring proofs
   against the subquotient definitions and Stacks Tag 012K. At r=1 both comparison
   complexes are the graded complex; at r=2 representatives have differential in
   F^(p+2), the kernel is representatives in d(F^(p-1))+F^(p+1), and both quotient
   maps have the stated directions. Zero complexes, zero differentials, and coincident
   adjacent steps give the expected zero or graded objects. Representative arguments
   mean inverse images and images of subobjects in an arbitrary abelian category,
   not an assumption that actual elements lift globally. Neither statement assumes
   finiteness or constructs a spectral sequence; neither restates the full item.
   Fresh LeanFinder searches using induced quotient differentials and images of
   cohomology inclusions, and a Mathlib grep for homology/image and kernel/pullback,
   found general cycle and short-complex tools, not either filtered theorem. Source
   rg in lean/Sheaf, lean/WeilConjectures and the upstream WeilConjectures tree likewise
   found no independent proof. These categorical calculations are not closable in a
   few minutes from a single existing lemma.
4. PASS after import/report pruning. Construction and both smaller calculations are
   used; the first-page homology and stabilization arguments are actually completed.
   Removed the redundant ShortComplex.Abelian import from the new comparison module,
   then recompiled all files. ShortComplex.HomologicalComplex is required by the
   comparison statement (removing it loses cycles and homologyMap), so stays public.
   The report now names the old def-sp-abelian proof dependency removed from the
   parent. No module is claimed unreachable. The unit record's realized statement
   and step lists are empty; no unit route is bypassed or changed.
5. PASS. Checked the parent proof steps against the Lean, equality of each node's
   proof_deps with the union of its steps' uses, verbatim signatures of both new nodes,
   sources, searches, created fields, blueprint ancestry, chapter, unit and Lean
   records. Parent statement and all metadata outside the permitted proof fields
   are unchanged. Both new nodes meet the standing brief's required fields.

Changes by this reader: removed one redundant new-module import, completed the
No longer needed inventory, stated the decomposition and net hole change explicitly,
and added this independent review. No mathematical statement or proof body changed.
