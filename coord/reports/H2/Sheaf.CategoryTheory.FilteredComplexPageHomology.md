## What changed

Replaced the whole proof of `CategoryTheory.filteredComplex_page_homology` in
`Sheaf.CategoryTheory.FilteredComplexPageHomology` with a compiling reduction to two
strict parts of its existing argument. The theorem's signature is unchanged. The second reading removes a redundant
public import of `Mathlib.Algebra.Homology.ShortComplex.Abelian`; that module is
already exposed through the filtration dependency chain.

The proof establishes `Z_(r+1) ≤ Z_r` directly from antitonicity of the filtration and
monotonicity of subobject operations. It obtains an epimorphic successor-cycle cover,
uses the successor-boundary inverse-image identity, and proves the quotient step with
Mathlib's `HomologicalComplex.homologyIsCokernel`, `ShortComplex.exact_iff_image_eq_kernel`,
`ShortComplex.Exact.gIsCokernel`, and uniqueness of cokernels. A private, fully proved
helper identifies inverse images of kernels with kernels of composites.

Added two statement modules, each with one public named theorem and its own DAG node:
`Sheaf.CategoryTheory.FilteredComplexSuccessorCyclesCover` and
`Sheaf.CategoryTheory.FilteredComplexSuccessorBoundariesImage`. Their imports expose only
what their signatures require. The main module imports them and
`Mathlib.CategoryTheory.Abelian.Exact` only for its proof. No definitions or existing
public interfaces change, and no modules held by other groups are adapted.

Read the Stacks formulas and proof at Tag 012K in the existing local literature mirror,
`/home/ubuntu/work-bp/sheaf/literature/stacks-project/homology.tex`, lines 6011–6104.
The two new proofs in words translate the existing representative calculations into
componentwise subobjects using epimorphic pullbacks, with no elementwise/projectivity
hypothesis. Searches through `msearch.py` and local library searches found no exact
filtered-page result; LeanSearch was unavailable and is recorded as unavailable.

All three delivered modules compile with `lcompile.py --all`; no compiler warnings.
The two new statements were checked mathematically on the zero complex, constant
filtrations (all graded pieces zero), and r = 1 (ordinary graded cohomology followed
by d_1). The incoming predecessor has filtration p-r and total degree n-1, which
produces exactly the incoming filtration p-(r+1)+1 in B_(r+1). The boundary identity
requires only the restriction equation for f: monicity of the page kernel inclusion
makes f uniquely determined. No arbitrary data is chosen in a public definition.

## Proved and sorry left

Closed the item's one hole:
`CategoryTheory.filteredComplex_page_homology`
(node `lem-sp-filtered-complex-page-homology`). No `sorry` remains in the item.

Added two lower holes:
- `CategoryTheory.filteredComplex_successor_cycles_cover`
  (node `lem-sp-filtered-complex-successor-cycles-cover`): the outgoing-kernel
  representative calculation, including epimorphic coverage.
- `CategoryTheory.filteredComplex_successor_boundaries_image`
  (node `lem-sp-filtered-complex-successor-boundaries-image`): the incoming-image
  representative calculation, stated as an inverse-image equality of subobjects.

This is a decomposition, not a complete proof free of `sorry`: one upper hole is
closed and two lower holes are added (net holes closed minus added: -1). Neither
new theorem asserts a homology isomorphism or contains both representative calculations.
The containment, kernel transport, exactness and cokernel identification are proved
in the item's module rather than left as a third hole.

## No longer needed

Removed the redundant direct import
`Mathlib.Algebra.Homology.ShortComplex.Abelian` (its declarations remain exposed
through the filtration dependency chain) and the redundant direct proof imports
`Sheaf.Algebra.Homology.FilteredComplexSubquotients` and
`Sheaf.CategoryTheory.FilteredComplexBoundariesLECycles` from the item. Both are
already publicly available through `FilteredComplexPageDifferential`, and their
notions/inclusion remain used. They are not globally pruned modules.

No old proof dependency is eliminated: the updated node still uses the filtration,
subquotients, boundary inclusion, differential data and abelian-category structure,
in addition to its two new representative-calculation nodes. No unit statement or
realized unit step is bypassed. The unit's `realized` lists are empty. No unused
new proof imports remain. In particular, the helper uses Mathlib's factorization
criteria directly, so no source-library subobject-extension import is needed.

## Where the brief, the DAG or earlier work was wrong

The original DAG supplies formulas and the differential data, but does not state
the two kernel/image calculations as usable Lean declarations. They are the actual
remaining work, now separately stated. The categorical quotient-of-quotients
argument is supplied by Mathlib and does not require another open theorem.

The local `blueprint_refs.py ancestor lem-sp-filtered-complex-page-homology` prints
`None`, because its ancestry walker follows `created.item` as a node id although
stage-3 records use module names. The new nodes preserve the original node's
explicit blueprint ancestor `thm-sp-spectral-object-yields` and prepend this item
node to its recorded `via` list. No tool was changed or bypassed.

## New nodes

`lem-sp-filtered-complex-successor-cycles-cover`, in
`dag/nodes/sec-abelian-varieties/lem-sp-filtered-complex-successor-cycles-cover.json`,
records the epimorphism from successor graded cycles onto page cycles, together
with its canonical restriction equation. It has a complete local-lifting argument
in its docstring and node, a signature copied from the compiled module, and three
recorded search kinds.

`lem-sp-filtered-complex-successor-boundaries-image`, in
`dag/nodes/sec-abelian-varieties/lem-sp-filtered-complex-successor-boundaries-image.json`,
records the inverse image of the incoming boundary image. It has a complete
representative argument in its docstring and node, a signature copied from the
compiled module, and three recorded search kinds. The second reading adds the import-only change record
`coord/changes/filteredComplex_page_homology_imports.md`; existing definitions,
statements and declaration visibility are unchanged.


## Second reading by H2

1. **Interfaces: pass.** Read the diff against the repository's
   `FilteredComplexPageHomology.lean` and compared the existing theorem signature
   verbatim: K, F, integer r, hr, differential data D, bidegree pq and the Nonempty
   isomorphism conclusion are unchanged. Its docstring is unchanged. The only
   added local declaration is a proved private kernel-pullback helper. There are
   no changed definitions, target statements or adapted modules. The new public
   statements are in their own new modules. The removed public import is documented in
   `coord/changes/filteredComplex_page_homology_imports.md`, as preflight requires.

2. **Proof and axioms: pass as a decomposition.** Independently compiled all three
   modules with `lcompile.py --all`, with no errors or warnings. Compiled scratch
   copies with `#print axioms` for all three public theorems and the private helper.
   The public theorems use only propext, Classical.choice, Quot.sound and sorryAx;
   the helper uses only the three allowed axioms. The only two literal sorries
   are exactly the two reported public named split-off theorems. No axiom, unsafe,
   opaque, implemented_by, extern or hollow definition occurs. The existential f
   is used inside a proof, and its restriction equation determines it uniquely
   since iCycles is monic; no arbitrary witness becomes definition data.

3. **New statements: pass.** Read Tag 012K's displayed formulas and
   lemma-spectral-sequence-filtered-complex in the local homology.tex, lines
   6011–6104, alongside both new Lean statements and their nodes. The cover
   isolates the outgoing kernel calculation; the boundary theorem isolates the
   incoming image calculation. Neither asserts the item's homology isomorphism.
   For the cover, the target r-boundary expression uses filtration
   (p+r)-r+1=p+1: subtracting its lifted representative preserves the source
   graded class. For the boundary theorem the predecessor has filtration p-r
   and total degree n-1, so its r-cycle condition is dx in F^p and its image is
   exactly B_(r+1) modulo B_r. Pulling that image back to Z_(r+1) adds only B_r,
   already contained in B_(r+1). No Epi f assumption is needed for this identity:
   the restriction equation fixes f by monicity. The docstrings explain both
   containments and the use of epimorphic pullbacks, so they apply to arbitrary
   abelian categories rather than requiring elements or projective objects.

   Checked the zero complex, constant filtrations, and a two-term complex of
   vector spaces with identity differential from degree n to n+1. Give the source
   its sole graded piece at p=0 and target its sole graded piece at p=1. At r=1
   the differential is an isomorphism: the source successor cycles and outgoing
   kernel both vanish; at the target, the incoming image and successor boundaries
   are the whole one-dimensional space. With the target at p=2 instead, d_1=0
   and d_2 is an isomorphism, checking the same identities with a genuine delay.
   These also check the predecessor indexing and the distinction between current
   and successor boundaries.

   Repeated msearch with different wording for the kernel cover and incoming
   boundary quotient; LeanFinder returned general cochain factorizations and
   HomologicalComplex image/kernel lemmas, not these filtered calculations.
   Loogle's Subobject.pullback/kernelSubobject query reports an unknown identifier,
   not a successful no-match. Grep and rg searches of Mathlib, upstream
   WeilConjectures, lean/Sheaf and the DAG found no exact existing public result.
   Inspected FilteredComplexQuotientImageComparison: it concerns images of
   cohomology maps between quotient complexes, not this page kernel/image.
   SubobjectHomologyStep is a general quotient step and its pullback_kernel is
   private, hence unavailable; the current helper is a short direct proof.
   Neither split-off hole can be closed by those declarations in a few minutes.

4. **Route and pruning: pass.** Followed the main proof from antitone cycle
   containment through the cover, boundary pullback identity and exact cokernel
   comparison. Checked Mathlib's homologyIsCokernel and exact_iff_image_eq_kernel
   against their actual declarations. The map to homology is epic as a composite
   of the cover and homology projection; Exact.gIsCokernel then gives the required
   cokernel and the final iso has the original orientation. All original
   proof_deps remain used: filtration, subquotients, boundaries-in-cycles,
   differential data and abelian structure. Thus no old node or globally reached
   module is pruned. Read sk-prop-av-pqf-finite.json: realized.statement and its
   realized step are empty, and no unit realization or chapter route is changed.

5. **Nodes: pass.** Diffed the existing node: only proof, proof_deps and
   proof_origin change. The four proof steps match the actual Lean reduction;
   proof_deps is their uses union. Read both new nodes whole: their hypotheses,
   conclusions, source, natural-language proof, searches, created record,
   blueprint ancestry, chapter, unit and Lean record match their modules and
   the standing brief. No cyclic dependency on the item is introduced.

Second-reading changes: removed the redundant public ShortComplex.Abelian import,
which is needed only by the proof and already available transitively, and changed
one proof lambda to the conventional mapsto spelling. No mathematical proof,
statement or definition needed repair. Updated the two new nodes’ Lean statement
fields to retain the signatures verbatim, including their original line breaks. Updated the import report above. Preflight initially required a change record for
the removed public import; added it, checked the retained public import chain to
ShortComplex.Abelian, and compiled an unchanged scratch copy of the sole direct
importer, FilteredComplexPositivePages, against the revised sandbox modules. No
forced adaptation or target review is needed because no definition or target
meaning changes.
This delivery remains one hole closed, two holes added, net -1: a decomposition,
not a sorry-free proof of the item. Axiom probes are scratch files, not delivery files.
