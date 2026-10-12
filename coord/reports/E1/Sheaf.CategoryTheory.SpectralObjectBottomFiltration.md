## What changed

Replaced the sole sorry in `Sheaf.CategoryTheory.SpectralObjectBottomFiltration`
with a complete Lean reduction to a single local successor-page square.
The existing statement, universes, visibility and public imports are unchanged.
Added proof-only imports of
`Sheaf.CategoryTheory.SpectralObjectBottomPageCompatibility` and
`WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits`.

The proof reuses the source library's proved consecutive image-quotient and
stable-page comparisons. Private helpers transport cokernels through the
specified abutment isomorphism. It proves bottom-row transitions and their
iterates epi, proves the canonical bottom-page map monic at page p+2, identifies
its image with the bottom-edge image, constructs k by equality of subobjects,
and constructs g on the bottom row using the invertible quotient projection.
For q>0 the existing graded comparison supplies g. Thus the gluing argument is
actual Lean, rather than an application of a renamed existence statement.

`Sheaf.CategoryTheory.SpectralObjectBottomPageMap` supplies the explicit map
from each bottom-row page to the abutment, constructed from proved APIs.
`Sheaf.CategoryTheory.SpectralObjectBottomPageCompatibility` isolates its local
cycles-to-homology square. Updated the original node's proof and dependencies
to this route. No existing definition or statement was changed, and no
adaptations or change records are needed.

## Proved and sorry left

Original hole closed:
`CategoryTheory.exists_spectral_object_bottom_filtration`
(node `lem-sc-spectral-object-bottom-filtration`). Its body contains no sorry.

One new hole remains:
`CategoryTheory.Abelian.SpectralObject.bottomPageMap_compatibility`
(node `lem-sc-spectral-object-bottom-page-compatibility`). This is a square for
one successor page, with no supplied transition family, iterated map b,
transported abutment, filtration, graded comparison, or existence conclusion.
Its proof is exactly `by sorry`, with a full proof in words in its docstring
and node. This delivery is a decomposition: one upper hole closed, one lower
hole added, net zero holes removed. It is not a completed axiom-free proof of
the original theorem.

The explicit definition `bottomPageMap` contains no sorry and chooses no
arbitrary existence witness. Its only inverse is specified by a proved
isomorphism. The private theorems `bottomPageMap_two` and `bottomPageMap_mono`,
and the private `graded_comparison`, are fully proved. The latter chooses
isomorphisms only from existing proved Nonempty theorems.

All three modules compile together through lcompile.py, without warnings.
Edge cases: r=2 has identity outer intervals; p=0 uses the valid degree -1
and the stable page is already page two. No positive-degree restriction is
added. The compatibility proof in words covers these cases by the same
spectral-object homology data.

## No longer needed

No existing imports, nodes or modules are pruned: all three original proof
nodes are still used. In particular, the source spectral-object abutment,
filtration definition and spectral-sequence definition are retained.
The prose plan's comparison with every page later than the stable page and
its uniqueness argument for t are unnecessary: the proof uses the specified
t and the single successor square directly, then induction. Those extra
arguments had no separately imported module or node to remove.

## Where the brief, the DAG or earlier work was wrong

The original DAG's step 3 hid a local naturality calculation relating the
spectral-object kernel/opcycles homology model to the abutment map. The cited
abutment theorem gives graded objects but does not provide this square.
The new local node states exactly that missing calculation; the other parts
of the original plan are implemented from existing proved declarations.

For the next worker: expanding `spectralSequence_iso`, then
`π_homologyIsoSc'_hom`, `homologyπ_comp_homologyIso_hom`, the two cycles
isomorphisms, and `spectralSequenceHomologyData_left_i/left_π` reduces the
square to naturality of `ιE` and `fromOpcycles`. Use the literal next-page
indices `2-(r+1)` and `r+1-1`, matching bottomPageMap, to cancel the page
isomorphisms before normalizing arithmetic. Using `import all
Mathlib.Algebra.Homology.SpectralObject.SpectralSequence` is necessary for
that attempted proof because `spectralSequence_iso` exposes private proof
constants; that import is not present in the delivered statement module.
The remaining identity is opcyclesMap_fromOpcycles followed by the commuting
H-map square and functoriality after moving inverse vertical maps across it.

The blueprint-ancestor helper returned None when applied to the original
created node, whose `created.item` is a module name. New nodes instead retain
the original node's explicit blueprint ancestor
`lem-sc-pic-proper-ntorsion`, extending its via chain by the original node.
The unit record's realized statement and steps are unchanged.

## New nodes

`def-sc-spectral-object-bottom-page-map`:
`lean/Sheaf/CategoryTheory/SpectralObjectBottomPageMap.lean` defines the
canonical bottom-page map explicitly, using the page comparison, iota-E,
fromOpcycles and the inverse of the first-quadrant interval comparison.
The definition node has no proof obligation or sorry.

`lem-sc-spectral-object-bottom-page-compatibility`:
`lean/Sheaf/CategoryTheory/SpectralObjectBottomPageCompatibility.lean` states
the local successor-page square and carries the only new sorry. Its source
is the spectral-object construction behind Tags 012K and 015N, expanded
against Mathlib's homology-data and naturality APIs; the written argument
is agent-authored. The statement is strictly part of the bottom-factorization
argument, and is independent of the transport and filtration construction.

Searches: LeanSearch was attempted for both notions and returned Internal
Server Error, so no absence verdict is drawn from it. LeanFinder returned
mapping-cone homology-sequence declarations, not the required map or square.
Loogle found no specialized bottom-edge result. Grep/read of Mathlib's
SpectralObject/{Page,Cycles,SpectralSequence}.lean found the constituent APIs;
grep of both library roots and the entire DAG, plus the blueprint search,
found no duplicate bottomPageMap or compatibility node.

No change records.

## Second reading by E1

1. Interface preservation — PASS. Read the complete diff of
   `SpectralObjectBottomFiltration.lean` against the repository version.
   The existing theorem signature, from its declaration through the conclusion,
   is byte-for-byte identical, including universes, hypotheses hT/ht/hb2/hbt,
   and both required compatibility equalities. No existing definition changes.
   The only added imports in that module are plain, proof-only imports. The
   revised proof docstring describes the actual reduction. The two new modules
   expose their definition and statement and publicly import only what those
   interfaces need. No change record or forced adaptation is required.

2. Kernel proof and data — PASS AS DECOMPOSITION. Independently compiled all
   three modules in import order with lcompile.py; no errors or warnings.
   Scanned all delivered Lean files: only bottomPageMap_compatibility contains
   sorry, as a named public theorem with body exactly `by sorry`; there are no
   forbidden declarations or implementation attributes, and no holed definition.
   Scratch-copy #print axioms checks gave [propext, Classical.choice, Quot.sound]
   for bottomPageMap, and those axioms plus sorryAx for both the compatibility
   theorem and exists_spectral_object_bottom_filtration. The explicit map takes
   its inverse from the proved interval-map isomorphism. The graded comparison
   chooses isomorphisms from proved upstream Nonempty results, not unproved
   arbitrary existence. The cokernel and subobject helpers are kernel-checked.
   One original hole is closed and one new hole is added: net zero, not an
   axiom-free proof of the original theorem.

3. Split statement — PASS. Read both new nodes, their modules, and Mathlib's
   SpectralObject/SpectralSequence.lean homologyData, fac,
   spectralSequenceHomologyData_left_i and spectralSequence_iso; also read
   Page.lean map_ιE and Cycles.lean opcyclesMap_fromOpcycles.
   The kernel model is E^p(1-r,0,1,r-1); its inclusion changes the first
   endpoint to 2-r, and its homology projection changes the last endpoint
   to r. These are the two changes described in the docstring. Naturality
   of iota-E and fromOpcycles reduces the square to functoriality of H,
   with inverse interval comparisons justified by first-quadrant vanishing.
   At r=2 the old outer intervals are identities; at p=0 the degree below
   p is the integer -1. Neither case requires an extra hypothesis. The zero
   spectral object also satisfies the square. The claim quantifies only Y,p,r
   and asks for one equality: it does not restate the existence of g,k or
   assume t,b,H,T. Its proof in words is complete, and its node matches it.
   Independent searches used different queries: LeanFinder for naturality of
   page morphisms with cycles inclusion and homology projection returned
   HomologicalComplex naturality APIs; Loogle for spectralSequence/iso returned
   the existing page and homology comparison APIs; wrapper grep for
   homologyπ_comp_homologyIso_hom, spectralSequence_iso, and map_ιE found the
   constituent formulas. Direct rg over lean/Sheaf and lean/WeilConjectures
   found no general bottom-page map or this square. No exact existing result
   or shorter complete proof was found. Formalizing the remaining naturality
   calculation requires the full homology-model transport, rather than a
   short substitution into one existing lemma; the correct split is retained.

4. Route and pruning — PASS. Read the upstream image quotient, stable page,
   bottomEdge and imageSubobject_bottomEdge declarations used by the reduction.
   The proof first uses these proved APIs, and uses the new open square only
   for hstep and the iterated factorization. The added Subobject.Limits import
   supplies imageSubobject_comp_of_epi. The original proof_deps were exactly
   lem-sp-first-quadrant-spectral-object-abutment, def-sp-filtration and
   def-sp-spectral-sequence; all three remain used, so `No longer needed` is
   complete and no original module is pruned. Read the unit
   dag/units/sk-thm-curveestimate.json: its realized statement remains
   thm-sc-proper-cohomology and its steps remain empty. This below-unit
   reduction neither changes nor bypasses a realized unit step.

5. DAG agreement — PASS. Compared the original node JSON with the sandbox:
   only proof, proof_deps and proof_origin differ. Its revised steps describe
   graded_comparison, bottomPageMap_two/mono, the two inductions, image
   identification, and the quotient construction implemented in Lean.
   The union of their uses is exactly proof_deps. The two new nodes have
   matching declarations, self-contained statements, sources, actual search
   records, creation metadata, chapter/unit and explicit blueprint ancestry.
   The definition has no proof obligation; the compatibility node is the sole
   new open theorem. Existing node statements and the unit record are unchanged.

Changes by the second reader: added this independent review and search evidence;
no Lean or DAG repair was needed. Removed all temporary axiom-probe copies after
checking them. The delivery remains one-hole-for-one-hole decomposition, with
no pruned imports or modules.
