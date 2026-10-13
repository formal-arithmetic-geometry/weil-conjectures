## What changed

Proved `CategoryTheory.filteredQuotient_map_restrictions` in
`Sheaf.CategoryTheory.FilteredQuotientMapRestrictions`, with the original signature and
visibility unchanged. Added a proof-only import of
`WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits` for its factorization criteria
and image-pullback Galois connection (including the imported lattice lemmas).

Six proved private helpers express restriction and preservation of pullbacks, images,
intersections, sums and filtration steps. The main proof applies them to the existing
cycle, boundary and representative definitions, cancels the target cycle inclusion to
check the boundary-to-cycle square, and applies `cokernel.map`. The page-one witnesses
are a second application of the same construction. The node proof now records these
actual operations. The unit route is unchanged: its `realized` lists are empty.

A theorem-local `set_option linter.unusedVariables false in` suppresses the unused `hr`
binder inside the existing `hBZ` hypothesis: its conclusion does not mention that named
positivity witness. This keeps the existing signature verbatim and changes no elaboration
or typechecking option. All helpers remain subject to the default linters.

Search: LeanFinder returned `imageSubobjectMap`, `pullback_factors_iff` and related
universal-property lemmas; Loogle returned `Subobject.pullback_comp`; msearch grep and
repository searches found no existing identical filtered restriction theorem. Direct
inspection of the source library found the factorization and Galois-connection API used
here. The cited local Stacks TeX is absent on this machine, so the source formulas and
Lemma 12.24.4 were checked at https://stacks.math.columbia.edu/tag/012K.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.filteredQuotient_map_restrictions`
(node `lem-sp-filtered-quotient-map-restrictions`).

No holes remain in the module; no holes were added or split off. All private helpers are
proved. This is a complete proof, not a decomposition. Local compilation passes; the dry
run additionally probes the axioms of all declarations.

The construction works for all integer page indices at the subobject-preservation level;
positivity is used to access the supplied `hBZ` containment. It therefore needs no exceptional
argument for r=1, zero maps, zero objects or zero filtration steps. Finiteness is not used
by this restriction argument, but the original full-subcategory hypotheses are preserved.

## No longer needed

None. Both original public imports are needed by the unchanged signature. All three
original proof dependencies remain used. No new comparison, first-page homology or
spectral-sequence modules are imported. No node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The previous representative-based prose was expanded into
precise preservation inequalities for the full cycle expression, including the added
(p+1)th step. The source library already proves the needed generic subobject API, so no
new intermediate statements or nodes are necessary.

## Second reading by G3

1. Compared the delivered module with the repository version by diff and checked the
   existing theorem signature byte for byte: identical. The sole added import is plain
   `import`, used only by the proof. No public declaration, definition, visibility or
   target statement changed. No change record or forced adaptation is needed. Verdict: pass.
2. Compiled the module locally with `lcompile.py`, without errors or warnings. A scratch
   copy prints the axioms of the main theorem and all six private helpers: each uses only
   `propext`, `Classical.choice`, and `Quot.sound`. Scanned the delivered Lean source for
   holes and prohibited declarations/options; none occur. No data is selected from an
   unproved existence theorem. Verdict: pass.
3. There are no split-off statements, new nodes or remaining holes. Read every private
   helper: the commuting-square pullback and image inequalities follow from composition,
   monotonicity and the image-pullback adjunction, and the restriction witness follows
   from factorization. These arguments apply unchanged to zero subobjects, zero maps,
   and page one; no nonzero or strict-index premise is hidden. Verdict: pass.
4. Read the proof downward against the actual subquotient definitions and upstream
   `Subobject.FactorThru`, `Subobject.Lattice`, and `Subobject.Limits` APIs. Repeated a
   search using the words factorization, image preservation and pullback, and searched
   the project for related restriction arguments. No existing theorem eliminates this
   filtered construction; the generic universal-property lemmas are already used.
   Both original public imports serve the signature; the added private import supplies
   the factorization and adjunction API. All three old proof dependencies remain used,
   so the pruning list is complete. The unit JSON has no realized statement or step
   nodes, and this delivery changes no unit route. Verdict: pass.
5. Compared the node with the repository: only `proof` and `proof_origin` differ.
   Its steps accurately describe step preservation, cycles and boundary preservation,
   restriction, monic cancellation, cokernel.map, and the two page instantiations.
   Its unchanged proof_deps is exactly the union of the steps' uses. Verdict: pass.

Second reading changed only this report: added the independent checks and their verdicts.
The Lean proof and DAG update required no repair. Closed one original hole and added zero;
no declarations were split off and no modules or nodes were pruned.
