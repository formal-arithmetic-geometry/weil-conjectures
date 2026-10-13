## What changed

Completed `AlgebraicGeometry.Etale.exists_etaleCE_prescribed_quotient_page_descent`
without changing its signature. It now combines prescribed normalized presentations,
generic filtered-page descent, and the first-page specialization of the resulting
representative equation. The quotient realization is explicitly evaluation of the
supplied page complex isomorphism; no definition chooses arbitrary existence data.

Added `Sheaf.CategoryTheory.FilteredCanonicalPageDescent`, proving
`CategoryTheory.exists_filteredCanonical_page_descent`. The proof constructs all page
maps and proves their successor compatibility by cancellation on epic successor-cycle
covers, then proves the equation for arbitrary test-object representatives. This works
for arbitrary decreasing filtrations, without a global `IsFinite` hypothesis.

Added `Sheaf.Paper.EtaleCEPrescribedNormalizedFirstPages`, isolating prescribed CE
assembly, normalized page comparisons, and the computation of an individual first-page
map on ordinary sheaf cohomology. This is the remaining intermediate theorem. It
constructs no spectral-sequence morphism and asserts no existence of higher-page maps.
The generic descent proof is the part removed from that remaining work.

All edits are in this item's sandbox. No existing definition, statement or visibility
changed, and no other group's module was adapted. Updated the item's proof route and
added a node for each new theorem. The new modules and the item are compiled individually
through lcompile; the complete sandbox is also compiled in import order.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.exists_etaleCE_prescribed_quotient_page_descent`
(node `lem-weil-pbc-ce-prescribed-quotient-page-descent`).

Proved the new generic theorem
`CategoryTheory.exists_filteredCanonical_page_descent`
(node `lem-weil-pbc-filtered-canonical-page-descent`), including the private proved helper
`CategoryTheory.quotient_homology_square`.

Added one remaining named hole:
`AlgebraicGeometry.Etale.exists_etaleCE_prescribed_normalized_first_pages`
(node `lem-weil-pbc-ce-prescribed-normalized-first-pages`). Its proof is exactly
`by sorry`; its docstring specifies the construction and row comparison argument.

This is a decomposition, not a net decrease in the import-closure hole count: one
original hole closed and one intermediate hole added. There is no remaining `sorry`
in the item's module or the generic descent module. Imported successor-cycle-cover
lemmas may themselves remain unfinished, as intended by stage 3.

## No longer needed

The old direct proof dependencies no longer applied by the item's proof are
`thm-sp-if-e1`, `lem-sp-filtered-complex-page-differential`,
`lem-sp-filtered-complex-normalized-homology`,
`lem-weil-pbc-sheafH-ext-derived-comparison`,
`def-weil-pbc-ext-resolution-sections-iso`, and
`lem-weil-pbc-ext-pullback-resolution-sections`. They remain needed below the two
new intermediate nodes; none is globally pruned.

No original import was removed: `EtaleCEStationaryPageNaturality` supplies the public
statement's types and representative predicate. No original mathematical dependency
is declared globally pruned: the six planned dependencies remain needed for the new
prescribed assembly/first-page intermediate theorem. The item's direct proof dependencies
are now the two new nodes, rather than those six lower nodes.

`Sheaf.CategoryTheory.FilteredQuotientCanonicalFunctor`,
`Sheaf.CategoryTheory.FilteredQuotientHomologyNaturality` and
`Sheaf.CategoryTheory.FilteredQuotientSuccessorCycleMaps` are not needed by this descent
proof and are not imported by it. They were not imports of the original item, so this
is not counted as removal of an existing dependency. In particular the public
finite-filtration theorem `filteredQuotient_page_maps` is not applied to CE totals.

## Where the brief, the DAG or earlier work was wrong

The DAG's plan is mathematically sound, but the available globally finite canonical
functor cannot directly handle these degreewise bounded totals. The generic private
constructions `quotientPageSquares` and `quotientPageMap` in
`FilteredQuotientPageMaps` already accept arbitrary filtered complexes and are proved.
They are reused with `import all` in theorem proofs only; no private declaration occurs
in a public signature or in the body of a public definition. The new public generic
descent theorem supplies the missing general interface. Its proof spells out successor
naturality rather than using the finite public successor-map statement.

The normalized assembly theorem is strictly part of the argument: it constructs the
prescribed presentation and computes only an individual first-page map if supplied.
It has no existence assertion for a spectral-sequence map. The roughly 190-line generic
descent module proves that missing existence and all successor compatibility equations.

Edge cases checked against the constructions: the generic proof needs no lower or upper
bound, assumes no projective test object, never lifts an element through an epimorphism,
and works unchanged for zero complexes and zero graded cycle objects. For the CE
intermediate statement, zero rows and empty schemes use injective row comparisons and
finite-diagonal sums; no nonemptiness or uniform bound was added. The original unit
`sk-prop-h2` has no realized nodes bound to this item; the unit's fixed route is unchanged.

Mathlib searches: LeanFinder found derived/homology functors but no prescribed quotient
presentation or arbitrary-filtration normalized descent; Loogle found the spectral
sequence types only; Mathlib grep found no matching construction. LeanSearch returned
Internal Server Error and is recorded as unavailable. Blueprint searches for quotient
pages and first-page computations found no duplicate; a filtered-complex search found
the bounded spectral-object and double-complex theorems, neither an exact match.

## New nodes

`lem-weil-pbc-filtered-canonical-page-descent` records the proved arbitrary-filtration
descent theorem in `Sheaf.CategoryTheory.FilteredCanonicalPageDescent`. It realizes
step 2 of the item's plan using canonical quotient maps and the normalized successor
comparison; it is valid in an arbitrary abelian category.

`lem-weil-pbc-ce-prescribed-normalized-first-pages` records the remaining prescribed
CE construction and first-page row comparison in
`Sheaf.Paper.EtaleCEPrescribedNormalizedFirstPages`. It realizes steps 1 and 3 of the
item's plan and does not reassert higher-page descent. The source places are Stacks
015J, 015K and 012K, with the explicit Ext-to-resolution-sections comparison and
resolution computation of Ext pullback used for coefficient and scheme naturality.
No change record is required because existing interfaces are unchanged.

## Second reading by R3

1. Compared the original module with the repository using diff. The only changes
   are two proof-only imports, a declaration-local unused-variable linter setting,
   and replacement of the original proof. The existing theorem signature and
   docstring are byte-for-byte unchanged. Both sibling modules are new; no existing
   definition or interface was changed. Verdict: pass.
2. Compiled all three modules in dependency order with lcompile.py: all passed
   without warnings. Scanned every delivered Lean file: exactly one textual sorry,
   the whole proof of the named normalized-first-pages theorem; no prohibited
   declarations or hollow definitions. Read the generic proof's monic and epic
   cancellation steps, including its arbitrary-test-object representative equation.
   The local presentation witnesses are eliminated inside a theorem proof, not used
   to define any public data. Verdict: pass, conditional on the declared remaining
   hole and imported unfinished theorems. Scratch #print axioms checks show only
   propext, Classical.choice and Quot.sound for the generic descent theorem and
   quotient_homology_square, and those axioms plus sorryAx for the assembly theorem
   and original CE theorem; this is a decomposition, not a completed
   target proof.
3. Read the remaining normalized-first-pages statement and its construction proof
   docstring against the original CE hypotheses and the row/quotient interfaces.
   It isolates assembly and computation of a supplied first-page map; it asserts
   no higher-page morphism. The proved generic theorem supplies that separate part
   of the original argument. Zero complexes, zero rows, empty diagonals, p=0,
   negative complex degrees and the absence of a uniform filtration bound add no
   hypotheses or exceptional choices. An epic pullback cover, rather than a lift
   from an arbitrary test object, justifies detecting a map on representatives.
   Independent LeanFinder search for injective bicomplex row naturality found
   injective-resolution comparison lemmas, not the assembly theorem. Loogle search
   for SpectralSequence Hom found types and spectral-object constructions, not this
   result. Mathlib grep for injective-resolution naturality and spectral-sequence
   maps found seven resolution comparison lemmas. Local searches also checked
   FilteredComplexQuotientMap, EtaleCECoherentQuotientPresentations and
   FilteredQuotientHomologyNaturality: these respectively remain unfinished, choose
   their CE resolutions, or require globally finite filtrations. None closes the
   prescribed assembly hole in a few minutes. Verdict: a true, needed smaller
   intermediate statement with a matching node and proof docstring.
4. Read the reduction from the top downward. It constructs the realization by
   evaluating the supplied page isomorphism, applies the proved arbitrary-filtration
   descent, and specializes its representative equation at r=1. Imports supply
   the public signature or declarations actually used in proofs; proof-only imports
   are private. All six old direct proof dependencies are no longer direct uses of
   the item's proof: thm-sp-if-e1, lem-sp-filtered-complex-page-differential,
   lem-sp-filtered-complex-normalized-homology,
   lem-weil-pbc-sheafH-ext-derived-comparison,
   def-weil-pbc-ext-resolution-sections-iso, and
   lem-weil-pbc-ext-pullback-resolution-sections. They remain dependencies of the
   smaller assembly statement or generic construction, so none is globally pruned.
   The unit sk-prop-h2 has empty realized bindings for this item; its route is kept.
   Verdict: pass.
5. Checked all three nodes. The existing node differs only in proof, proof_deps,
   and proof_origin. Its two direct dependencies match the two applications in
   Lean. The new generic node describes the actual quotient-map construction,
   successor-cycle cover argument and conjugation; the new assembly node records
   precisely the remaining hole. Both have sources, search records, provenance,
   chapter/unit and Lean signature records. Verdict: pass.

Second reading changed only this report: made explicit all six old dependencies
removed from the direct proof route, and recorded the independent review and search.
No proof or statement repair was necessary.
