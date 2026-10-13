## What changed

Proved `CategoryTheory.filteredQuotient_page_maps` in
`Sheaf.CategoryTheory.FilteredQuotientPageMaps`, with its signature unchanged.
The proof follows all three steps of `lem-sp-filtered-quotient-page-maps`.

Private, proved helpers show that pullbacks, images, intersections and sums
transport preserved subobjects across a commutative square. Step restrictions
come from the filtered morphism's preservation property. Cokernel maps give
graded maps; the subobject inequalities give cycle and boundary maps; a second
cokernel map gives the quotient component. These restrictions are uniquely
determined by monic inclusions and epic projections. The simultaneous
representative cover proves differential commutation using the underlying
chain map equation. Identity and composite squares prove both category laws.
The four-square property determines every component and hence the whole family.

Added the proof-only import
`Sheaf.CategoryTheory.FilteredComplexDifferentialRepresentativesCover`.
A theorem-scoped unused-variable linter setting preserves the original nested
binder names `hr` and `t`, which are unused in their dependent function types.
No public signature, definition, or public import changed. No new holes or nodes.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.filteredQuotient_page_maps`
(node `lem-sp-filtered-quotient-page-maps`).
No `sorry` remains in this module; none was added elsewhere.
This is a proof, not a decomposition. All private helper theorems are proved,
and all private construction fields contain actual data or proved properties.
The step lifts chosen using classical choice are uniquely determined by their
monic inclusion square, not arbitrary witnesses of an unproved existence claim.

## No longer needed

None. No imports removed and no planned proof dependency pruned.
The proof uses the filtration and concrete-subquotient definitions,
the page differential data, and the simultaneous representative-cover theorem.
It needs neither successor-page comparisons nor additional spectral-sequence
theory; those were not dependencies of this item.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The existing DAG proof already describes the
construction implemented here, so no route or node change is necessary.
The assigned unit record has no realized statement or proof step for this node;
the proof stays on the existing componentwise quotient route.

Searches: LeanFinder for induced functorial maps on filtered-complex spectral
sequence pages returned general homological-complex and mapping-cone machinery,
not this theorem. Loogle for `CategoryTheory.Limits.imageSubobjectMap` found
Mathlib image maps. The prescribed grep search and direct searches of
`lean/WeilConjectures` and `lean/Sheaf` found the existing quotient definitions
and representative cover, but no already proved map-family theorem. The proof
uses Mathlib's subobject image/pullback adjunction and cokernel universal
properties directly. Source read: Stacks Project Tag 012K, the displayed cycle,
boundary and differential formulas and Lemma 12.24.4.

## Second reading by P1

1. **Interface: pass.** Compared the sole delivered module with the repository
   using `diff`, and checked the existing theorem signature and the complete
   `FilteredQuotientPageMapProperty` definition byte for byte. Both are unchanged;
   the existing docstrings and public imports are unchanged. The only new import
   is private to proofs. No other library module or change record is delivered.
2. **Proof and construction: pass.** Independently compiled the module without
   errors or warnings (2.9 seconds). A scratch copy with `#print axioms` for the
   existing definition, the main theorem, all eight private helper theorems and
   both private constructions compiled (3.1 seconds); every output lists only
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. No `sorry`
   or forbidden declaration is present. Step maps chosen from `t.preserves` are
   unique by the monic step inclusion, as explicitly proved in the uniqueness
   argument. Graded and page maps are actual cokernel maps, and cycle/boundary
   maps are subobject factorizations. The representative cover is eliminated
   only inside a theorem proof, with no arbitrary object chosen for a definition.
3. **Split statements and edge cases: pass.** None were split off, and no new
   public statement or node was added. Read every private helper: preservation
   of pullbacks, images, intersections and sums follows from their universal
   properties. Zero objects, zero filtration steps and zero maps require no
   nonzero hypotheses. At r = 1 the same formulas and representative-cover
   argument apply. Identity and composition squares are checked explicitly;
   unrelated bidegrees commute because both differentials are zero.
4. **Route and pruning: pass.** Read the filtration/subquotient definitions and
   representative-cover/page-differential modules, and searched both library
   roots for existing page-map and cycle/boundary-map declarations. Also ran a
   different Loogle query (`Subobject.existsPullbackAdj`, unavailable under that
   search service's identifier index) and a grep query for adjunction and
   pullback-composition facts; the latter confirms the Mathlib tools used here.
   `filteredQuotient_map_restrictions` gives related restrictions but additionally
   constructs r = 1 maps and unquotiented representatives; it does not supply the
   chain map, category laws, or family uniqueness. The present direct construction
   keeps the stated dependency route without importing that extra module.
   Every old proof dependency is used; `No longer needed: None` is complete.
   The unit `sk-prop-av-pqf-finite` has empty realized entries for this node;
   no realized unit step is bypassed. Both public imports serve the signatures,
   and the new representative-cover import serves only the proof.
5. **DAG agreement: pass.** Read `lem-sp-filtered-quotient-page-maps` and its unit.
   Construction, differential commutation via the epic representative cover,
   and uniqueness/category laws match its three proof steps. Its four
   `proof_deps` and componentwise `proof_origin` already describe the implemented
   proof, so no node edit is needed.

Second reading changed only this report: no mathematical or Lean repair was
needed. Confirmed holes closed: `CategoryTheory.filteredQuotient_page_maps` (1).
Holes added: none (0). No decomposition and no pruned dependency.
