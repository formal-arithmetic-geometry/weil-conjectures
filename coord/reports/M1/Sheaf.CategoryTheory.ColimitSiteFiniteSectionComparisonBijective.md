## What changed

Repair of the import-prune return: replaced the duplicate private
`CategoryTheory.arrow_apply_heq` with the strictly more general proved private
`CategoryTheory.arrow_map_apply_heq`. Its explicit binders allow an arbitrary category
and an arbitrary functor to Type, rather than only abelian-group morphisms. The call
uses `forget AddCommGrpCat`; the proof uses Mathlib `Arrow.mk_inj`. No sorry was added.
Both sandbox modules compile after the repair. The existing specialized helper in
`ColimitSiteAbelianSectionUniversality` is private and its module is downstream of
this item, so it cannot be imported here; the return's generalization option is used.


Replaced the proof of `CategoryTheory.colimit_site_finite_section_comparison_bijective`
without changing its signature or definitions. Surjectivity now uses the existing
`CategoryTheory.colimit_site_abelian_section_representatives`, transporting its
representative through E, e and hK. Injectivity uses concrete filtered-colimit
representatives and the new strictly smaller eventual-zero theorem.
The proof imports `Mathlib.CategoryTheory.Filtered.Final`, the existing representative
module, and `Sheaf.CategoryTheory.ColimitSiteFiniteSectionEventualZero`, all privately.
The existing public imports remain required by the signatures and their instances.
The new eventual-zero module has the same signature imports and no unused Final import.

## Proved and sorry left

Hole closed: `CategoryTheory.colimit_site_finite_section_comparison_bijective`
(the only original hole in the item).
Hole added: `CategoryTheory.colimit_site_finite_section_eventual_zero`, node
`lem-weil-pbc-colimit-site-finite-section-eventual-zero`, in its own module, with a
source and complete natural-language proof. No other delivered sorry is present.
This is a decomposition, not a complete proof: one original hole closed and one
strictly smaller hole added; the comparison still depends on sorryAx. The existing
representative theorem may itself depend on open upstream statements.
The first worker's added
`CategoryTheory.colimit_site_finite_section_jointly_surjective` hole and its module
and node were removed before delivery; the existing representative theorem suffices.

## No longer needed

The removed new module `Sheaf.CategoryTheory.ColimitSiteFiniteSectionJointlySurjective`
and its node `lem-weil-pbc-colimit-site-finite-section-jointly-surjective` are not delivered.
The eventual-zero module's unused `Mathlib.CategoryTheory.Filtered.Final` import was removed.
No existing library module is claimed as pruned from the targets' import closure.

The parent node's old proof dependencies no longer directly used by its proof are:
`def-weil-pbc-arrows-functor`, `def-weil-pbc-category-colimit`,
`def-weil-pbc-finite-precoverage`, `def-weil-pbc-sites-and-cohomology`,
`lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`,
`lem-weil-pbc-filtered-colimits-commute-finite-limits`, and
`lem-weil-pbc-initial-functor-cofiltered-criterion`.
Some remain statement dependencies or dependencies of the lower construction;
this list records direct proof edges, not removal of their library modules.
`lem-weil-pbc-filtered-colimit-sets-elementwise` remains directly used through Mathlib.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the private abelian-group arrow evaluation lemma
in `Sheaf.CategoryTheory.ColimitSiteAbelianSectionUniversality`. The repaired helper
has genuinely more general explicit category and functor binders, and its use is
specialized by the forgetful functor. No changes to the other module are required.


The earlier IsIso reformulation was an equivalent restatement. The first worker's
new surjectivity hole duplicated the usable existing representative theorem.
Its eventual-zero node cited the existing abelian eventual-equality theorem,
which imports finite-unit-zero-detection, which imports finite-section-colimit-presentation,
which imports this item: using it here would create a cycle. The remaining hole
instead records the independent presentation construction in Stacks 0A35 and
its equality-with-zero consequence, without citing downstream comparison results.
Both source tags were checked directly at
https://stacks.math.columbia.edu/tag/0A35 and
https://stacks.math.columbia.edu/tag/03CO (the local literature files are absent).

## New nodes

`lem-weil-pbc-colimit-site-finite-section-eventual-zero` states only eventual
vanishing of a stage element whose cocone image is zero. Its source, independent
construction proof, dependency union, search history and verbatim Lean signature
are recorded. No statement or definition change records are needed.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered parent module with the repository using diff and checked
   the theorem signature byte for byte programmatically: unchanged. Only its proof,
   a private Arrow equality helper and private proof imports changed. No definitions
   or target statements changed. The new module has one named theorem and no data definitions.
2. Compiled both delivered modules locally in import order. The only delivered sorry
   is the named eventual-zero theorem, with exactly `:= by sorry`. No axiom, unsafe,
   opaque, implemented_by, extern or hollow definition occurs. Scratch #print axioms
   checks the parent and the lower theorem; both use only standard axioms and sorryAx.
3. Read the remaining split statement and its docstring against Stacks 0A35/03CO.
   It is the injectivity component only, not the whole bijectivity assertion. Zero is
   killed at the identity refinement; all-zero groups and empty-cover zero groups
   satisfy it; an empty source stage has no U; a constant identity diagram reduces
   to x = 0. Searches with different wording (leanfinder, loogle, grep and rg on the
   library) found filtered-colimit support and an existing representative theorem.
   The existing eventual-equality result cannot be used because it is downstream
   of this item. The independent construction proof is retained for that component.
4. Took the shorter existing representative route and removed the duplicate split
   and its node. Kept signature imports, including Grp.FilteredColimits, whose removal
   fails HasWeakSheafify instance synthesis in the statements. Removed the unused
   Final import from the lower module. The No longer needed list covers all old
   direct proof edges not used now. Read dag/units/sk-thm-p1.json realized: this item
   is not a realized unit statement or step, and no unit route is bypassed.
5. Updated the parent node to the actual representative/zero proof and the exact
   union of its proof-step dependencies. Replaced the lower node's circular planned
   dependency with the independent original construction steps and updated their union.
   The new node has the required source, created, blueprint, chapter, unit, searches
   and Lean record, with its signature copied verbatim from the delivered Lean.

Second reading changed the surjectivity proof to use the existing declaration,
removed one duplicate hole/module/node, removed one unused import, repaired the DAG
proof dependencies and clarified the decomposition accounting. No existing signature changed.


## Second reading by M1

1. PASS. Independently compared the parent module with the repository using diff
   and compared its theorem signature byte for byte: unchanged. Its docstring and
   all existing public imports are unchanged. Only private proof imports, the
   generalized private Arrow evaluation helper, and the proof differ. The new
   module contains no definition or chosen data. No change record is needed.
2. PASS. Recompiled both delivered modules in import order with lcompile.py.
   The only delivered sorry is the named eventual-zero theorem. Inspected the
   proof and helper; no forbidden declaration or hollow definition occurs.
   A fresh scratch copy of the current parent prints axioms of both declarations:
   only propext, Classical.choice, Quot.sound, and sorryAx. This delivery is a
   decomposition (one original hole closed, one smaller hole added), with zero
   net holes closed; it does not establish an axiom-clean comparison theorem.
3. PASS. Read the eventual-zero signature, docstring and node against Stacks
   https://stacks.math.columbia.edu/tag/0A35 and
   https://stacks.math.columbia.edu/tag/03CO. The conclusion is just the kernel
   component, strictly less than bijectivity. Checked zero via the identity
   refinement, zero groups, empty-cover zero groups, empty source stages, and
   constant identity diagrams. Fresh leanfinder, loogle and grep searches plus
   rg of project sources found no independent replacement. The existing abelian
   eventual-equality theorem imports finite-unit-zero-detection, then finite
   section presentation, then this parent; using it here would be circular.
   The older unit-zero and varying-site zero theorems assume stronger covering
   stability and extra exactness instances, and do not give this reduction.
   The independent presentation construction is substantial and cannot be
   closed by a short existing-lemma application.
4. PASS. Surjectivity already takes the shorter existing representative route;
   injectivity is a genuine concrete-colimit kernel reduction. Proof-only imports
   are private. The lower module has no unused Final import. Checked the old
   proof_deps against the report: all seven removed direct edges are listed.
   No existing library module is pruned. Read sk-thm-p1 realized: this item is
   below its realized statements and steps, so the unit route is retained.
5. PASS. Both Lean records match their signatures verbatim and both proof_deps
   equal the union of proof-step uses. The parent node changes exactly proof,
   proof_deps and proof_origin. The new node supplies source, proof, searches,
   creation, blueprint, chapter, unit and Lean fields. Its independent proof
   does not cite the parent comparison or downstream zero-detection results.

Second reading changed only this report: added the independent current review
and explicit zero-net-hole accounting. The generalized helper repair already
present in the sandbox is correct and was retained; no Lean repair was needed.
