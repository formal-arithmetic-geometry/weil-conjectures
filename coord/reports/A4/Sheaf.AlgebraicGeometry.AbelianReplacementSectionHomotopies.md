## What changed

The existing theorem `abelian_replacement_section_homotopies` now has a complete Lean proof from the construction-only theorem `abelian_replacement_section_homotopies_core`. A proved private helper `quasiIso_of_replacement_section_homotopy` supplies the entire acyclicity step. It proves that sections of l and sections of the explicit forgotten identity lift are quasi-isomorphisms, transfers the latter property across the second homotopy, and cancels the former using two-out-of-three.

The remaining construction theorem lives in the new module `Sheaf.AlgebraicGeometry.AbelianReplacementSectionHomotopiesCore`. It omits both the quasi-isomorphism conclusion and the unnecessary termwise-injectivity assumption on K. The original theorem's signature and visibility are unchanged. New imports are proof-only; no existing public import was changed. The construction module imports the mapping-cylinder and uniqueness modules and Mathlib injective model-category lifting API used by its recorded proof plan. The parent DAG proof now records the construction and the Lean acyclicity proof separately. The unit route is unchanged.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.abelian_replacement_section_homotopies`. Added one hole in `AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.abelian_replacement_section_homotopies_core`, node `new-abelian-replacement-section-homotopies-core`. This is a decomposition: one original hole closed, one construction hole added, net zero. The acyclicity step is proved, not split off. The new hole carries the parent plan's first two steps; the existing theorem combines those with the actual proof of its third step.

The private theorem `quasiIso_of_replacement_section_homotopy` is proved without any new sorry. It needs only the second homotopy and imposes no augmentation or first-homotopy conditions. No other sorry is added. Existing dependencies may still use sorry, as allowed by this stage.

## No longer needed

No existing import was removed. The second reading removed the redundant newly added proof import `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`; its API is already publicly available through `ModuleCohomologyExtResolutionNaturality` and `ModulePushforwardInjectiveAcyclic`. This removes a redundant direct edge, not a module from the import closure. The planned dependency `lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso`, module `Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso`, is not needed by this proof: the nonnegative acyclic-comparison API proves the needed section comparison directly from `module_pushforward_injective_acyclic`. In particular its integer-complex extension and reflection work is avoided here. This is local pruning, not a claim that the module is globally unreachable. The lifting, uniqueness, inverse-image and counit dependencies remain needed inside the construction node. The old direct edges `def-pc-flat-cohomology-comparison`, `lem-weil-pbc-lift-along-injective-quasi-iso` and `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy` have moved to the construction node rather than been pruned. The old direct edge `lem-sc-injective-module-abelian-acyclic-zariski` is replaced by `new-module-cohomology-ext-resolution-naturality`: its proved wrapper `forgottenInjectiveAcyclic` still uses the old acyclicity theorem indirectly. Thus this last edge removal is not a claim that the underlying result is unnecessary.

## Where the brief, the DAG or earlier work was wrong

The original plan proposed extending to integer complexes for the section quasi-isomorphism step. The source library already provides `Functor.quasiIso_map_of_rightAcyclic_nat`, so extension is unnecessary for that step. Injectivity of K is needed for the acyclicity proof but not for construction of the two homotopies. No mathematical error in the original statement was found. The new construction statement was checked against the zero-complex, zero-coefficient and empty-scheme cases.

The local published library initially lacked the olean for the existing `AbelianCounitResolutionCalculation` prerequisite. An unchanged sandbox copy was compiled to supply that local prerequisite, then removed from the delivery; no dependency source is modified or delivered.

## New nodes

`new-abelian-replacement-section-homotopies-core` states only the construction of q and the two homotopies, without any quasi-isomorphism assertion or injectivity condition on K. Source: Stacks 013P(1), 013S, and the common-section comparison of 01FB. Its proof in words is in the Lean docstring and its node, with the needed mapping-cylinder and injective-lifting ingredients named. It contains the sole new sorry. No change record is required: no existing statement, definition or public interface was changed.

## Second reading by A4

1. Compared the complete existing module against the repository with diff and
   compared its theorem signature with the node's verbatim Lean statement.
   Verdict: the existing signature, visibility and definitions are unchanged;
   all changes are proofs, private helper code and proof-only imports. The new
   construction theorem has its own module and node; no change record is needed.
2. Compiled both modules locally in import order. Scanned the delivered sources:
   the sole sorry is the named public construction theorem, with source and
   proof docstring; there is no axiom, unsafe, opaque, implemented_by, extern or
   definition containing sorry. A scratch-copy #print axioms check found only
   propext, Classical.choice and Quot.sound for the private acyclicity helper;
   the parent and construction theorem additionally contain sorryAx. Verdict:
   the acyclicity step is kernel-checked and the construction remains open.
3. Read the construction theorem against Stacks 013P(1), 013S and the actual
   forgotten augmentation, counit lift and sections-isomorphism definitions.
   Exact abelian inverse image ensures f_*R has injective terms. The lifting
   homotopy and the augmentation identity identify both maps from the single
   degree-zero complex; uniqueness after the augmentation quasi-isomorphism
   supplies the first homotopy. Taking sections and cancelling a.hom/a.inv
   supplies the second. No injectivity of K is used here. In zero and empty
   cases the same maps and identities apply; when K is zero its quasi-isomorphism
   hypothesis forces the required acyclicity. The new lemma is strictly a part
   of the original argument: it drops QuasiIso q, which the private helper proves,
   and drops hK. It is not a renamed copy of the item. Repeated LeanFinder search
   with “Precomposition by a quasi-isomorphism induces a bijection on homotopy
   classes of maps into a bounded below injective complex” found generic
   K-injective localization APIs, not this section comparison. Local rg over
   lean/Sheaf and lean/WeilConjectures found only the parent, its users and the
   fixed counit definitions. The msearch grep query
   “counitResolutionAdjoint|descOfQuasiIso|homotopy_of_comp” returned no hits.
   A Loogle compound-expression query had a parser error and supplies no evidence.
   Verdict: true, needed, properly sourced decomposition; completing the remaining
   adjunction and comparison calculation is not a few-minute repair.
4. Reviewed the acyclicity proof from the parent downward: it uses the existing
   nonnegative acyclic-comparison API directly, then homotopy invariance and
   two-out-of-three. No integer-complex reflection lemma is needed for this step.
   Checked every old proof dependency: inverse-image, lifting, mapping-cylinder,
   uniqueness and counit remain in the construction plan; only
   lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso is bypassed.
   No longer needed records it. Read dag/units/sk-thm-p1.json realized: this
   auxiliary node realizes no unit step, and no unit route is replaced. Verdict:
   valid pruning below the unit level; the remaining explicit imports are needed
   by the proof, statement or the construction plan.
5. Compared both DAG records with the declarations and proof. The parent records
   construction, the two applications of quasiIso_map_of_rightAcyclic_nat, and
   cancellation; the new node records the actual construction-only statement,
   sources, proof steps and their dependency union, searches, origin, creation,
   blueprint, chapter, unit and verbatim Lean signature. Verdict: records agree.

Second reading changed: removed the redundant direct Acyclic proof import;
added the construction plan's proof-only mapping-cylinder, uniqueness and
Mathlib injective model-category imports, which were missing. Completed the No longer needed accounting for all removed direct DAG edges. No proof or
statement needed repair. This delivery closes one original hole and adds one
construction hole: a decomposition with net zero, not a completed proof.
