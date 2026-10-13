## What changed

Proved `AlgebraicGeometry.Scheme.Modules.FlatBaseChangeOpenChoices.targetClass_restriction`
without changing its signature, visibility, or docstring. Its only added import is the
proof-only `Sheaf.AlgebraicGeometry.RestrictedResolutionCohomology`.

The new module proves `AlgebraicGeometry.Scheme.Modules.restrictedResolution_cohomology`:
the canonical cohomology restriction, transported through the source and restricted
resolution comparisons, is the homology map of degreewise restriction of sections.
The proof uses the existing `moduleCohomologyFMap_independent`, the source-library
restriction limit-preservation instance, and the right-adjoint injective-preservation lemma.
For an open inclusion the pushed restricted resolution already has injective terms,
so the cohomology-map data uses lambda equal to the identity. No injective replacement
or newly chosen resolution is needed.

In the item module, two proved private helpers establish evaluation-homology/section-class
naturality and combine that square with the raw comparison. The public theorem then
uses naturality of the inverse derived comparison, evaluates at eta, and applies
`TopCat.Presheaf.germ_res_apply`. Both affected DAG nodes record this actual proof route.

The new statement was checked on empty and top opens, zero modules, and degree zero:
it is an equality of the same canonical morphisms, obtained by functoriality and
inverse identities. These cases need no additional hypotheses. For the original
statement an empty V has no witness hy.

Both modules compiled together with lcompile.py in import order. No existing definition
or statement was changed, no forced adaptations were made, and all writes are in the sandbox.

## Proved and sorry left

Closed the item's sole original hole:
`AlgebraicGeometry.Scheme.Modules.FlatBaseChangeOpenChoices.targetClass_restriction`
(node `lem-weil-pbc-target-section-class-restriction`).

Also proved the new
`AlgebraicGeometry.Scheme.Modules.restrictedResolution_cohomology`
(node `lem-weil-pbc-restricted-resolution-cohomology`).

Holes closed: 1. Holes added: 0. No declaration in either delivered module contains
`sorry`; all private helpers are proved. This is a proof from the existing named
library declarations, including the recorded cohomology-map independence theorem;
it is not a claim that the entire transitive dependency closure is already axiom-free.

## No longer needed

No import was removed from the original module: its original public import supplies
`targetClass`, which occurs in the unchanged statement. Every new proof import is used.
No module is claimed pruned from the targets' import closure.

The original node no longer needs a direct proof dependency on
`lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso`
(module `Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso`): the explicit
restriction calculation uses lambda equal to the identity. This node/module remains
a transitive dependency through the existing definition of moduleCohomologyFMap,
so this delivery does not claim that its module can leave the queue.

`def-weil-pbc-module-cohomology-fmap` is also removed from the item's direct
`proof_deps`: its construction is now used by the raw-comparison node, and its
module remains required transitively and for the unchanged statement.

`lem-weil-pbc-module-cohomology-fmap-functorial` is now used by the new raw-comparison
node rather than cited directly by the item. Its module remains needed. The definitions
of the open choices, cohomology map, and section class, and the derived-resolution
comparison remain needed. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false or unusable statement was found. The DAG's extra injective replacement is
unnecessary for this open-inclusion restriction: restriction preserves finite limits,
so its right adjoint preserves injectives. The proof uses this shorter specialization.

The source equation for cohomology restriction at Tag 01E2 is numbered the project server;
the new docstring and node use that number. The existing item docstring was preserved.

Searches: LeanSearch was attempted and returned Internal Server Error; LeanFinder returned
8 naturality-related hits but no restriction/resolution comparison; Loogle returned
12 homology-comparison hits; grep returned germ-restriction lemmas and no Mathlib
resolutionSectionClass. Local searches in both library roots found no existing raw
comparison. Mathlib's `NatTrans.app_homology` and `germ_res_apply` were read and used.

## New nodes

`lem-weil-pbc-restricted-resolution-cohomology` is a proved general tool for steps 1–2
of the item's argument. It compares raw cohomology of section complexes, before theta,
the higher-direct-image comparison, or germs. Its module is
`lean/Sheaf/AlgebraicGeometry/RestrictedResolutionCohomology.lean`.
The node includes the statement, complete proof steps, dependencies, source, searches,
and verbatim Lean signature. There are no change records because no existing interface changed.


## Second reading by Y3

1. **Interfaces: pass.** Diffed the item against the repository. The existing
   theorem signature is byte for byte identical, as is its docstring and public
   visibility. The sole new import in the item is proof-only. The new module has
   no counterpart in the repository. No existing definition changes and no change
   record or forced adaptation is needed. Both node Lean signatures match their
   delivered Lean verbatim.
2. **Proof and trust: pass.** Compiled both delivered modules in dependency order:
   30.1 s and 51.3 s, without errors or warnings. Read each proof, including the
   augmentation, degreewise cancellation, evaluation homology square, derived
   comparison naturality and final germ calculation. No delivered declaration has
   sorry or a forbidden trust escape. Scratch copies with #print axioms for the
   public theorems and all three private helpers compiled; every result contains
   only propext, Classical.choice and Quot.sound, with no sorryAx. The comparison
   data is constructed explicitly. Classical.choice merely unfolds the existing
   canonical cohomology-map choices, whose independence is proved; the delivery
   introduces no arbitrary object chosen from an unproved existence theorem.
3. **New statement: pass.** restrictedResolution_cohomology is a proved raw
   section-complex comparison, strictly below the germ statement, not a renamed
   target or a remaining hole. Its source, complete docstring argument and node
   are present. For U equal to top the restrictions become identities; for empty
   U and zero coefficients the same morphism/inverse identities apply; p=0 uses
   the same augmentation-compatible calculation. Empty V has no hy in the target.
   Repeated searches using different words: LeanFinder for homology of global
   sections restriction unit/open immersion/injective resolution returned eight
   scheme-section comparison hits; Loogle for app_homology returned its exact
   naturality ingredient and two unrelated hits; grep for restriction/injectivity
   found no equivalent theorem. Local searches and reading OpenModuleCohomology,
   OpenRestrictionModuleCohomology, BasicPropertiesRestriction and
   HigherDirectImageResolutionNaturality found related constructions, but no
   equality with the specified moduleCohomologyRestriction and pinned R.sections.
4. **Route and pruning: pass.** The proof uses Mathlib homology naturality and germ
   restriction directly, and a concrete identity comparison avoids another
   injective replacement. All imports are needed with their current visibility.
   An attempted removal of the right-adjoint injective-preservation import failed
   with an unknown constant, so it was restored. Checked sk-thm-p1.realized:
   neither the item nor its replaced lower dependencies realizes a required unit
   step; no chapter or unit route is bypassed. No module leaves the target closure.
   All three old direct dependencies removed from the item are now explicitly
   accounted for in No longer needed.
5. **DAG: pass.** Both proof_deps lists equal the union of their proof-step uses.
   The steps and proof_origin describe the Lean calculation actually performed.
   The new node has the required source, searches, creation/blueprint/unit/chapter
   fields and exact Lean record. The raw comparison is proved, with no added hole.

Second-reading changes: clarified the removed direct dependency on
 def-weil-pbc-module-cohomology-fmap in this report and added this review.
No Lean proof, signature, definition, import, or DAG change was needed.
