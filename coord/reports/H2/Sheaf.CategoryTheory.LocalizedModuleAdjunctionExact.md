## What changed

Proved `SheafOfModules.localizedModule_adjunction_exact` without changing its signature or
visibility. Added fully proved private helpers for the module direct-sum Hom equivalence,
its naturality, and its composition with the module sheafification Hom equivalence.
Restriction and extension by zero preserve short exact sequences by forgetting to abelian
sheaves, applying the existing abelian results, and reflecting short exactness. Mathlib's
exact-functor characterizations turn this into preservation of finite limits and colimits.

Added proof imports `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor` and
`Mathlib.CategoryTheory.Abelian.ShortExact`. All original imports remain needed for the
statements, instances, constructions, or the proof. Updated the node's proof and proof origin
to record the direct module adjunction construction and explicit functor comparisons.
No existing interface changes and no adaptations.

The source proof was read in a read-only local Stacks source copy, `sites-modules.tex`,
labels `lemma-extension-by-zero` and `lemma-extension-by-zero-exact` (03DI and 03DJ).
Mathlib searches used LeanFinder, Loogle and grep; their actual outputs are recorded in the
sandbox search log. The finite-exact-functor characterizations supplied the short route for
the exactness clauses. The file compiles without warnings in approximately 17 seconds.

## Proved and sorry left

Closed the sole hole `SheafOfModules.localizedModule_adjunction_exact`
(node `lem-pur-site-restriction-module-adjunction-exact`). All five conjuncts are proved.
There are no sorries left in this module, no new sorries, and no split-off statements.

The proof uses the existing named statements
`CategoryTheory.siteExtensionByZeroPresheaf_adjunction` and
`CategoryTheory.site_extensionByZero_exact`, whose proofs are external dependencies. The axiom probe of this theorem still
reports `sorryAx` from the imported library; the private module adjunction reports only
`propext`, `Classical.choice`, and `Quot.sound`. It also uses the already proved `CategoryTheory.siteRestriction_exact` and
`CategoryTheory.moduleSheaves_colimits_forgetful`. The new module adjunction construction
itself does not use the abelian adjunction or its sorry.

## No longer needed

Pruned proof-dependency node `lem-weil-pbc-site-restriction-adjunction`: the proof uses
Mathlib `sheafAdjunctionContinuous` directly rather than that wrapper theorem. No original
imports or dependency modules are removed. The abelian direct-sum adjunction is still used
for the exactness comparison, although it is not used to construct the module adjunction.

## Where the brief, the DAG or earlier work was wrong

The abelian adjunction Lean statement records an adjunction and an inverse-law clause,
but does not expose the sectionwise direct-sum formula described by its informal node.
It therefore cannot directly justify module linearity merely by applying its homEquiv.
The delivery avoids that gap by constructing and proving the linear module Hom equivalence
itself. No statement changes are needed. The unit record `sk-def-sf-operations` has no
realized statement or steps at this node; the unit and chapter route are preserved.


## Second reading by H2

1. PASS: compared the complete module with the repository using `diff`. The existing
   theorem signature and visibility are byte-for-byte unchanged. The existing docstrings
   and definitions are unchanged; additions are private, fully proved helpers and proof
   imports. There are no change records or forced adaptations.
2. PASS: compiled the delivered file locally without errors or warnings. Scanned for
   forbidden declarations and sorries: none occur. A scratch copy with `#print axioms`
   reports only `propext`, `Classical.choice`, `Quot.sound`, and imported `sorryAx` for
   the public theorem; the private module adjunction has only the three permitted axioms.
   Read the direct-sum maps, both inverse laws, and both naturality proofs. They construct
   genuine linear morphisms and an adjunction, with no arbitrary witness or hollow data.
3. PASS: no statements are split off and no new holes or nodes are added. The helpers
   cover summand restrictions, the direct-sum universal property and sheafification.
   Empty indexing sets and zero sections are covered by the direct-sum zero and induction
   cases; no nonemptiness hypothesis is introduced.
4. PASS with repair: reviewed the exactness route through faithful exact forgetting,
   natural isomorphisms and Mathlib's additive exact-functor characterizations. Searched
   upstream and `lean/Sheaf` for module extension/restriction adjunction alternatives;
   found no applicable shorter existing module theorem. Proof-only added imports are
   plain imports. The unit `sk-def-sf-operations` has empty realized statement and steps;
   the unit route is preserved. Removed the stale restriction-adjunction wrapper node
   from the proof dependencies and documented it under No longer needed.
5. PASS after repair: compared the node changes with the repository. Only `proof`,
   `proof_deps` and `proof_origin` differ. The steps now match the direct linear Hom
   construction and exactness comparisons. Replaced the unused wrapper citation in
   Step 4 with the actual Mathlib adjunction and removed it from that step's uses.

Second reading changed DAG dependency pruning and corrected the report's claim that
specific imported theorem bodies still contain sorries. The Lean proof needed no repair.
One original hole is closed, no holes are added, and no modules are pruned.
