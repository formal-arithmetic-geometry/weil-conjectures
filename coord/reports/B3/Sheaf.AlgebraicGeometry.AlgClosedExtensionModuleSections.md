## What changed

Proved `AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_algClosed_extension` by reducing the module-valued unit to the underlying set-valued unit and applying `etale_sections_base_field_extension`. Added the strictly smaller canonical coefficient comparison theorem `AlgebraicGeometry.Etale.isIso_upperStar_forget_comparison`, proved from filtered Kan-extension preservation, sheafification preservation, and the adjunction unit factorization. Added the corresponding DAG node and updated the target node proof dependencies.

## Proved and sorry left

Closed one existing hole: `AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_algClosed_extension` (node `lem-sc-algclosed-extension-module-sections`). Added zero holes. The new `AlgebraicGeometry.Etale.isIso_upperStar_forget_comparison` is proved outright, so it is not a sorry split-off. Both delivered modules contain no `sorry`. Existing imported theorem `AlgebraicGeometry.etale_sections_base_field_extension` remains a sorry-backed dependency in its own module; the main theorem is a checked reduction to that existing input, not yet a theorem with only the three standard axioms.

## No longer needed

The previous proof-plan imports `Sheaf.AlgebraicGeometry.EtaleSheaves` and `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` are replaced by the direct coefficient-comparison module and the existing sections module. The node `def-weil-pbc-etale-sheaves` and its module are unnecessary to this proof; no constructibility or locally constant definitions enter it. `def-weil-pbc-inverse-image` is retained through the new comparison node. The removed direct import of `UpperLowerStar.Defs` is redundant because both public statement imports already expose it. The new comparison's redundant proof import `Mathlib.CategoryTheory.Functor.KanExtension.Preserves` was also removed after compiling successfully without it. This does not claim that the pruned modules are globally unreachable from other targets.

## Where the brief, the DAG or earlier work was wrong

The original plan omitted the concrete categorical comparison needed to pass from module sheaves to set sheaves. The missing comparison is now proved, including compatibility with the actual adjunction unit, rather than assuming an arbitrary comparison isomorphism respects the unit. No mathematical error or changed statement was needed. The unit record has no realized nodes for this item, and the original geometric route through sections invariance is retained.

The new theorem was checked for arbitrary (including zero) rings, arbitrary morphisms and empty schemes: filtered base-change comma categories and the canonical comparison identities impose none of the excluded geometric or coefficient assumptions. Consequently n=0 and n=1 in the main theorem are covered. Mathlib searches ran through LeanFinder, Loogle and grep; LeanSearch returned an Internal Server Error, recorded as unavailable. A whole-blueprint search for `forget inverse image` returned no matching node. The existing module-to-abelian-group comparison is insufficient for sets and does not state compatibility with the unit. Both delivered modules compile in import order with no warnings. The dry run also runs axiom probes; current deliver3.py disables individual server compilation by default, and the global batch build verifies the delivery; the main theorem remains dependent on the previously stated set-valued invariance theorem.

## New nodes

`lem-sc-etale-module-set-pullback-comparison` records the coefficient-forgetting inverse-image comparison and its complete Lean proof. Its proof uses the existing inverse-image definitions and Mathlib's canonical Kan-extension and sheafification comparison identities.

## Second reading by B3

1. **Visible interface: pass.** Compared the existing module with the repository using
   `diff -u`. Its sole theorem signature and existing docstring are byte for byte
   unchanged. Only the proof and two plain proof imports differ. No definition,
   existing statement, or public import is changed; no change record is needed.
2. **Proof: pass as a reduction to the existing open geometric theorem.** Compiled
   both delivered modules in import order with lcompile.py, with no errors or
   warnings. Scanned the delivered sources: no sorry, axiom, unsafe, opaque,
   implemented_by, extern, or hollow definition. Scratch-copy `#print axioms`
   checks show that the private unit-expansion helper and the new comparison use
   only propext, Classical.choice, and Quot.sound. The main theorem additionally
   uses sorryAx through the existing set-valued sections theorem. Read the actual
   hom-equivalence calculation: apply_symm_apply identifies the forgotten module
   unit with the set unit followed by the comparison, not just some arbitrary
   isomorphism. The terminal-object naturality argument then proves invertibility
   of the precise globalSectionsUpperStarMap in the original signature.
3. **New statements: pass.** No new open statement is split off. The fully proved
   comparison concerns arbitrary rings and scheme morphisms, rather than
   restating field-extension sections invariance. Checked zero rings, identity
   maps, empty schemes, and n=0/1: filtered colimit preservation and the two
   canonical comparison identities need no nontriviality or finiteness assumption.
   Read Stacks 0A3I, 03D3 and 03D7; 0A3I supplies precisely the existing geometric
   input, while the canonical compatibility calculation is supplied by the Lean
   proof and Mathlib's comparison APIs. Searched with the alternative LeanFinder
   query about representably flat site functors and with Loogle
   `"sheafCompose", "IsIso"`, plus rg across Lean and Mathlib. The existing
   EtalePullbackForgetModules and EtaleModulePullbackForgetNaturality results
   concern abelian groups, not sets; SitePullbackAbelianUnderlying is open and
   uses small categories. None replaces this canonical set comparison with its
   unit identity. No shorter complete route was found.
4. **Route and pruning: pass.** The proof follows the original degree-zero route
   through set-valued sections invariance; it adds no alternate geometric route.
   Read sk-thm-vanishing.json: its realized statement and step arrays are empty,
   and no realized unit node is bypassed. Every old proof dependency is accounted
   for under No longer needed: sections invariance stays, inverse-image definitions
   remain through the comparison, and def-weil-pbc-etale-sheaves is pruned from
   this proof. Public imports support the displayed signatures and their required
   coefficient instances; PreservesSheafification and both geometric/comparison
   inputs used only by the main proof are plain imports.
5. **Nodes: pass after repair.** The existing node changes only its proof,
   proof_deps, proof_origin and lean record. The proof steps match the actual
   comparison, sections-invariance application and terminal transport. The new
   node has the required source, searches, provenance, blueprint ancestry, chapter,
   unit and Lean record. Its proof dependencies are exactly the union of its step
   uses. Replaced the new node's flattened lean.statement with the exact multiline
   theorem signature from the delivered module, as the contract requires.

Second reading changed the new node's verbatim Lean signature and the report's
hole accounting and compile description. No Lean proof required repair.
