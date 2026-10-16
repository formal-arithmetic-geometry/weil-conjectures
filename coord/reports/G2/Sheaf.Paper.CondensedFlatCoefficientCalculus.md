## What changed

Completed `AlgebraicGeometry.ProEtale.condensedCoefficientCoherence`, preserving all four
public theorem signatures and the specified comparison maps and shift structures. Its eight
clauses now follow from proved private associativity, unit, and shift lemmas for derived
scalar extension. These specialize the existing adjunction-uniqueness and localization
transport helpers; no new mathematical obligation is introduced.

Factored the two existing exact coefficient calculus proofs through a fully proved generic
`scalarCalculus` lemma. It accepts the chosen derived categories and obtains the derived
adjunction by deriving the scalar adjunction and transporting along the exact restriction
comparison. Private canonical module-structure caches have local instance registrations only
inside the generic helper section; public proof bodies introduce the same canonical data
caches locally. `Mod.extendScalars` is locally irreducible while matching
its proved comparison API. These changes avoid repeatedly elaborating resolution structures.

Reused the source library's finite-basis and scalar-transport constructions via proof-only
`import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`.
The finite-free proof still chooses an actual finite field basis and proves continuity of
its coordinate maps; source `continuousBasisSheafIso` and `mapFreeRestrictedRegularIso`
replace duplicate private constructions. Updated the existing node's proof and proof_origin.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.condensedCoefficientCoherence`
(node `lem-weil-pbc-condensed-flat-coefficient-calculus`).

Holes closed: 1 of 1. Holes added: 0. Split-offs: 0. There are no sorries in the delivered
module, and every added private helper is proved. All other public theorems remain proved.
Existing imported obligations remain with their source modules.

## No longer needed

Removed proof-only imports:
- `WeilConjectures.CategoryTheory.ModuleObjects.MapMod` (available through Compatibility).
- `Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete` (the duplicated
  presheaf construction was removed).

Removed duplicate private helpers `fieldPresheaf`, `postcompLinear`, `presheafCoordinate`,
`presheafVector`, `presheaf_basis_iso`, `map_preserves_free`, `restrictedRegularIso`, and
`transport_free`. No entire module or further DAG dependency is pruned; the node's existing
four proof dependencies remain needed. No new node or split-off is needed.

## Where the brief, the DAG or earlier work was wrong

The earlier node accurately identified the remaining concrete coherence specialization.
Its compile-time obstruction is addressed by generic instance caches, explicit derived
category parameters, and reuse of the already proved source constructions. No definition or
public statement change, forced adaptation, or change to the blueprint unit route is needed.

The static interface checker reports local attributes and generic variable sections as
commands; their proof-only scope is documented in
`coord/changes/G2-condensed-coherence-local-structures.md`.

## Second reading by G2

1. **Signatures and accidental changes — pass.** I compared the delivered module with the
   repository version. All four public theorem signatures, definitions, comparison maps,
   and shift structures are byte-for-byte unchanged. The import changes and the node proof
   metadata are declared above and in the change record.

2. **Proof and axioms — pass.** The module compiles with the required launcher and contains
   no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or hollow definition.
   The completed coherence theorem uses only the permitted foundational axioms through its
   proved helpers; imported obligations are unchanged.

3. **Split statements — pass.** No statements were split off and no new node was added.
   The completed theorem is not replaced by a restatement, and the reused source helpers
   are existing declarations rather than duplicate local obligations.

4. **Shortest route and pruning — pass.** The generic scalar calculus and derived coherence
   helpers close the original hole directly using existing adjunction, localization, and
   shift APIs. The duplicate finite-basis and scalar-transport helpers were removed, and
   the two unused proof-only imports were removed. The unit route remains intact.

5. **DAG agreement — pass.** The node's proof steps, proof dependencies, and proof origin
   were updated to match the source-library finite-free constructions and the completed
   scalar coherence proof. No unit realization was changed.

I changed only the report by adding this second-reading record; the module and DAG changes
   described above are mathematically sound and ready for delivery.
