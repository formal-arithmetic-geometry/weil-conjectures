## What changed

Repaired the returned delivery by removing the import of
`Sheaf.AlgebraicGeometry.OrdinaryHigherImageQuasiCoherent`, which created the reported cycle through
`AffineMorphism` and `FiniteFreeComplex`. The quasi-coherence theorem is temporarily split off as a
named `sorry` with a matching node; the other two original holes remain proved with their existing
acyclic imports and proofs.

## Proved and sorry left

Proved:

- `AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_restrict`.
- `AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_restrict`.

Sorry left:

- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage`, recorded by
  `lem-pc-sections-higher-direct-image-quasi-coherent`.

No other holes were added.

## No longer needed

Removed import: `Sheaf.AlgebraicGeometry.OrdinaryHigherImageQuasiCoherent`. Its theorem cannot be
imported here because it reaches this module through the reported cycle.

## Where the brief, the DAG or earlier work was wrong

The previous proof imported `OrdinaryHigherImageQuasiCoherent`, but that module transitively imports
`AffineMorphism`, whose `FiniteFreeComplex` dependency reaches the Sections module through the
ProperFlat chain. This made the delivered import graph cyclic. The quasi-coherence proof must be
landed separately or supplied from an acyclic lower-level module.

## New nodes

`lem-pc-sections-higher-direct-image-quasi-coherent` records the temporarily split theorem and its
required ordinary higher-image dependency. `lem-pc-higher-direct-image-local-vanishing` records the
proved local vanishing theorem. `lem-pc-sections-open-base-change` records the proved
open-base-change theorem.

## Earlier second reading (a previous round; superseded)

The cycle is removed from the delivered import graph, and the module compiles. The two completed
proofs retain their original statements and imports. The remaining quasi-coherence hole is named and
has a matching DAG node; it is strictly below the affine-sections theorem and can be proved by a
future acyclic ordinary higher-image module.


## Second reading by Q1

1. **Interface comparison.** Compared the delivered module with the repository version. All existing declaration signatures are unchanged byte for byte; the only interface-level additions are proof-only imports and private helpers. Verdict: pass.

2. **Proof and axioms.** Compiled `Sections.lean` with `lcompile.py`. The only remaining `sorry` is the named theorem `isQuasicoherent_higherDirectImage`; no forbidden declarations occur. The scratch axiom check shows the two completed public theorems use only the permitted library axioms (the quasi-coherence theorem necessarily retains `sorryAx`). Verdict: pass.

3. **Statements and nodes.** Checked the three Q1 node statements against their Lean declarations, including the open-base-change and local-vanishing special cases. The statements are true and unchanged, and the quasi-coherence split has its source, proof description, and matching node. Verdict: pass.

4. **Pruning and route.** The proofs use the shortest available local APIs: the coefficient-independent local bound, injective-resolution restriction, and the explicit pushforward square. The ordinary higher-image import that caused a cycle is absent; the remaining proof dependencies and unit route are recorded in the nodes. Verdict: pass.

5. **Delivery metadata.** Node `proof`, `proof_deps`, and `proof_origin` agree with the Lean proofs, and the report lists the one hole left and the two holes closed. Verdict: pass.

Changed during this reading: appended this review record only. No proof repair was needed after compilation.
