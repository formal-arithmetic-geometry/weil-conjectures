## What changed

Closed `AlgebraicGeometry.Etale.nonempty_higherDirectImage_forget_iso` without changing
its signature, universes, public imports, or definitions. The proof specializes the
already-proved canonical derived coefficient comparison to `F[0]`, then composes the
exact-forgetful homology comparison and the single-functor comparison. It works for
all integer degrees and arbitrary coefficient rings, including the zero ring.

Added the proof-only import
`Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison` and updated the
item node's proof, proof_deps, and proof_origin to the actual route. No new modules,
statements, definitions, or nodes. The unit record has empty realized statement/step
lists, and this specialization does not change the universal-datum unit's route.

Read the original statement, its node and unit, and the dependency signatures.
LeanFinder, Loogle, and grep searches were run through msearch. After a first complete
acyclic-resolution proof compiled, a broader derived-coefficient search located the
existing stronger comparison. That comparison's node, statement, and proof were read;
its arbitrary-ring and universe parameters match this item. Import-direction check
reported no cycle. Source proofs read online: Stacks Tags 03FD and 072W.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.nonempty_higherDirectImage_forget_iso`
(node `lem-sbc-higher-direct-image-forget-comparison`).

No sorry remains in the item, and no holes are added elsewhere (0 split off).
This is a proof from an existing proved derived-comparison declaration, not a
new decomposition. The final file compiles cleanly using lcompile.py.

## No longer needed

All seven original proof-only imports were removed:

- `Sheaf.AlgebraicGeometry.InjectiveModuleSheafHCohomology`
- `Sheaf.Paper.HigherDirectImageSheafifiedPresheaf`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`
- `Sheaf.AlgebraicGeometry.ModuleSheafConstantRingEquivalence`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The following original direct proof dependencies are removed from this node:

- `def-sp-injective-resolutions`
- `def-weil-pbc-direct-image` (its definitions remain available through public imports)
- `lem-sp-derived-functor-single-identification`
- `lem-weil-pbc-higher-direct-image-sheafified-presheaf`
- `lem-weil-pbc-injective-module-sheaf-H-acyclic`
- `lem-weil-pbc-module-sheaf-constant-ring-equivalence`
- `lemma-weil-pbc-leray-acyclicity`

These are removed as direct dependencies of this item. Several remain transitive
imports or proof dependencies of the reused derived-comparison module; this report
does not claim they have disappeared from the entire targets' import closure.
In particular, the global-H injective-acyclicity module is unnecessary for this
comparison: the existing derived comparison proves all-object evaluation acyclicity.
No additional original modules were present beyond the imports listed above.

## Where the brief, the DAG or earlier work was wrong

The original plan overlooked the already-proved
`AlgebraicGeometry.Etale.isIso_moduleAbelianDerivedLowerStarComparison` and its
`moduleAbelianDerivedLowerStarIso` wrapper in the source interface module above.
Its invertibility supplies the planned acyclic-resolution argument in full.
The original global-H acyclicity statement only concerns the terminal object;
the derived-comparison proof instead explicitly handles every etale object.
No statement error or target change was found. Zero and negative degrees require
no case split because the derived comparison and exact-functor homology
isomorphisms are indexed by all integers.

## Second reading by V3

1. **Visible changes and statements.** Compared the delivered module and node with
the repository versions. The theorem signature is byte-for-byte unchanged; only
the proof, its proof explanation, proof-only import, and node proof metadata differ.
No target or definition changed.

2. **Proof and axioms.** Compiled the module with `lcompile.py`, and compiled a
scratch copy with axiom probes. The theorem has no `sorry` in this module and uses
only the standard axioms plus `sorryAx` inherited from the existing derived
comparison dependency. No forbidden declarations, hollow definitions, or arbitrary
existence witness occur. `moduleAbelianDerivedLowerStarIso` is `asIso` of a fixed
canonical comparison whose `IsIso` proof is supplied by the dependency.

3. **New or split statements.** No new Lean declarations or split-off statements
were added, so there are no new truth or strength claims to discharge.

4. **Shortest route and pruning.** The proof directly specializes the existing
canonical derived coefficient comparison and composes the exact-functor homology
and single-functor isomorphisms. The removed imports and seven removed direct proof
dependencies are unused by this proof; the replacement dependency is exactly the
module imported by the proof.

5. **DAG and unit.** The node's changed `proof`, `proof_deps`, and `proof_origin`
match the Lean proof. The universal-datum unit has no realized statement or step
entry for this comparison, so its route is unchanged.

Changed nothing during this second reading beyond this report section.
