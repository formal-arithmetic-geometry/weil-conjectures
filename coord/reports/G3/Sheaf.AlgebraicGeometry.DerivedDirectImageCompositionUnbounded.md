## What changed

Proved `AlgebraicGeometry.derivedDirectImageComposition` without changing its signature,
universes, instances, or visibility. The proof specializes
`AlgebraicGeometry.RingedSpace.exists_derivedModuleDirectImageComposition` to the underlying
ringed-space morphisms, extracts the canonical comparison and takes its inverse. Both
`schemeDerivedDirectImage` and forgetting composition reduce definitionally to the
ringed-space expressions. The imported theorem pins its comparison by the right-derived
unit equation, so this is the canonical comparison in the node, specialized to schemes.

Replaced the two proof-only imports `DerivedAdjoint` and `DerivedPullbackComposition` with
`RingedSpaceDerivedDirectImageComposition`; both public imports stay unchanged. Updated
only the existing node's `proof`, `proof_deps`, and `proof_origin` to this route.
The unit `sk-thm-picard-semicon` has empty realized statement and step lists. This
specialization changes no unit statement or realized step.

Removed the unused `RightAdjointComposition` module and its new node from the earlier
attempt, together with its scratch probes. These were never needed for the specialization
and are not part of this delivery.

## Proved and sorry left

Closed the only hole in the item:
`AlgebraicGeometry.derivedDirectImageComposition`
(node `lem-pc-derived-direct-image-composition`). No sorry remains in the delivered module.
No holes added or split off, no new declarations, and no definitions changed. This proves
the item from an existing library theorem; it does not claim that all transitive
geometric dependencies are already free of sorry. The single-file compile passed without
warnings using `lcompile.py`.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.DerivedAdjoint` and
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition`. The old proof dependencies
`lem-pc-ringed-spaces-derived-adjoint`,
`lem-pc-ringed-spaces-derived-pullback-composition`, and
`lem-cat-right-adjoint-composition` are not used by this scheme-level proof. Replaced them
in the node by `lem-pc-ringed-spaces-derived-direct-image-composition`.

The following modules and their recorded nodes leave this item's import closure.
This is local pruning; other target branches may still use them.

| Module | Recorded nodes |
|---|---|
| `Sheaf.AlgebraicGeometry.DerivedAdjoint` | `lem-pc-ringed-spaces-derived-adjoint` |
| `Sheaf.AlgebraicGeometry.DerivedPullback` | `def-pc-derived-pullback` |
| `Sheaf.AlgebraicGeometry.DerivedPullbackComposition` | `lem-pc-ringed-spaces-derived-pullback-composition` |
| `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionAssocKFlat` | `lem-pc-derived-pullback-assoc-kflat` |
| `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionCoherence` | `lem-pc-derived-pullback-comparison-coherence` |
| `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionIsIso` | `lem-pc-derived-pullback-comparison-is-iso` |
| `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionUnitKFlat` | `lem-pc-derived-pullback-unit-kflat` |
| `Sheaf.AlgebraicGeometry.InverseImageExactKFlat` | `lem-pc-inverse-image-exact-kflat-resolution` |
| `Sheaf.AlgebraicGeometry.TensorPullback` | `lem-pc-module-pullback-identity-composition`, `def-pc-module-pullback` |
| `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction` | `lem-pc-module-pullback-adjunction` |
| `Sheaf.AlgebraicGeometry.TensorPullbackKFlatQuasiIso` | `lem-pc-tensor-pullback-kflat-quasi-iso` |
| `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors` | `lem-pc-derived-adjoint-functors` |
| `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd` | `def-pc-essentially-constant-ind-diagram` |
| `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantIndHomColimit` | `lem-pc-essentially-constant-ind-hom-colimit` |
| `Sheaf.CategoryTheory.LocalizationHomColimit` | `lem-pc-left-localization-hom-colimit` |
| `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral` | `lem-pc-pre-derived-adjoint-functors-general` |
| `Sheaf.CategoryTheory.RightLocalizationHomColimit` | `lem-pc-right-localization-hom-colimit` |

The earlier attempt's new `Sheaf.CategoryTheory.RightAdjointComposition` and node
`lem-cat-right-adjoint-composition-codex` are also omitted entirely.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt correctly found that the scheme derived-pullback adjunction uses a
single shared derived-category universe, while this theorem has three independent
universes. That mismatch is not a blocker: the existing ringed-space composition theorem
already supports those independent universes and gives precisely the stronger canonical
comparison needed. No universe generalization or extra intermediate theorem is necessary.
The old node's coherence step asserted more than the Lean Nonempty statement requests;
canonicity here follows from the existing comparison's right-derived unit characterization.

## Second reading by G3

1. Compared the complete delivered module and node with the repository copies. The sole
   theorem signature, all universe and instance binders, visibility, and both public
   imports are byte-for-byte unchanged. There are no definition changes or new declarations.
   Restored the original theorem docstring, leaving the new route explained in this report
   and the node rather than changing existing documentation.
2. Independently compiled the delivered module with lcompile.py: no errors or warnings.
   Compiled a scratch copy with `#print axioms AlgebraicGeometry.derivedDirectImageComposition`:
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is inherited
   from existing open dependencies; the delivered proof has no sorry or forbidden construct.
   The proof eliminates an existential inside a proposition, and constructs no data from
   arbitrary existence. Inspected the ringed-space theorem and the scheme abbreviation:
   inversion gives the requested orientation and composition is definitionally preserved.
3. No statements, holes, modules, or nodes are split off. No duplicate declaration is added.
   Searched the source for derived-composition results and repeated a Mathlib grep search
   for `rightDerivedFunctorComp|derivedModuleDirectImageComposition`: generic localization
   comparison results do not shorten the existing three-line specialization.
4. The direct specialization is the shortest applicable route found. Its only new import
   is proof-only; the two original public imports are retained. Compared transitive source
   import closures: the 17 project modules listed above disappear locally. Corrected the
   report by removing its erroneous claim that `Mathlib.CategoryTheory.Limits.Types.Colimits`
   disappears. All three old proof dependency nodes are listed as unused. The unit
   `sk-thm-picard-semicon` has no realized statement or step nodes; no unit route is bypassed.
   The generic ringed-space theorem is used as a tool, without replacing a unit result.
5. Compared node JSON fields: only `proof`, `proof_deps`, and `proof_origin` change.
   The two steps match the actual specialization and inversion, and their dependency union
   is exactly `lem-pc-ringed-spaces-derived-direct-image-composition`. No new node records
   or change records are required. The node statement and Lean record remain unchanged.

Second-reading changes: restored the existing docstring, corrected the pruning report,
and added this independent review. The proof and node route required no repair.
