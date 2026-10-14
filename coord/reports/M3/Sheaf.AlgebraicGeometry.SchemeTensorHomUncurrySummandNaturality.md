## What changed

Proved `AlgebraicGeometry.schemeTensorHomUncurry_summand_naturality` without changing
its signature or visibility. Added three proved private helpers: functor identity
cancellation, abstract tensor-Hom naturality, and an explicit component formula.
The slow definition is `CategoryTheory.homComplexFunctor`, whose chosen existence
specification was being reduced repeatedly. Marked it locally irreducible while
using its projection API; temporarily restored its ordinary transparency only to
prove the component formula by reflexivity. No shared definition or importer API
changes. No imports added or removed. The theorem has a scoped heartbeat setting;
the 60-second wall-clock limit is unchanged.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.schemeTensorHomUncurry_summand_naturality`
(node `lem-pc-scheme-uncurry-summand-naturality`). Added zero holes and left zero
holes. All three private helpers are proved. This is a proof, not a decomposition.

## No longer needed

No imports removed. The wrapper node `lem-pc-sheaf-modules-tensor-closed` and its
module `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed` are not used directly:
the existing `SheafOfModules.tensorHomEquiv` naturality lemmas suffice. This does
not assert that the wrapper is absent from other targets' import closures.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox contained a partial proof with an internal sorry. Replaced
it with the complete calculation. The reported importer named the item itself;
its public signature is preserved. The actual direct importer is
`Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationTripleComponent`; it needs no
adaptation: its unchanged source compiled against the repaired module in 11.5 s.
Expensive rewriting with transparency disabled unfolded the chosen
Hom-complex construction. Explicit equations and local irreducibility avoid it.
The original component definition is preserved; an attempted shared-definition
edit was discarded. No hollow definitions, axioms, or new nodes.

Change record: `coord/changes/scheme-uncurry-local-transparency.md`.

## Second reading by M3

1. Compared the delivered Lean module and node against the repository with diff.
   Restored the extra space before `:=` in the theorem declaration; its complete
   existing signature is now byte-for-byte identical. Visibility, definitions,
   docstring and both public imports are unchanged. All additional declarations
   are proved private helpers. No consumer or shared definition is edited.
2. Read the complete proof and all three helpers. The component equation reduces
   the outer inclusion; functor identity cancellation specializes projection
   naturality, and injectivity of tensorHomEquiv proves the source/target
   naturality calculation after braiding naturality. The module compiled without
   errors or warnings in 42.6 seconds. No forbidden declarations, internal holes,
   or definitions with postponed data occur in the delivered source. Independent
   scratch axiom and unchanged-importer checks are recorded below.
3. There are no split-off statements, new public statements, new nodes or new
   holes. Each private helper is proved and strictly smaller than the item.
   The argument uses only categorical equalities and integer index equalities,
   so zero complexes, zero maps, negative degrees and the empty scheme impose
   no missing hypotheses.
4. Searched the library for inverse tensor-Hom naturality and evaluation
   factorization, and independently queried Loogle for
   `tensorLeftHomEquiv_symm_naturality`: that rigid-category result requires
   an exact pairing, which arbitrary module sheaves do not have. Existing
   tensorHomEquiv naturality is already the short route used here. Both imports
   are required in the public signature. The sole removed proof dependency is
   lem-pc-sheaf-modules-tensor-closed, named above; there is no direct import of
   its wrapper to remove. Neither it nor this item is a realized unit statement
   or step in dag/units. The unit route and realized record are unchanged.
5. The node diff changes only proof, proof_deps and proof_origin. The two retained
   dependencies name exactly the component/differential and projection APIs
   used in Lean; the removed wrapper is replaced by the existing upstream
   tensorHomEquiv API, as the proof text records. No new-node fields are needed.

Second reading changed only the extra signature whitespace and this review
record. The mathematical proof and its private helpers were retained.

Independent scratch verification: the repaired module compiled in 39.9 seconds;
`#print axioms` for the theorem, map_id_app_comp, uncurry_natural and
component_formula printed exactly propext, Classical.choice and Quot.sound,
with no sorryAx. The repository's unchanged
Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationTripleComponent compiled against
that scratch module in 16.4 seconds. Verdict for points 1--5: pass.
