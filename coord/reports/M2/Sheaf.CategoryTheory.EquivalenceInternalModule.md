## What changed

Proved `CategoryTheory.equivalence_induces_internalModules` in
`Sheaf.CategoryTheory.EquivalenceInternalModule`, with its statement unchanged.
The construction transports the four operations by the stated comparison maps.
For generalized elements of an arbitrary target object, precompose by the counit
isomorphism and use fullness to reduce every module axiom to the corresponding
source axiom. The transport preserves and reflects operation-compatible maps,
so it defines a fully faithful functor. The counit preserves the transported
operations, giving essential surjectivity and hence the required equivalence.
The forgetful-functor equality and all five heterogeneous operation/map equalities
are definitional. All helper declarations are private and fully proved.

The original DAG route (step 1: transport operations, diagrams, and morphisms;
use the inverse equivalence and counit) is followed without introducing nodes.
No definitions or statements used by other modules were changed.

## Proved and sorry left

Proved: `CategoryTheory.equivalence_induces_internalModules`.

Unchanged sorry: `CategoryTheory.internalModules_finiteContAction`, node
`lem-pod-equivalence-induces-module-objects` (its step 2).
No new sorries were introduced. The source declarations defining the category of
internal modules and finite continuous actions retain their pre-existing proof
obligations; this delivery does not modify those modules.

## No longer needed

Removed redundant direct imports `Mathlib.CategoryTheory.Adjunction.Limits`,
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts`, and
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal`. They remain available
transitively through the retained public imports. No DAG nodes or modules are pruned.
No DAG dependencies were bypassed.
The imported internal-module and finite-continuous-module definitions are needed
for the two statements. Adjunction limits supply preservation by equivalences;
the product and terminal preservation imports supply the invertibility of their
comparison maps. No new modules or nodes are needed for the first theorem.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. Step 1 of the node describes the route used.
The generalized-element axioms require reducing an arbitrary target test object
through the counit, not merely applying the functor to source generalized elements;
the proof implements that reduction explicitly. The finite continuous action
identification in step 2 remains for a later worker.

## Second reading by M2

1. Compared the complete module against the repository version. Both existing theorem
   signatures and docstrings are byte for byte unchanged. All added helpers are private;
   no existing definition changed. Verdict: pass.
2. Compiled the complete file locally without errors or warnings. The only local sorry
   is the unchanged `CategoryTheory.internalModules_finiteContAction`. No forbidden
   declaration or hollow definition occurs. Scratch `#print axioms` for both public
   theorems gives only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`;
   the first theorem inherits the open `InternalModule.isHom_id/isHom_comp` category
   proof obligations. Verdict: pass relative to the existing open dependencies.
3. No statements were split off and no new public statements or nodes were added.
   Checked all private helpers: comparison maps commute with pairing, transported
   morphisms preserve and reflect all four operations, the counit preserves them,
   and inverses of compatible isomorphisms are compatible. The argument works for
   arbitrary rings (including the zero ring) and arbitrary test objects, using the
   counit isomorphism and fullness rather than assuming every object is an image.
   Independent search for `InternalModule|mapCommGrp|mapMod` and library search found
   no exact existing transport theorem: CommGrp handles groups and Mod handles a
   monoid object, not this external-ring InternalModule. Verdict: pass.
4. Read the proof downward from the main theorem. Full faithfulness plus essential
   surjectivity gives the required equivalence with definitionally the prescribed
   underlying functor and operations. No shorter applicable existing result found.
   Tested each Mathlib import removal and their joint removal; compilation succeeds.
   The two Sheaf imports are required by the statements. The old proof_deps is empty,
   so no nodes are bypassed. The unit sk-lem-finite realized fields are unchanged;
   this auxiliary node is not one of their realizations. Verdict: pass after cleanup.
5. Read the existing node's two proof steps, empty proof_deps, source proof_origin,
   and lean record. The delivered proof implements precisely step 1; step 2 remains
   open as reported. No node update is necessary. Verdict: pass.

Changed only the import list and report: removed three redundant direct public
Mathlib imports. Recorded the removal and downstream effects in
`coord/changes/EquivalenceInternalModule-redundant-imports.md`. No proof repair needed.
