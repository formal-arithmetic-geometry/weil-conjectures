## What changed

Proved AlgebraicGeometry.Scheme.scalar_unit_abelian_ext_factorization in
Sheaf.AlgebraicGeometry.ScalarAbelianExtFactorization without changing its signature,
definitions, or existing docstrings. Added proof-only imports of
Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisExtFunctorSquare and
Sheaf.CategoryTheory.ExtExactFunctorIdentityComparison.
The proof evaluates the forgotten scalar-unit class at 1 via the constant-sheaf
adjunction, identifies the two exact-functor Ext maps, and combines the equalities
using Yoneda associativity. Updated the existing node's proof and proof dependencies.

## Proved and sorry left

Closed the sole hole: AlgebraicGeometry.Scheme.scalar_unit_abelian_ext_factorization
(blueprint: new-sc-scalar-abelian-ext-factorization). No sorry remains in the item's
module, and no holes were added. This is a complete proof, not a decomposition.
The imported definitions still depend on existing upstream open statements; those
were neither modified nor proved in this delivery.

## No longer needed

None. All original imports are needed by the definitions or statements, and both
new proof imports supply used theorems. All original proof-dependency nodes remain
used; no modules or nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan correctly described the argument. Its dependency list omitted the
identity exact-functor comparison needed to eliminate the identity Ext map after
applying the square theorem. Online Loogle lists comp_mapExactFunctor and
id_mapExactFunctor, but these are absent from the pinned Mathlib source. The existing
proved exactFunctorIdentityComparison supplies the needed identity. It is a generic
closed tool from another unit and does not replace any step of the cube unit's route.
The square theorem already permits independent Ext universes; the more restricted
exactFunctorCompositionComparison is unnecessary. No statement or definition was wrong.

## Second reading by U4

1. Compared the sole delivered Lean module with the repository version and checked
   the declaration table. Every existing signature, definition, visibility and
   docstring is unchanged; the only Lean changes are the theorem proof and two
   plain, proof-only imports. No change record or forced adaptation is needed.
2. Compiled the module locally with lcompile.py: no errors or warnings. Inspected
   its whole body: no sorry, axiom, unsafe, opaque, implemented_by or extern, and
   no hollow definition or arbitrary existence witness. Scratch #print axioms
   checks show only propext, Classical.choice and Quot.sound for the three
   public definitions; the theorem additionally has sorryAx from existing open
   upstream dependencies, as permitted by the brief. The scalar unit is
   constructed by the adjunction; scalarCohomologyExtEquiv wraps an explicit map
   using its bijectivity theorem, which determines its inverse uniquely.
3. No statements were split off and no nodes or holes were added. The unit
   evaluation uses map_one and adjunction identities without a nonvanishing
   hypothesis, so empty schemes and zero classes pose no exception.
4. Read the proof downward, searched pinned Mathlib Ext.Map and the library for
   composition and identity alternatives, and independently ran msearch grep.
   The available Mathlib mapExactFunctor_comp concerns Yoneda composition, not
   composition of functors; the existing square and identity comparison are the
   appropriate tools. Both added imports are plain and used. All three original
   proof dependencies remain used, so No longer needed is complete. The unit
   sk-prop-av-cube has empty realized statement/step lists in the current record;
   this proof retains the specified factorization route and bypasses no recorded
   realization. No unit record was changed.
5. Compared the old and delivered node and read each dependency declaration.
   Its three proof steps match the local hunit calculation, hmap calculation,
   and final Yoneda rewrites. proof_deps is exactly the union of their uses,
   including the added identity-comparison node. proof_origin accurately records
   the argument. No new node fields need review.

Second reading changed only this report; the Lean proof and DAG were correct.
