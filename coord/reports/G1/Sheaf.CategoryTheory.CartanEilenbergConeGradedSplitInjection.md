## What changed

Completed `CategoryTheory.Functor.cartanEilenberg_cone_graded_split_injection` in
`lean/Sheaf/CategoryTheory/CartanEilenbergConeGradedSplitInjection.lean`, preserving its
signature, visibility, original docstring, and public imports.

Two proved private helpers implement the existing node's plan: lift the retained
column-cone summands into step p; and project the ambient cone onto the retained column,
annihilating step p+1. The two step lifts are constructed directly with Mathlib
`factorThruImageSubobject`, `Subobject.ofLE`, and `Subobject.underlyingIso`. The lift
uses the finite image supremum or the zero source when the column is outside the interval.
The projection uses the total coproduct and cone biproduct. The identity-functor extension
isomorphism is included explicitly; its components are not treated as definitional equalities.

The final proof descends the projection through the evaluated cokernel using
`PreservesCokernel.iso` and `cokernel.desc`. Cone extensionality proves the left-inverse
identity, with zero-source arguments for the missing summands. The requested normalized
lifts are the column-cone coprojections followed by the step lift. All objects and maps
are constructed using proved Mathlib universal properties; no unproved witness is chosen.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.Functor.cartanEilenberg_cone_graded_split_injection`
(blueprint: `lem-sp-cartan-eilenberg-cone-graded-split-injection`).

The two private helpers `cartanEilenberg_cone_retained_lift` and
`cartanEilenberg_cone_retained_projection` are also fully proved. No `sorry` remains in
the delivered module, and no holes are added elsewhere. This is a proof, not a decomposition.

Single-file compilation with the required `lcompile.py` succeeds without warnings.
The delivery dry run checks the axioms of every declaration.

## No longer needed

None of the original imports, proof-dependency nodes, or modules is pruned. The proof
implements the original retained-column construction directly from definitions and Mathlib.
The two temporary helper modules used during development have been consolidated into
proved private helpers and are absent from the delivery. No new nodes are required.
The unit statement and its realized steps are untouched. The duplicate private helper
`CategoryTheory.Functor.lift_of_image_le` has been removed; no import of
`Sheaf.CategoryTheory.CartanEilenbergConeGradedHomExt` is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The earlier sandbox attempt contained only the
original sorry statement and search log. The identity functor on complexes, its extension,
and the degreewise cokernel identification require explicit isomorphisms in Lean.
The edge cases m=p-1, negative extended degrees, p<b, and empty finite intervals are
handled in the proof. Neither a compatibility between aug and a nor surjectivity of the
constructed injection is used or asserted.


Repair of the return at head 109ab3661: the added private `lift_of_image_le`
duplicated the helper in `CartanEilenbergConeGradedHomExt`. That existing helper is
private and cannot be used by importing its module. Removed the duplicate entirely,
and replaced both applications with explicit Mathlib image-factorization maps and
Mathlib simplification of their composites. No replacement theorem states the same
fact, no existing module is adapted, and no signature or public import changes.
The previous second reading predates this repair and has been removed so the next
reader can review the repaired version.

## Second reading by G1

1. Interface: PASS. Compared the sole delivered module with the repository by
   `diff` and checked the existing theorem signature byte for byte with a script.
   Its signature, visibility, original docstring, and all three public imports
   are unchanged. There are no definition changes or forced adaptations. The
   only added declarations are two proved private proof helpers.
2. Proof: PASS. Independently compiled the delivered module with `lcompile.py`
   without errors or warnings (6.5 seconds). A fresh scratch copy compiled with
   `#print axioms` for the public theorem and both private helpers: each uses
   exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   The delivered module contains no `sorry` or forbidden axiom/implementation
   commands. The image factorizations, total coproduct projection, and evaluated
   cokernel descent are actual constructions using proved Mathlib properties.
   The witnesses extracted from the private helpers come from fully proved
   existential theorems, never from an unproved existence assertion.
3. Auxiliary statements: PASS. No statements were split off and no new holes
   or nodes were added. Read both private helper statements and their proofs.
   The lift asserts only ambient normalization; the projection asserts only
   normalization and annihilation of step p+1. Checked m=p-1, m>=p, p<b, and
   empty finite intervals. For p<b the retained resolution object is zero;
   the source object is also zero when m+1=p by the original K-vanishing
   hypothesis. The proof does not require aug to arise from a, since the claim
   is degreewise and the cone object is a biproduct. No epicity is claimed.
4. Route and pruning: PASS. Searched the library and Mathlib with different
   wording using `rg`, Loogle (`CategoryTheory.Limits.cokernel.desc`), and Lean
   Finder (a projection killing the denominator and retracting a lift). The
   results supply the universal properties already used, not a shorter
   normalized retained-column construction. The former duplicate private
   image-lifting lemma is absent. All imports provide names in the public
   signature: mappedFunctor, filtration/subquotients, and mappingCone. None
   is proof-only. All four old proof dependencies remain used, so
   `## No longer needed` is complete. Read the unit record; its realized fields
   are unchanged, and this below-unit proof bypasses no realized unit step.
5. DAG: PASS. Read the item's node and compared its proof, proof_deps, and
   proof_origin with the Lean argument. The recorded retained-column
   projection, finite-image lifting, quotient descent, and biproduct identity
   are precisely the implemented route. All listed dependencies are used.
   No DAG or statement correction is needed.

Second reading changed only this report: added the independent five-point
review and its compilation/axiom evidence. The repaired Lean proof is retained
without further edits. Confirmed one original hole closed, zero holes added,
zero split-off statements, and no pruned imports, nodes, or modules.
