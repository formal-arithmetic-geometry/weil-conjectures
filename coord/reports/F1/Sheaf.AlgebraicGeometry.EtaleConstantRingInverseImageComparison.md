## What changed

Proved `AlgebraicGeometry.etaleConstantRingInverseImageComparison` in its original module,
without changing its signature or definitions. Added the proof-only import
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf` for the direct-image/sections
comparison. The existing public import is unchanged.

The proof follows the node's three steps. Obtain the compatible algebraic lifts from
`etaleInverseImageAlgebraicStructures`. Compose its ring adjunction with the constant-sheaf
adjunction on V and identify the right adjoint with sections at the pulled-back terminal
object. Compare with the constant-sheaf adjunction on U using `Adjunction.leftAdjointUniq`.
Its hom-equivalence equation gives the formula on constant sections at the terminal object;
naturality of the sheafification units and the adjunct gives the formula at every object.
Finally, apply the lift's pointwise identity equations for the direct-image comparisons to
remove those comparisons from the ring and abelian hom-equivalence equations.

## Proved and sorry left

Proved the module's one previously unproved theorem,
`AlgebraicGeometry.etaleConstantRingInverseImageComparison`
(node `lem-weil-pbc-constant-ring-inverse-image-comparison`).
No `sorry` remains in the delivered module. No intermediate theorem or new module is added.
The proof uses the existing algebraic-lift declaration; its transitive unfinished dependencies
remain existing project items. This delivery does not claim to close those dependencies.

Local single-file compilation passes. The required delivery dry run checks compilation,
axioms, unchanged signatures, and delivery shape.

## No longer needed

None. No imports are removed and no planned dependency is pruned. The mathematical route
of the node is retained, with uniqueness of left adjoints implementing the planned Yoneda
comparison. The unit `sk-def-exchange` has no proof steps bypassed by this delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The terminal object after base change need not be identified
with a chosen terminal object of U's etale site: using `constantSheafAdj` at its terminal
image avoids an unnecessary object equality. The direct-image comparison isomorphisms
provided by the algebraic-lift theorem are arbitrary witnesses, so their pointwise identity
properties must be used when deriving the requested compatibility equations.

## Second reading by F1

1. Compared the complete delivered module with the repository version using `diff` and
   independently compared the theorem signature byte for byte. PASS: only the proof body
   and one plain proof-only import differ; no declaration, definition, public import,
   hypothesis, or conclusion changed. No change record is required.
2. Independently compiled the delivered file through `lcompile.py`, without errors or
   warnings, and compiled a scratch copy with `#print axioms`. PASS: the axioms are
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from existing unfinished
   dependencies. The module contains no `sorry`, forbidden declaration, or hollow
   definition. This closes one local named hole, not the transitive proof obligations.
3. PASS: no statement is split off, no new declaration is introduced, and no lower hole
   is added. The construction works uniformly for identity maps, empty schemes, and
   the zero ring: it requires only the terminal-object and adjunction properties already
   available, with no nonemptiness or nontriviality hypothesis.
4. Read the upstream constant-sheaf comparison and searched the project and Mathlib
   with alternative names, including `sheafPushforwardContinuousCompSheafSectionsObjIso`
   and `constantSheafsheafPullbackIso`. PASS: the upstream comparison is for the chosen
   generic sheaf pullback, whereas this proof needs the arbitrary compatible ring lift
   supplied by the existing theorem and its section formula. Applying uniqueness of
   left adjoints directly avoids a further transport comparison. Both imports are used;
   the upstream import is correctly plain. All five old proof dependencies remain used
   (the global-sections node is realized by its Mathlib match `constantSheafAdj`).
   `## No longer needed` is complete. The unit `sk-def-exchange` has no realized proof
   steps bypassed; its realized statement nodes remain unchanged.
5. Read the item's node, its global-sections Mathlib leaf, and the unit record alongside
   the Lean proof. PASS: the existing three proof steps, dependency union, and source
   origin agree with the proof. The terminal-sections comparison is implemented by
   adjunction uniqueness; naturality gives the objectwise formula; the pointwise
   identity equations remove the direct-image comparisons. No node update is needed.

Changes made by the second reader: appended this review and the explicit axiom verdict.
No Lean repair was necessary; the proof and node are retained unchanged.
