## What changed

Replaced the sorry in `AlgebraicGeometry.GeometricallyConnected.iff_connectedSpace_finite_separable`
by the finite-separable tests, a separable closure, an invariant clopen partition, and
Galois descent of the two closed parts. The private proved helper
`invariant_clopen_eq_empty_or_univ` proves the descent contradiction using the existing
`exists_closed_subset_of_galois_invariant` twice and surjectivity of the projection.
The original public imports, signatures, universes and visibility are unchanged.
Added the proof import `Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition`.
Updated the assigned node's proof route and created the finite-partition node and module.

Both delivered modules compile together through `lcompile.py --all`, without warnings.

## Proved and sorry left

Closed: `AlgebraicGeometry.GeometricallyConnected.iff_connectedSpace_finite_separable`
(node `lem-weil-pbc-geometrically-connected-finite-separable-test`). No sorry remains in
the assigned module. Its helper `invariant_clopen_eq_empty_or_univ` is fully proved.

Also proved: `AlgebraicGeometry.exists_finite_invariant_clopen_partition`
(node `lem-weil-pbc-galois-finite-invariant-clopen-partition`), in its own new module.
Its private generic helper `orbit_intersection` is fully proved. No holes are added:
one original hole closed, zero split off, zero sorry left in the delivered modules.
The existing quasi-compact-open descent, Galois closed-subset descent and
field-extension-checking declarations are
used as stated; their import closure includes existing sorries that this delivery does not add.

The new statement assumes a particular nontrivial clopen partition over a Galois extension
and produces only an invariant partition over a finite intermediate field. It neither
assumes finite-separable connectedness tests nor concludes geometric connectedness.
The assigned module itself proves nonemptiness, the two descents, complementation,
triviality on the connected finite base change, and passage back from the separable closure.

## No longer needed

Removed the assigned module's direct proof import
`Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends` and its direct proof dependency
`lem-weil-pbc-galois-base-change-qc-open-descends`; it remains needed through the new
finite-partition module and node, so no globally pruned module is claimed.

The assigned node no longer directly uses
`lem-weil-pbc-qcqs-morphism-permanence`, `def-weil-finite-type-morphism`,
`lem-weil-pbc-closed-in-quasi-compact`, `lem-weil-pbc-finite-extension-finitely-many-embeddings`,
and `lem-weil-pbc-cartesian-square-pasting`. These remain dependencies of the new
construction node, not globally unnecessary theory. Its separable-extension definition
is provided by the original public Mathlib import and the separable-closure node.
All other original proof imports are used. Public imports were preserved.
Second reading removed the redundant proof imports `Mathlib.Topology.Connected.Clopen`,
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, and
`Mathlib.LinearAlgebra.FreeModule.Finite.Matrix` from the new partition module;
the required declarations and instances are already exported by its public dependencies.

## Where the brief, the DAG or earlier work was wrong

No false statement or forced adaptation was found. The original plan's long gluing argument
was not a single usable Lean declaration. Its construction subargument was isolated
and proved in the new node, while the Galois descent and connectedness contradiction
were written out in the assigned module. Instead of explicit gluing over all compact
opens, the proved helper intersects all global translates of U. Its restriction to
an affine open is a finite intersection of open translates, so it is globally open;
it is closed as an arbitrary intersection of closed translates. This is the same
partition as the plan's compatible local intersections.

The source file `literature/stacks-project/varieties.tex` is absent in this clone. Read the
full proof at https://stacks.math.columbia.edu/tag/0389 and checked it against the existing
node's numbered proof. The construction applies to any algebraic Galois extension: its
local argument uses Tag 04KU and finite embeddings, not separable closedness of L.
An affine W₀ through one point of U suffices; the complement stays nonempty because the
identity translate is included. Checked empty X (the new hypotheses are impossible),
trivial extensions (the identity action), finite Galois extensions (take the top
intermediate field), and arbitrary non-quasi-compact X (only compact opens are used).

LeanSearch was attempted twice and returned Internal Server Error. This is recorded as
unavailable, with no mathematical absence verdict. LeanFinder, Loogle, source grep,
DAG grep and the blueprint search found no matching invariant-partition theorem.

## New nodes

`lem-weil-pbc-galois-finite-invariant-clopen-partition`, in
`Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition`, isolates steps 5--10 of
Tag 0389 and the pullback-action identification at the start of step 11. Its docstring
and DAG proof explain the compact local pieces, finite translates, compatibility,
gluing, nonemptiness and transport to the iterated pullback. It has the same chapter
and unit as the assigned node; none of the unit's realized statements or steps is bypassed.
The new module proves this statement from the existing
`galois_baseChange_qc_open_descends`: finite orbit cardinality is proved by factoring
through restrictions of inverse automorphisms to a finite intermediate field.
The global intersection proof and the action transport both compile without holes.
No signature changes or change records are needed.


## Second reading by R2

1. Compared the existing module against the repository with `diff -u`: its sole
   public theorem signature, universes, visibility, and all public imports are byte
   for byte unchanged. The differences are one proof-import substitution, a proved
   private helper, and the replacement of the original sorry. The partition module
   and its node are new; no definition or existing statement changes, adaptations,
   or change records are needed. Verdict: pass.
2. Compiled both delivered modules in import order with `lcompile.py --all`, without
   errors or warnings. Neither source contains sorry or a forbidden axiom mechanism;
   neither defines data. Scratch-copy `#print axioms` checked both public theorems
   and both private helpers. `orbit_intersection` uses only propext, Classical.choice,
   and Quot.sound; the other three also use sorryAx from the existing imported
   dependency closure. Galois closed-subset descent remains a named open dependency;
   the repository has meanwhile received proofs of open descent and field-extension
   checking. This delivery introduces no new hole. Verdict: pass, relative
   to those existing named dependencies.
3. There are zero split-off holes. Independently checked the new proved construction:
   the action is contravariant, restrictions of inverse automorphisms give a finite
   orbit on each affine piece, a fixed nonempty local subset stays in the global
   intersection, and the identity translate keeps its complement nonempty. Pullback
   pasting transports precisely the Aut(L/K) action required by the caller. Empty X
   makes its hypotheses impossible; trivial and finite extensions give the expected
   cases; the argument covers non-quasi-compact schemes through affine opens. The
   new theorem neither assumes the connectedness tests nor concludes geometric
   connectedness. Independent LeanFinder search for detection by ground-field
   extensions, Loogle `IsClopen, Homeomorph`, launcher grep for orbit intersections,
   and source searches in lean/ and Mathlib found no shortcut covering this generality.
   Verdict: pass.
4. Read Stacks Tag 0389 online and compared the construction and descent contradiction
   to its proof. The global intersection is the same compatible local partition,
   with openness proved locally. Checked `dag/units/sk-thm-p1.json` realized fields:
   no unit statement or step is bypassed. Compared old and new proof_deps; the report
   lists every removed direct dependency, while the construction still needs them.
   No globally pruned module is claimed. Removed three redundant proof imports from
   the new module after checking them separately and together. Existing public imports
   serve unchanged statements; the new public imports serve its signature.
   Verdict: pass.
5. Compared node statements and Lean signatures; verified that the new node's lean
   statement is verbatim, its required metadata is present, and proof_deps is the
   union of the steps' uses. Existing node edits stay within proof, proof_deps, and
   proof_origin. Repaired the new node's first step to use X, U, and affine W as in
   the actual Lean proof, rather than copied converse notation Y and barred subsets.
   Mathlib instances carry compactness, finite embeddings, and pullback pasting;
   the two existing descent declarations carry the named non-elementary steps.
   Verdict: pass.

Changes in this reading: removed three redundant proof imports, corrected the new
node's compact affine-piece proof description, and recorded this independent review.
Corrected the report's description of upstream holes after the repository refreshed.
No proof term or statement was changed; one original hole closed, zero holes added.
