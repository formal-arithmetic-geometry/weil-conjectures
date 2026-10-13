## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_extendScalars_of_finite_free`
in `Sheaf.AlgebraicGeometry.LocalFreeBaseChangeReflectsIso` with a complete matrix proof.
The statement, universes, hypotheses, visibility and existing public imports are unchanged.
Added two proof-only Mathlib imports: `RingTheory.TensorProduct.Free`
and `LinearAlgebra.Matrix.NonsingularInverse`. The second reader removed redundant
`FreeModule.Finite.Basic` and `Dimension.StrongRankCondition` imports; their required
declarations are already available transitively.

The extended isomorphism identifies the finite basis index types by invariant basis number.
After reindexing, its matrix is the entrywise image of a square matrix over R.
The extended inverse makes the mapped determinant a unit; locality reflects that unit.
The nonsingular inverse matrix gives both inverse identities over R.
Updated the existing node's proof and proof_origin to this route; proof_deps stays empty.
All mathematical ingredients are proved Mathlib declarations; no Sheaf dependencies were added.

Searches used the prescribed msearch leanfinder, loogle and grep calls, and targeted rg searches
of Mathlib, WeilConjectures and Sheaf. There was no existing exact reflection theorem.
The broader faithfully flat reflection theorem would require a missing flatness hypothesis.
The found matrix base-change, inverse and basis-index lemmas suffice instead.

The final module compiles without warnings using lcompile.py. An explicit #print axioms probe
reports only propext, Classical.choice and Quot.sound. No global build was run.
The required deliver3.py --no-push dry run printed OK after transient SSH fetch failures.
The independent second reading is recorded below; final delivery follows its dry run.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_extendScalars_of_finite_free`
(node `lem-sc-local-free-base-change-reflects-iso`).
Holes closed: 1. Holes added: 0. Sorries left: none.
This is a full proof, not a decomposition.

## No longer needed

No repository imports, nodes or modules were pruned. The second reading removed two
redundant newly proposed proof imports: `Mathlib.LinearAlgebra.FreeModule.Finite.Basic`
and `Mathlib.LinearAlgebra.Dimension.StrongRankCondition`.
The residue-field rank comparison in the original plan is implemented by Mathlib's invariant
basis number theorem directly over S; no separate residue-field module or lemma is needed.
An experimental extra RingHom.Basic import was removed before delivery because the existing
imports already provide local-hom unit reflection.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The source was read at Stacks Tag 00O0,
Lemma 10.79.4(3); the item is its explicitly adapted local finite-free matrix argument.
The unit record sk-prop-av-cube realizes neither its statement nor a unit proof step by this node;
its route is unchanged. The node's original unexpanded matrix argument can be proved entirely
from existing Mathlib lemmas, with rank equality supplied by invariant basis number.
The proof requires no flatness and handles zero rank via the empty-matrix inverse identities.
Unequal ranks cannot satisfy the extended-isomorphism premise over nontrivial S.
No new statements, new nodes, changes to definitions or forced adaptations were necessary.


## Second reading by G4

1. Interface: PASS. Read the entire delivered module and diffed it against the repository.
   The only changes are the original theorem's proof and two plain proof-only imports.
   Its signature is byte for byte identical: the universes, commutative-ring and local-ring
   instances, local homomorphism, both finite/free module pairs, morphism and extended-IsIso
   hypothesis all stay unchanged. No definition, public import or other module changed.
2. Proof: PASS. Compiled the delivered file locally without errors or warnings, and compiled
   a scratch copy with an explicit `#print axioms` for
   `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_extendScalars_of_finite_free`.
   It reports exactly `propext`, `Classical.choice`, `Quot.sound`. No sorry or forbidden
   declaration remains. The base-change map is the categorical extension map after
   `algebraize`; the inverse is a genuine constructed matrix inverse, not an arbitrary
   witness from an unproved existence theorem.
3. Split statements: PASS, none. One original hole closed, zero added. Read the adapted
   matrix source at https://stacks.math.columbia.edu/tag/00O0, Lemma 10.79.4(3).
   Checked the nontriviality supplied by local rings for invariant basis number, locality
   for unit reflection, and finiteness for determinants. Rank zero uses the valid empty
   determinant/inverse identities; unequal ranks cannot admit the extended equivalence.
   Independent searches used `msearch grep` with
   `bijective.*baseChange|baseChange.*bijective|IsLocalHom.*[Ii]so`, `msearch loogle`
   with `IsLocalHom, Function.Bijective`, and rg on Sheaf and WeilConjectures. No exact
   shorter reflection theorem was found. Residue-field split-injectivity would need extra
   tensor comparisons; faithfully-flat reflection would require absent flatness.
4. Route and pruning: PASS after import repair. Checked the tensor-basis and matrix
   lemmas, including reindexing direction, both inverse compositions, determinant mapping
   and local unit reflection. The direct invariant-basis-number comparison replaces the
   residue-field rank calculation below the unit level. Read
   `dag/units/sk-prop-av-cube.json`: this item realizes neither its statement nor a step;
   the unit route is preserved. Original proof_deps is empty, so none is omitted from
   No longer needed. Individually removing each proposed proof import showed two were
   redundant, while TensorProduct.Free and NonsingularInverse are needed. Removed both
   redundant imports together and recompiled successfully. Existing public imports stay
   because they form the existing interface.
5. DAG: PASS. Diffed and read the node. Only proof and proof_origin changed; proof_deps
   stays empty. Its three steps match the Lean: tensor basis/index equivalence; mapped
   square matrix and reflected determinant unit; constructed two-sided matrix inverse
   and categorical isomorphism. All ingredients are proved Mathlib declarations, with no
   added Sheaf dependencies or nodes. Statement and lean signature record remain unchanged.

Changes by second reader: removed the two redundant proof-only imports and corrected
this report's import inventory. No mathematical proof, statement, definition or node repair
was needed. Final repaired file compiles cleanly; the original axiom probe was clean and
removing imports changes no proof term or trust assumption.
