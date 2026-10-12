## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biprod` without changing its
signature. Replaced the proof-only import of `Sheaf.AlgebraicGeometry.Coherent` by
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`. Its already proved
`isQuasicoherent_sigma` applies to a family indexed by `ULift Bool`; the universe lift
is needed because that theorem uses an index type in the scheme universe. Constructed
both directions of the biproduct/coproduct isomorphism and checked their composites
by the respective extensionality lemmas. Updated the node route to this proof.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biprod` (node
`lem-weil-pbc-quasi-coherent-module-direct-sum`). No sorry remains in the delivered
module; no new theorem with sorry was added. Local compilation completed without
warnings. No hypotheses were added, and the proof also covers the empty scheme.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.Coherent`. The explicit original proof
route no longer needs `lem-weil-pbc-module-restriction-open-immersion-colimits`
(Mathlib restriction declarations in
`Mathlib.AlgebraicGeometry.Modules.Sheaf`) or
`lem-weil-pbc-affine-tilde-gamma-adjunction` (`Mathlib.AlgebraicGeometry.Modules.Tilde`). The
original proof dependencies `def-weil-sheaf-of-modules-category`,
`def-weil-additive-category`, `def-weil-pbc-category-colimit`, `def-pc-scheme`,
`def-weil-affine-spectrum`, and `pqf-def-coherent` are no longer proof-dependency
nodes of this auxiliary theorem; its statement-dependency nodes remain unchanged.
The three public Mathlib imports are retained for the unchanged signature and local
biproduct instance. This node does not realize any of the unit's own steps, so no
unit-level route was bypassed. The source coproduct theorem internally implements
the affine-local presentation argument, without importing the original Sheaf plan.

## Where the brief, the DAG or earlier work was wrong

The DAG's search record already identified the proved source-library theorem
`isQuasicoherent_sigma`; it suffices after the binary categorical identification.
No mathematical statement error was found. LeanFinder and Loogle searches returned
quasi-coherence definitions and related facts but no Mathlib closure theorem;
repository searches located the source theorem. Import-direction check accepted the
new proof import. No new nodes or statement changes were needed.

## Second reading by V2

1. PASS: compared the complete delivered module with the repository using `diff -u`.
   The theorem signature, local biproduct instance, definitions, and public imports
   are byte-for-byte unchanged. Only its proof and one proof-only import change; no
   change record is required.
2. PASS: independently compiled the delivered file successfully without warnings.
   Compiled a scratch copy containing the actual delivered proof followed by
   `#print axioms AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biprod`; the
   result is exactly `propext`, `Classical.choice`, and `Quot.sound`. No sorry or
   forbidden declaration remains. The earlier Axioms.lean scratch import checked
   the repository's unfinished version instead, so was not evidence about this proof.
3. PASS: no statements were split off and no new declarations or nodes were added.
   Read the upstream coproduct theorem: its only input is quasi-coherence of the
   family, and its index universe is met by ULift Bool. Both Boolean cases select
   exactly the corresponding summand. The empty scheme and zero summands need no
   extra hypotheses. Independent repository searches for coproduct/biproduct
   quasi-coherence confirm the existing sigma theorem is the direct available route;
   launcher grep search for "quasicoherent coproduct binary" returned zero hits.
4. PASS: the proof first applies the proved source-library coproduct theorem, then
   explicitly proves the canonical isomorphism in both directions. The orientation
   of prop_of_iso is correct. No still-open Sheaf lemma is used. The removed import
   and all eight old proof-dependency nodes are listed under No longer needed.
   Checked dag/units for this node: it realizes no unit statement or step, so the
   auxiliary specialization preserves the unit route. Public imports support the
   unchanged signature and local biproduct instance; the new source import is private
   to the proof. No shorter theorem application was found that warrants rewriting
   this correct proof.
5. PASS: compared the node JSON against the repository. Only proof, proof_deps,
   and proof_origin change. The new prose describes the actual sigma application,
   two inverse maps, extensionality checks, and isomorphism transport. No old DAG
   proof dependency is used; the proved source theorem is recorded by declaration
   and module in proof and proof_origin. Statement and stmt_deps are unchanged.

Second reading changed only this report and added a scratch axiom check; no repair
to the Lean proof or node was needed.
