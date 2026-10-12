## What changed

Proved `AlgebraicGeometry.coherentFormalModules_of_iso` in
`Sheaf.AlgebraicGeometry.CoherentFormalModulesIsoInvariant` with its public signature
and imports unchanged. Added a proved private `finiteType_of_iso` helper: finite local
generators push forward along the component isomorphism. Kernel transport establishes
coherence. The existing `formalModuleQuotient_factor` proves annihilation, and the
existing quotient-map identity and composition laws construct the transported quotient
isomorphism. Naturality proves its required transition equality. The node proof now
records these concrete steps and their existing dependencies.

## Proved and sorry left

Closed the sole original hole, `AlgebraicGeometry.coherentFormalModules_of_iso`
(node `lem-weil-pbc-coherent-formal-iso-invariant`). No holes added or split off.
No `sorry` remains in the delivered module. The private helper is also fully proved.
Single-file compilation passes without warnings. Explicit `#print axioms` checks for
the target and private helper show only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

None: the sole original import, `Sheaf.AlgebraicGeometry.CoherentFormalModule`, is
needed for both the statement and its quotient-map laws. No modules or nodes are
pruned. In particular the proof needs no new import of the general coherent
kernel/cokernel closure module, and no new intermediate statements.
The item's node is not one of the unit's realized statement or proof-step nodes;
the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The original node gave transport steps but
no proof dependencies. Its proof now records the already proved ideal-product
factorization and quotient-map laws used to realize those steps in Lean.

## Second reading by G1

1. Compared the complete delivered module with the repository version. The existing
   theorem signature, visibility, universe, and sole public import are byte for byte
   unchanged. No definition changed; no change record or forced adaptation is needed.
2. Compiled the module locally without errors or warnings. Read both proofs and ran
   explicit `#print axioms` checks in a scratch copy for
   `AlgebraicGeometry.coherentFormalModules_of_iso` and the private `finiteType_of_iso`:
   both use only `propext`, `Classical.choice`, and `Quot.sound`. No sorry or forbidden
   declaration is present. The quotient isomorphism is constructed from actual maps;
   the factorization witness is used only to prove a proposition, not to choose data.
3. No statements were split off and no holes added. The private helper transports
   the existing local generators over exactly the same covering and preserves their
   finite index sets, including the empty case. Checked Mathlib's Generators module
   and searched Loogle for `SheafOfModules.IsFiniteType`; no public transport theorem
   replaces this helper. The related helpers in CoherentKernelCokernelSum are private.
4. The three branches directly establish coherence, annihilation, and quotient
   compatibility. The sole import is necessary for the statement and quotient laws;
   adding the general kernel/cokernel closure module would introduce an unnecessary
   dependency. The old node had no proof dependencies, so none is omitted from the
   pruning report. Read `dag/units/sk-thm-p1.json`: this node is not a realized unit
   statement or step, and its proof preserves that unit's route.
5. Compared the node with its repository version: only `proof`, `proof_deps`, and
   `proof_origin` changed. Its steps match the Lean, and its dependency union names
   the existing ideal-power factorization node and the coherent-formal-module node
   containing the quotient identity/composition laws. No new nodes need validation.

Second-reading changes: restored the existing theorem docstring verbatim, leaving
its valid proof intact; recorded explicit axiom verification and this review.
Verdict: pass; one original hole closed, zero added, zero split off, no pruning.
