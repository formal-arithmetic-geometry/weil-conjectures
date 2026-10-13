## What changed

Proved AlgebraicGeometry.torsionControlled_completion_hom_lift_raw in
Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftRaw with its current
signature unchanged. Added proof-only imports of CoherentMapTorsionCompletionExtZero
and TorsionControlledCompletionHomLiftCompletion. A separating quotient gives an
invertible finite-graph projection; its inverse followed by the second projection
is the explicit witness. The pullback equation proves the required comparison.
Updated the raw node's proof, proof_deps and proof_origin to this route.

## Proved and sorry left

Closed the one hole: AlgebraicGeometry.torsionControlled_completion_hom_lift_raw
(node lem-weil-pbc-torsion-controlled-completion-hom-lift-raw).
No sorry remains in the delivered module; no holes or modules were added.
The proof relies on the existing finite-graph epimorphy theorem
AlgebraicGeometry.torsionControlledGraphFst_epi, which remains sorry in its
unchanged dependency module (node lem-weil-pbc-torsion-controlled-finite-graph-epi).
This is a proof from existing stated dependencies, not an axiom-free closure.
The separating-quotient and graph monomorphy arguments are already proved.

## No longer needed

No imports removed and no existing dependency node or module pruned: the original
raw module had no proof-only imports and its node had empty proof_deps.
The direct affine localization and sheaf-gluing construction in its earlier plan
is replaced by the existing finite-graph argument. The proof only uses the graph
isomorphism part of the completion lemma; it does not use the stronger constructed
lift's completion equation or the Exists theorem. The bound ha is unnecessary for
this route, but remains in the unchanged signature. The unit's realized statements
and steps are untouched; this node is below the unit level.

## Where the brief, the DAG or earlier work was wrong

The inherited sandbox was stale: it omitted θ and hθ and marked the resulting
statement disputed. The repository has already repaired that omission, so the
sandbox was reset to the corrected repository declaration before proving it.
Its obsolete counterexample helpers and dispute comments are not delivered.
The zero-ideal counterexample does not meet the corrected compatibility hypothesis.
Existing graph and Artin–Rees declarations supply a shorter route than the raw
node's unlinked affine-gluing sketch. No statement or definition changes were made.

## Second reading by Q4

1. PASS: compared the sole delivered Lean module with the repository using diff.
   The existing declaration signature and docstring are byte-for-byte unchanged;
   only its proof and two plain, proof-only imports differ. There are no delivered
   definitions, additional modules, or change records. The already-landed repair
   restoring θ and hθ is retained exactly.
2. PASS: compiled the module locally through lcompile.py without errors or warnings.
   Scanned the delivered source: no sorry and no prohibited declarations or attributes.
   A scratch copy with #print axioms reports precisely propext, Classical.choice,
   Quot.sound and sorryAx. The remaining sorryAx is inherited from open dependencies,
   including torsionControlledGraphFst_epi; this is not an axiom-free target closure.
   The witness is an inverse of a specified graph projection followed by its second
   projection, not arbitrary data chosen for a new definition from an open existence
   statement. The inverse is uniquely determined by its isomorphism equations.
3. PASS: no statements were split off and no new nodes or holes were added. Read the
   separating-depth, graph monomorphy, graph isomorphism and graph epimorphy statements.
   The zero ideal gives the graph of θ, the unit ideal makes a′ invertible, and zero
   modules and the empty scheme present no exception. The finite graph epimorphy
   theorem is an existing, strictly intermediate statement, not a renamed raw lift.
4. PASS: searched the library by hom_lift and graph projection terminology and ran
   a fresh msearch grep query for compatible formal-completion lifts. The already
   proved Exists theorem is stronger and would shorten the text, but the current
   proof avoids using its additional completion equation and finite-detection step.
   Both proof-only imports are used; the public import supplies the signature.
   The old node has empty proof_deps, so there are no omitted pruning entries.
   Read dag/units/sk-thm-p1.json: this node realizes neither its statement nor a
   named step, and the realized route is preserved.
5. PASS: compared the node JSON with its repository version. Only proof, proof_deps
   and proof_origin change. The two dependency nodes match the separating-depth and
   graph-isomorphism calls, and the last elementary step matches the pullback
   equation and inverse cancellation. The completion node's current proof_deps
   contain graph epimorphy and finite detection, not the raw node, so the new route
   does not create a dependency cycle.

Changes by the second reader: appended this independent review only; no Lean or
node repair was needed. Closed one named hole, added zero holes, split off zero
statements; no modules pruned. The existing docstring describes the original
formal-gluing argument; the updated node and this report record the shorter graph
argument actually used by Lean.
