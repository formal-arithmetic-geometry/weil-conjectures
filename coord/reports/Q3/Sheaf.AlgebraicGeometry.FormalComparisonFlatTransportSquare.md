## What changed

Replaced the proof of `AlgebraicGeometry.formalComparison_flat_transport_square` with a complete
construction. The proof applies `formal_flat_quotient_mate_data`, obtains the normalized completion
pullback isomorphism, defines `δ` as the completion map of the ordinary base-change isomorphism
followed by the inverse normalized pullback map, and defines `κ₀` by transport. The quotient
identity is proved componentwise using the two projection equations, functoriality of pullback,
the given `hκ`, and the lower mate theorem. Added the proof-only import
`Sheaf.AlgebraicGeometry.FormalCompletionPullbackNormalized`.

The copied DAG node was updated so its proof and `proof_deps` record exactly this route.

## Proved and sorry left

The target declaration `AlgebraicGeometry.formalComparison_flat_transport_square` is fully proved.
Closed hole: `AlgebraicGeometry.formalComparison_flat_transport_square`
(node `lem-weil-pbc-formal-comparison-flat-transport-square`): one of one holes closed.
There are zero `sorry`s left and no new holes or declarations were added.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.FormalSystemsPullback`; no declaration from
that module is used by the completed proof. The corresponding node
`lem-weil-pbc-formal-systems-pullback` is no longer a direct proof dependency of this node.
Its module remains a transitive import of `FormalCompletionPullbackNormalized`; no module is
claimed pruned from the target import closure.

## Where the brief, the DAG or earlier work was wrong

The original DAG route listed formal systems pullback as a direct dependency, but the ordinary
quotient-mate theorem already packages all system-level pullback data needed here. No statement
was changed.

## Second reading by Q3

1. Compared the delivered module with the repository version. The existing theorem signature
   is byte-for-byte unchanged; only its proof and proof-only imports differ. No definition,
   target statement, public import, or other module is changed. No change record is needed.
   Verdict: pass.
2. Compiled the module with `lcompile.py` without errors or warnings. Scanned the entire file:
   no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or kernel-check bypass.
   Appended `#print axioms` to a scratch copy of the actual delivered source: the theorem uses
   only `propext`, `Classical.choice`, and `Quot.sound`. The local constructions of delta and
   kappa zero contain no arbitrary data choice from an unproved existence theorem.
   Verdict: pass.
3. No statements or holes were split off. Read both supporting theorem signatures and their
   constructions/docstrings. The ordinary mate theorem supplies precisely b, t, beta zero,
   the ordinary projection equation, and the unit equation. The normalized pullback theorem
   supplies the completion isomorphism and projection equation. The cokernel descent equation
   proves naturality of completion at b. The remaining composition uses functoriality and h-kappa.
   Zero/unit ideals and empty schemes require no cancellation except of an isomorphism; the
   same equations apply. Searched local Sheaf/upstream declarations and independently queried
   LeanFinder with `formalComparison flat transport square`: only generic category tools, no
   shorter exact theorem or duplicate. Verdict: pass.
4. Read the proof from its target downward. Both proof-only imports supply declarations used
   explicitly. All public imports support the unchanged statement. The removed direct import
   and its node are listed above; no transitive module pruning is claimed. Inspected
   `dag/units/sk-thm-p1.json`: this item realizes none of its fixed statement or proof steps,
   and replacing this internal diagram chase bypasses no unit realization. Verdict: pass.
5. Compared the DAG metadata against the proof. The three steps describe the ordinary mate
   data, completion isomorphism, and quotient chase, respectively. `proof_deps` is their union
   and `proof_origin` describes the actual route. No new nodes are present; all other existing
   node fields retain their values. Verdict: pass.

Second reading changes: clarified the one closed hole and the lack of transitive module pruning;
corrected the DAG prose to distinguish the normalized pullback isomorphism from delta; preserved
Unicode formatting in the node. No Lean proof repair was needed.
