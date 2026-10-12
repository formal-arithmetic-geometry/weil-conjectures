## What changed

Proved `AlgebraicGeometry.Etale.isZero_constant_cohomology_one_of_torsors_trivial`
in `Sheaf.AlgebraicGeometry.GabberH1TorsorCohomologyBridge` without changing its
statement. Added the proof-only import
`Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison`.
The proof applies the upstream `Sheaf.subsingleton_H_one_iff`, takes the component
of `Scheme.nonempty_sheafH_extDerivedIso Z 1` at the constant sheaf, and transports
`AddCommGrpCat.isZero_iff_subsingleton` across that isomorphism.
Updated the item's DAG proof, proof dependencies, and proof origin to this route.
The node does not realize a unit statement or proof step, and the unit's route is kept.

## Proved and sorry left

Proved the module's sole sorry:
`AlgebraicGeometry.Etale.isZero_constant_cohomology_one_of_torsors_trivial`
(node `lem-weil-pbc-gabber-h1-torsor-cohomology-bridge`).
No sorry remains in the delivered module; no new theorem, definition, or sorry is added.
The existing comparison module already has a complete Lean proof.
Local compilation passed without warnings. The delivery dry run checks compilation
on the server and the permitted-axiom probe.

## No longer needed

No import removed. All existing public imports support the unchanged statement
and its instances; the sole added import is used only by the proof.
No existing argument node or module is pruned: torsor classification remains needed,
and the derived comparison is now explicitly named as a proof dependency.
`def-weil-pbc-etale-cohomology` remains a statement dependency; it is removed from
`proof_deps` because the proof does not unfold cohomology or construct a resolution.
No separate direct injective-resolution proof or new intermediate node is needed.
The broader `Sheaf.AlgebraicGeometry.ConstantEtaleCohomologyIsoComparison` was
considered but is not imported: the generic Ext-to-derived comparison suffices.

## Where the brief, the DAG or earlier work was wrong

The previous proof step named only torsor classification and the definition of
cohomology, leaving the Ext-to-derived comparison implicit. The existing node
`lem-weil-pbc-sheafH-ext-derived-comparison` supplies precisely that comparison and
is already proved and available in the compiled snapshot. Its direct use avoids
new nodes and the extra isomorphism-of-schemes transport.
The previous node's search note that the comparison was unavailable in the green
build is stale; local compilation successfully imports it.
There is no mathematical or signature correction. The geometric and finiteness
hypotheses remain unchanged, even though this cohomological implication does not
use them. The proof works uniformly for the trivial coefficient group and the
empty scheme through the general terminal-site classification and comparison.

## Second reading by V1

1. **Diff and statements.** Compared the delivered module with the repository version. The theorem
signature and all existing declarations are byte-for-byte unchanged; the only module change is the
proof and one proof-only import. The DAG node changes only proof route, proof dependencies, and
proof origin.

2. **Proof and axioms.** Compiled the module locally with no errors or warnings. The theorem has no
`sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; an axiom probe reports only
`propext`, `Classical.choice`, and `Quot.sound`.

3. **Split-off statements.** No statement was split off and no new theorem or definition was added.
The proof uses the existing torsor classification and Ext/derived comparison declarations.

4. **Pruning and route.** The added comparison import is used by the proof and is proof-only. The
existing public imports remain required for the unchanged signature and instances. The route first
obtains subsingleton H¹ from torsor triviality, then applies the existing comparison isomorphism and
transports `IsZero`; the unit `sk-thm-p1` route is unchanged.

5. **DAG agreement.** The node's two proof steps, `proof_deps`, and `proof_origin` match the Lean
proof. No old proof dependency is used implicitly, and no node or module can be pruned from this
item's closure.

I changed only this report section after the first delivery attempt; no Lean or DAG repair was
needed.
