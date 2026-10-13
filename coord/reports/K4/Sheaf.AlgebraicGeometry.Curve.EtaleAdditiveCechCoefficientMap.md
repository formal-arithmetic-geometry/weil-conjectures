## What changed
Closed `AlgebraicGeometry.Scheme.Modules.additiveCechCoefficientMap_comm` in
`Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechCoefficientMap`. The proof constructs
the natural section identification followed by the resolution augmentation and
applies the Čech complex functor, with the canonical product comparison after
forgetting scalars and applying ULift. Projection identities identify the resulting
chain-map components with the existing fixed coefficient maps. All existing
signatures, definitions, docstrings, visibility, options, and imports are unchanged.
The existing horizontal node's proof and proof_origin now describe this argument.

## Proved and sorry left
Hole closed: `AlgebraicGeometry.Scheme.Modules.additiveCechCoefficientMap_comm`
(node `lem-pbc-additive-cech-coefficient-horizontal`), the only original hole.
Holes added: none. Holes left in delivered modules: none. This is a proof, not a
decomposition: 1 of 1 original holes closed, 0 split off, net 1 hole removed.
`AlgebraicGeometry.Scheme.Modules.additiveCechCoefficientMap_vertical` was already
proved and is unchanged.

Compilation of the delivered file is clean. A scratch copy with `#print axioms`
for `additiveCechCoefficientComplex`, `additiveCechCoefficientMap`,
`additiveCechCoefficientMap_comm`, and `additiveCechCoefficientMap_vertical` reports
only `propext`, `Classical.choice`, and `Quot.sound` for each, with no `sorryAx`.

## No longer needed
None: no imports were removed and the original node's proof_deps was empty.
The proposed new adjacent-degree node and theorem were removed from the sandbox
before delivery; they never belonged to the original dependency graph.
No realized unit node or unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong
The first worker's reduction of the horizontal equation to the adjacent-degree
equation only replaced one hole with another. Its report should have called this
a decomposition. The new theorem lacked a source and complete natural-language
proof in its docstring and carried the original blueprint tag; its node lacked the
required metadata, searches and verbatim Lean statement. The nonadjacent proof
also produced an unused simp argument warning. These faults are resolved by
removing the proposed split and completing the original theorem directly.

## Second reading by K4
1. Compared the entire delivered module against the repository version with diff.
   Verdict: every existing declaration's signature is byte-for-byte unchanged;
   only the horizontal theorem's proof changed. No definition, target statement,
   import, public visibility, or existing docstring changed. No change record is
   needed.
2. Compiled the delivered file through lcompile.py without errors or warnings.
   Scanned for sorry, axiom, unsafe, opaque, implemented_by, extern and kernel
   bypasses: none occur. Independently compiled the scratch axiom probe for all
   four public declarations; all use only the three permitted axioms. Verdict:
   complete proof, no hollow data or unresolved lower statement.
3. Reviewed the proposed adjacent-degree split and removed it after proving the
   complete equation. Searches with msearch.py using loogle (cechComplexFunctor),
   leanfinder (naturality of Čech differentials after forgetting scalars), and grep
   (cechComplexFunctor_map_f_π, PreservesProduct.iso, restrictFunctorΓ), plus rg
   over the project and Mathlib, identified the existing functorial and projection
   lemmas used. Verdict: no new statement or node is required. Empty families,
   empty and repeated opens, degree zero and nonadjacent degrees obey the same
   natural-transformation and product identities; no additional hypotheses enter.
4. Read the original proof plan, imported definitions and relevant existing
   comparison proofs. Used the natural-transformation/Čech-functor route rather
   than leaving a coordinate calculation open. The sole public import supplies
   the definitions in the public signatures and remains necessary. Read
   dag/units/sk-thm-p1.json: this helper is below the unit's realized steps, which
   remain intact. Verdict: shortest available direct route used; no old proof_dep
   or module is newly redundant; unit route preserved.
5. Updated lem-pbc-additive-cech-coefficient-horizontal's proof and proof_origin
   to match the naturality, product comparison, component identification and
   unchanged vertical proof. Its proof_deps remains empty because all reductions
   use existing Mathlib and upstream declarations and no other DAG proof node.
   The statement and Lean record are unchanged. Verdict: node agrees with Lean;
   no new-node obligations remain.

Changed in the second reading: replaced the partial reduction with the full
horizontal proof, removed additiveCechCoefficientMap_comm_succ and its proposed
node, corrected the progress report, and updated the original node's proof route.
