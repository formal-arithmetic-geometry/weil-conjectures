## What changed

Proved `AlgebraicGeometry.Scheme.Hom.geometricallyConnected_fiber_iff_connectedSpace_etale_neighbourhood`
in its original module, preserving its signature and public imports. The forward direction applies
geometric connectedness to Mathlib's cartesian fibre square directly. The converse uses the existing
finite-separable test and prescribed-residue-field theorem, transports that square by the compatible
Spec isomorphism, and transfers connectedness along its canonical homeomorphism. Updated the existing
node's proof, proof dependencies and proof origin. The unit's realized statements and steps are kept.
The mathematical argument follows [Stacks Tag 03GZ](https://stacks.math.columbia.edu/tag/03GZ).
Local compilation passed with no errors or warnings.

## Proved and sorry left

Closed 1 of 1 local holes:
`AlgebraicGeometry.Scheme.Hom.geometricallyConnected_fiber_iff_connectedSpace_etale_neighbourhood`
(node `lem-weil-pbc-stein-geometric-fibre-etale-criterion`).
No sorries remain in the delivered module; no new holes were added or split off.
The proof uses the existing open theorem
`AlgebraicGeometry.GeometricallyConnected.iff_connectedSpace_finite_separable`
(node `lem-weil-pbc-geometrically-connected-finite-separable-test`), which is not changed here.
This closes the local hole from the existing planned dependencies, not the entire axiom closure.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.BaseChangeConventions`:
Mathlib's cartesian fibre lemma supplies the comparison instead. Removed
`def-pc-base-change` from this node's proof dependencies; its module is still imported transitively
by the retained finite-separable test, so this does not claim global removal from target reachability.
Removed `lem-weil-pbc-etale-residue-field-extension-separable` from this node's proof dependencies:
the forward implication works over every residue-field extension, and the converse starts with
finite separable extensions already. No dedicated module import existed for this Mathlib leaf.
Retained both other original proof imports because the converse uses their declarations.
No other node or module from the original proof plan is pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan unnecessarily checked finite separability of the residue extension in the forward
direction. Geometric connectedness already gives connectedness after every field extension.
The local Stacks source file named in the node is absent on this machine; the cited Tag 03GZ was read
on the official Stacks website. Its argument agrees with the theorem and the implemented proof.
No statement, definition, visibility, or other module was changed.

## Second reading by A3

1. **Unchanged interface — pass.** Compared the delivered module with the repository using
   `diff` and checked the theorem signature byte for byte through `:= by`. Its hypotheses,
   conclusion, universe, visibility and public imports are unchanged. There are no definitions,
   other delivered modules, new declarations or change records. Only the proof, its explanatory
   docstring and a private proof import differ.
2. **Proof and axioms — pass with the reported open dependency.** Independently compiled the
   module with `lcompile.py`: no errors or warnings. Scanned its source: no `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by` or `extern`. A scratch copy with `#print axioms` reports
   only `propext`, `Classical.choice`, `Quot.sound` and `sorryAx` for the criterion. The existing
   finite-separable test remains open as reported. The prescribed-residue-field theorem reports
   only the three permitted axioms. Its existential witnesses are eliminated within this proof;
   this delivery introduces no definition or arbitrary data chosen from an unproved existence.
3. **Split statements — pass, none.** No holes or statements were added or split off. Checked
   the two existing dependencies and the compatibility of the residue-field isomorphism. Empty
   fibres fail connectedness on both sides (the identity neighbourhood already detects them);
   trivial residue extensions and identity neighbourhoods are covered without extra hypotheses.
   No quasi-compactness, properness or surjectivity is silently required.
4. **Shortest route, imports and pruning — pass.** Independently searched Mathlib with
   LeanFinder using scalar-extension and residue-field wording, and searched the local Sheaf,
   upstream and Mathlib connectedness sources with `rg`. No applicable existing complete
   criterion or finite-separable test replaces this reduction. The forward cartesian-square
   argument needs no separability lemma. The converse needs both retained private Sheaf imports.
   Both public Mathlib imports supply the statement's notions. The report lists both removed
   original proof dependencies and the removed direct import, without claiming transitive
   target-closure pruning. Read `dag/units/sk-thm-p1.json`, including `realized`: neither pruned
   node realizes its statement or a step, and this reduction retains the unit's route.
5. **DAG agreement — pass.** Compared the node JSON: only `proof`, `proof_deps` and
   `proof_origin` differ. Checked that `proof_deps` is exactly the union of the steps' `uses`.
   The steps describe the cartesian fibre square, prescribed residue field, compatible Spec
   isomorphism and connectedness transfer actually used in Lean. Independently read
   [Stacks Tag 03GZ](https://stacks.math.columbia.edu/tag/03GZ); the implemented reduction agrees
   with its argument. No new node records are needed.

Second reading changed only this report: added the independent checks and their verdicts.
No Lean proof, import or node repair was necessary. Closed one local hole, added zero holes;
the existing open finite-separable test prevents claiming that the full axiom closure is proved.
