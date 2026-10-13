## What changed

Proved `AlgebraicGeometry.coherentFormalModules_iso_equivalence` in
`Sheaf.AlgebraicGeometry.CoherentFormalModulesIsoEquivalence`, preserving its entire signature
and all definitions. Added one private proof import:
`Sheaf.AlgebraicGeometry.FormalSystemsPullback`.

The proof obtains the forward and reverse formal pullback functors with their inclusion
equations from `exists_formalSystemsPullback`. Comap composition identifies the reverse
functor's target ideal with the original ideal. Tensor pullback composition and identity
isomorphisms give ambient inverse-system comparison isomorphisms. Rewriting the inclusion
equations and cancelling the fully faithful inclusions lifts these into unit and counit
isomorphisms. `Equivalence.mk` constructs the equivalence.

Updated the existing DAG node's proof, proof dependencies, and proof origin to this route.
No statement, definition, visibility, or target changed; no other Lean module was adapted.
The unit's realized statement and proof steps are untouched.

## Proved and sorry left

Closed one of one local holes:
`AlgebraicGeometry.coherentFormalModules_iso_equivalence`
(node `lem-weil-pbc-coherent-formal-modules-iso-equivalence`).
No local sorry remains and no hole was added or split off.
This is a proof from existing library declarations, not a claim that the entire dependency
closure is free of sorry. Local compilation completed without errors or warnings.

## No longer needed

The planned dependency `lem-weil-pbc-coherent-formal-iso-invariant`, module
`Sheaf.AlgebraicGeometry.CoherentFormalModulesIsoInvariant`, is not needed by this proof.
It was not imported in the original module, and has not been added. Both constructed
functors already land in the required full subcategories, so fully faithful cancellation
lifts the unit and counit directly. This removes that edge from the item's DAG proof;
other uses of that module elsewhere in the project may remain.

No existing import was removed: the original public `CoherentFormalModule` import is
necessary for the statement and the sole new private `FormalSystemsPullback` import is
necessary for the proof. No affine presentation, abelian-category theorem, or coimage-image
calculation is used; these were not direct proof dependencies of the item.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's separate use of formal-object isomorphism
invariance was unnecessary: the inclusion equations of its existing formal pullback
statement are enough to lift the ambient natural isomorphisms by full faithfulness.
The node now explicitly names the existing identity/composition tool
`lem-pc-module-pullback-identity-composition` from `sk-def-av-jacobian`, as realized by
`nonempty_tensorPullbackId` and `nonempty_tensorPullbackComp` in `TensorPullback`.
It is used only as the module-pullback functoriality tool; it does not replace the route
of any unit. The formal-systems node does not itself state these composition isomorphisms.

Sources checked: Stacks Section 0EHN and Lemma 0887, directly at
https://stacks.math.columbia.edu/tag/0EHN and https://stacks.math.columbia.edu/tag/0887.
The local literature checkout contains citation lists rather than the cited TeX files.
The proof is uniform for the zero ideal, unit ideal, and empty schemes: no nonemptiness,
proper-support, or nonzero-module hypothesis is used.

## Second reading by N2

1. PASS: Compared the delivered module byte for byte with the repository using `diff`.
   The sole existing declaration retains its entire signature, visibility, and docstring;
   there are no definition or statement changes. The only edits are its proof and the
   private proof import of `FormalSystemsPullback`. No change record is needed.
2. PASS: Compiled the delivered file locally with `lcompile.py` (exit 0, no warnings).
   Compiled a scratch copy with `#print axioms
   AlgebraicGeometry.coherentFormalModules_iso_equivalence`: exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Scanned the delivered Lean
   for sorry and forbidden declarations; none occur. In particular this theorem is
   now proved even under the project's transitive axiom criterion. The existential
   pullback functors are supplied by an already proved theorem, whose inclusion
   equations specify their objects and morphisms; no arbitrary data from an unproved
   existence theorem is introduced.
3. PASS: No statements or holes were split off, and no new nodes were added. Checked
   the imported pullback statement and both tensor comparison signatures. The proof
   uses no extra hypothesis in the zero-ideal, unit-ideal, or empty-scheme cases.
4. PASS: Read the proof from the target downward. Checked the orientations of both
   comap and tensor-pullback compositions, the whiskering and unitor isomorphisms,
   and full-faithful cancellation of the inclusions. Searched the repository's
   coherent-formal modules and Mathlib via `msearch.py grep` for equivalence and
   cancellation alternatives. The existing cancellation helper is already used;
   no direct coherent-formal equivalence or shorter applicable route was found.
   Both imports are needed, and proof-only imports are private. The report lists
   every removed old proof dependency: only the isomorphism-invariance node.
   Read `dag/units/sk-thm-p1.json`: neither this auxiliary node nor the pruned node
   realizes a statement or step of that unit; its route and `realized` record stay
   intact. Tensor comparison is used as a generic module-pullback tool.
5. PASS: Compared the node JSON with its repository version. Only `proof`,
   `proof_deps`, and `proof_origin` change. The steps match the Lean proof, and
   `proof_deps` is exactly the union of their cited nodes. Checked the existing
   identity/composition node's two recorded declarations in `TensorPullback` and
   the formal-systems node's declaration in `FormalSystemsPullback`.

Second reading changed only this report; the proof and node required no repair.
