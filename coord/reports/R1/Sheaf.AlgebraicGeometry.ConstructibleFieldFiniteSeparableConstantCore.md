## What changed

Proved `AlgebraicGeometry.constructible_field_finite_separable_constant_of_datum`
in `Sheaf.AlgebraicGeometry.ConstructibleFieldFiniteSeparableConstantCore` without changing
its signature. Added proof-only imports of `WeilConjectures.PointCount`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`, and
`WeilConjectures.ConstructibleSheaf.Pullback`. The first identifies the residue-field
structure map geometrically, the second supplies the finite separable residue extension,
and the third supplies the localized-site and constant-sheaf comparisons.

The proof chooses a point on a cover member, constructs its residue-field extension,
transports the given localized trivialization without changing its finite module value,
and composes inverse images. Updated the node's proof and dependencies to this Lean proof.
The unit route is preserved: the node implements its original point-and-residue-field plan.
Local compilation passes; the dry run also checks server compilation and the axiom probe.

## Proved and sorry left

Proved `AlgebraicGeometry.constructible_field_finite_separable_constant_of_datum`
(node `lem-weil-pbc-constructible-field-finite-separable-constant-step3-7`).
No `sorry` remains in the item's module, and no new declarations or `sorry`s are added.
The second reader's explicit `#print axioms` check confirms that the theorem uses only
`propext`, `Classical.choice`, and `Quot.sound`, with no transitive `sorryAx`.

## No longer needed

None: no original import or planned dependency was removed. No new intermediate module
is needed. In particular the proof does not require a decomposition of the whole etale
cover member as a coproduct, an isolated-point finiteness lemma, or a new theorem
transporting finite constant values: the existing residue-field and sheaf comparisons
suffice. These were search alternatives, not dependencies of the original node.

## Where the brief, the DAG or earlier work was wrong

The original node had one unsplit proof step and no proof dependencies. Its mathematical
plan is correct. The updated record names the site-equivalence, inverse-image-composition,
and constant-pullback nodes actually used and records the existing proved residue-field
APIs. `JointlySurjective etalePrecoverage` is supplied locally from the instance for
`precoverage @Etale`; importing an additional constructible-sheaf module just for this
instance is unnecessary. The statements and definitions are unchanged.

## Second reading by R1

1. Compared the only delivered Lean module with the repository using `diff` and checked
   the complete existing theorem signature byte for byte: identical. There are no changed
   definitions, new declarations, or statement changes. The three added imports are plain
   proof-only imports. Verdict: pass.
2. Compiled the module through `lcompile.py` without errors or warnings. A scratch copy
   with `#print axioms` shows exactly `propext`, `Classical.choice`, and `Quot.sound` for
   the theorem, and separately for the residue-field etaleness, structure-map identity,
   and localized-sheaf comparison used in it. No `sorry`, forbidden declaration, hollow
   definition, or transitive `sorryAx` occurs in the delivered proof. Verdict: pass.
3. No statements were split off and no new nodes or modules were added. Checked the
   mathematical edge cases: an empty cover cannot cover the closed point of `Spec k`;
   empty cover members are harmless because the chosen member has a point; the zero
   coefficient ring and zero constant module are allowed and the same finite module is
   transported throughout. No perfectness assumption on k is used: etaleness gives the
   required finite separable residue extension. Verdict: pass.
4. Read the proof from its conclusion backward, inspected the existing residue-field
   and sheaf-comparison APIs, and searched the surrounding Lean modules for a direct
   finite-separable-constant result. The parent theorem already reduces to this item,
   so it cannot be used to close it. The existing residue-field route avoids a coproduct
   decomposition or additional lemmas. Each added import supplies a declaration actually
   used. The sole original import remains needed for the signature. The original node
   had no proof dependencies, so `No longer needed: None` is complete. Read
   `dag/units/sk-thm-p1.json`, including `realized`: this is a reduction below that unit's
   steps and preserves the point/residue-field plan. Verdict: pass.
5. Compared both node records structurally: only `proof`, `proof_deps`, and `proof_origin`
   differ. Checked that `proof_deps` is precisely the union of the step uses, and checked
   the named site-equivalence, composition, and constant-pullback nodes against their
   recorded declarations. The four proof steps match the Lean construction. No new-node
   fields or change records are needed. Verdict: pass.

Changes by the second reader: corrected the report's tentative claim about transitive
`sorry` to the verified axiom result and added this review. The Lean proof and node record
needed no repair.
