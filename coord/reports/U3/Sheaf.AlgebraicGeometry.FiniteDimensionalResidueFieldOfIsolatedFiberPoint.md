## What changed

Proved `AlgebraicGeometry.Scheme.Hom.finiteDimensional_residueField_of_isOpen_singleton_asFiber`
with its original signature and algebra structure unchanged. Replaced the two Sheaf proof imports
with the ordinary proof import `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`.
Both public imports remain necessary for the signature.

Mathlib's isolated-fibre-point characterization gives quasi-finiteness of the stalk map.
The stalk-to-residue quotient is finite by surjectivity, hence quasi-finite. Compose these
maps, rewrite using `Scheme.residue_residueFieldMap`, and cancel the base residue quotient
with `RingHom.QuasiFinite.of_comp`. The resulting residue-field map is quasi-finite;
`Module.Finite.of_quasiFinite` over the base field proves finite dimensionality.
The node's proof, proof dependencies, and proof origin now describe this route.

The final module compiles cleanly through lcompile.py. The dry run also performs the axiom probe.
No new statements, definitions, modules, nodes, or holes were needed. The item's node is not a
unit statement or a realized unit proof step in `dag/units/sk-thm-p1.json`; the unit route is kept.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.Hom.finiteDimensional_residueField_of_isOpen_singleton_asFiber`
(node `lem-weil-pbc-isolated-fibre-point-residue-finite`).
There are zero sorries left in the delivered module and zero holes added elsewhere.
This is a complete proof from Mathlib, not a decomposition using holed declarations.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.FibreProductPointResidueField`
  (`lem-weil-pbc-fibre-product-point-residue-field`).
- `Sheaf.AlgebraicGeometry.LftOverFieldIsolatedPointResidueFinite`
  (`lem-weil-pbc-lft-over-field-isolated-point-residue-finite`).

Also removed from this node's proof dependencies:
- `lem-weil-pbc-lft-base-change`: no base change of the morphism is needed.
- `lem-weil-pbc-spec-residue-field-identification`: no field-spectrum identification is needed.

The two removed modules and their dependencies are no longer needed through this item.
Other consumers may still need them; this delivery makes no global unreachability claim.
The definition nodes `def-pc-scheme-fibre`, `def-weil-finite-type-morphism`,
`def-weil-residue-field`, and `def-pc-field-extension` remain in the route.

## Where the brief, the DAG or earlier work was wrong

The earlier plan's tensor-product residue-field argument is mathematically valid but unnecessary.
Its search had found the isolated-point characterization but missed the short ring-hom route:
compose with the surjective residue quotient and apply `RingHom.QuasiFinite.of_comp`.
This avoids both previously imported holed theorems entirely.
LeanFinder, Loogle, launcher grep, and direct source searches were run; Loogle returned the
exact cancellation lemma, and source inspection checked the composition and finiteness lemmas.
The existing theorem docstring is preserved as requested by the Lean skill; the updated DAG and
this report record the actual shorter proof.

## Second reading by U3

1. Compared the only delivered Lean module with the repository using `diff` and
   checked the original theorem signature byte for byte. Only the proof and ordinary
   proof imports change; both public imports and every existing declaration are unchanged.
   No definitions or statement changes are delivered. Verdict: pass.
2. Independently compiled the module with `lcompile.py`: no errors or warnings.
   Searched for forbidden declarations and `sorry`: none. A scratch copy with
   `#print axioms` shows exactly `propext`, `Classical.choice`, and `Quot.sound`.
   Checked the stalk/residue commuting identity, the direction of composition and
   cancellation, and the final algebra instance against Mathlib source. The algebra
   is exactly the one in the unchanged conclusion. Verdict: pass.
3. No statements are split off, no new nodes or holes are added, and no data are
   chosen from an unproved theorem. This point is vacuous. The result also has the
   expected edge cases: an identity morphism gives the degree-one residue extension;
   an empty source has no point to instantiate the theorem. Verdict: pass.
4. Read the Mathlib characterization, quotient finiteness, quasi-finite composition
   and cancellation, and finiteness over an Artinian base. Searched both library
   roots for residue-field finiteness alternatives. The short direct Mathlib route
   needs no Sheaf proof imports. The report lists all four old proof dependencies
   removed, including the two removed modules. Checked `sk-thm-p1.json`: this item
   is neither its realized statement nor any realized step, so this reduction
   preserves the unit route. Verdict: pass.
5. Compared the delivered node with its repository version. Only `proof`,
   `proof_deps`, and `proof_origin` change; their three steps follow the Lean proof.
   The dependency list is the union of the steps' uses, and the statement and Lean
   signature record are unchanged. There are no new-node obligations. Verdict: pass.

Second reading changed only this report by adding the independent review. No proof,
import, declaration, or node repair was needed.
