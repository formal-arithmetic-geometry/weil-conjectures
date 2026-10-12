## What changed

Added the proof of `AlgebraicGeometry.Scheme.constantSheaf_geometricStalk_isIso`.
The proof uses `Point.presheafFiberConstIso` and the general point
sheafification-fibre isomorphism from
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf` (via the
point-fibre sheafification instance). It identifies the displayed map with the
composition of the inverse constant-presheaf fibre isomorphism and the
sheafification map on fibres, both isomorphisms.

## Proved and sorry left

`constantSheaf_geometricStalk_isIso` is proved. No `sorry` remains in the item.

## No longer needed

The new proof no longer depends on these old `proof_deps` nodes:
- `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`;
- `lem-weil-pbc-colimit-constant-connected-diagram`;
- `lem-weil-pbc-sheafification-geometric-stalk`;
- `def-weil-pbc-category-colimit`.

The existing point-fibre infrastructure supplies the corresponding facts. No
import was removed: the original three public imports support the signature and
its sheafification instance; the new plain import supplies the proof lemmas.
No additional DAG nodes or modules were added. The existing item node now records
the route through the upstream constant-presheaf fibre isomorphism and Mathlib's
general sheafification-fibre instance.

## Where the brief, the DAG or earlier work was wrong

The earlier candidate based on `sheafFiberConstantSheafIso` required an unavailable
`WEqualsLocallyBijective` instance at the larger coefficient universe. Using the
point-fibre sheafification isomorphism and `presheafFiberConstIso` avoids that
unnecessary assumption while proving the exact displayed morphism.

## Second reading by H2

1. Compared the complete delivered module with the repository using `diff`.
   The only changes are the new plain proof import and the proof replacing
   `sorry`; the existing declaration signature is byte for byte unchanged.
   No definitions or target statements changed, so no change record is needed.
2. Compiled the delivered module locally without errors or warnings. A scratch
   copy with `#print axioms AlgebraicGeometry.Scheme.constantSheaf_geometricStalk_isIso`
   reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
   No `sorry`, axiom declaration, unsafe/opaque declaration, or foreign-code
   escape remains. The coprojection identity and naturality prove exactly the
   displayed morphism, including the identity neighbourhood and chosen lift.
3. There are no split-off statements or new declarations to review. The
   constant-presheaf isomorphism and the sheafification-fibre instance are already
   proved upstream/Mathlib results; no restatement of the item was introduced.
4. Searched `lean/Sheaf`, upstream Point.ConstantSheaf, and Mathlib
   Point.Skyscraper for existing fibre and sheafification results. The proof uses
   the short existing route, with the required naturality bridge. Each import
   has a role: EtalePoint supplies the point, ConstantSheaf supplies the displayed
   sheaf, HasSheafify supplies the signature's sheafification instance, and the
   plain upstream import supplies the constant-presheaf fibre lemmas. The four
   unused old proof dependencies are now listed explicitly above. Reviewed
   `dag/units/sk-def-pbc.json`: the item and pruned leaves realize none of the
   unit's statement/steps, so this is an allowed reduction below the unit level.
5. Repaired the missing item-node delivery: its `proof`, `proof_deps`, and
   `proof_origin` now follow the compiled proof. The statement, `stmt_deps`, and
   Lean declaration record remain unchanged; there are no new nodes.

Second reading changed only the DAG proof metadata and the report (explicit
pruning and this review). The Lean proof was correct and was retained.
