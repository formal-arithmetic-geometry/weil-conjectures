Files written:

- `dag/nodes/sec-picard-framework/lem-pc-affine-derived-pullback-tensor-tilde.json` (statement, split; Mathlib no match)
- `citations.json` (verbatim dependency quotes for all three steps)

Attachments:

- None. No sorry-free declaration in `~/weil-conjectures-slopmaster2/WeilConjectures` states this item exactly.

WANTED:

- None; `literature/stacks-project/perfect.tex` is present and contains Tags 08DW and 08DX.

What was checked and changed:

The item statement was compared with Stacks Project `perfect.tex`, Lemmas 36.3.8 and 36.3.9 (Tags 08DW and 08DX), including the restriction clause and both affine clauses. The source has no project Lean declaration tagged with this item. The imported node had only a single LeanFinder search and no proof; I recorded fresh LeanFinder, Loogle, and Mathlib grep searches and found only underived pullback declarations.

## Review by M1

I read the statements of every cited node before writing the proof. Step 1 uses `lem-pc-kflat-resolution` for a K-flat resolution, `lem-pc-kflat-pullback-preservation` for preservation under the open immersion restriction, `def-pc-derived-pullback` for computation on that resolution, and `def-pc-tensor-complex-sheaves` for the termwise total tensor complex. The restriction is the pullback along an open immersion, so its hypotheses match. Steps 2 and 3 use the same K-flat-resolution existence and the defining derived constructions; on affine schemes the associated-sheaf pullback and tensor identifications are the standard localization calculations from the 08DW/08DX proofs. Step 3 also uses `def-pc-kflat-complex` for the meaning of the chosen K-flat resolution. Every cited node says the quoted fact recorded in `citations.json`.

I checked small cases: for an identity ring map A -> A, both affine isomorphisms reduce to the identity; for the zero complex, all three comparisons are the zero-complex identity. No hypotheses beyond those in the item are introduced, and no new node duplicates a DAG statement or restates a clause of the item. The proof dependencies are exactly the union of the step uses.

What could not be finished:

- Nothing. The proof follows the cited Stacks affine calculations and the existing K-flat definitions.

## Second reading by M1

- Item statement: checked against Stacks `perfect.tex`, Lemmas 36.3.8 and 36.3.9 (Tags 08DW and 08DX); the restriction, affine pullback, and affine tensor clauses retain the stated hypotheses and conclusions.
- New node statement: checked for self-contained scheme, derived-category, K-flat, tensor, and affine associated-sheaf notions; no duplicate lower node or sorry-free Lean declaration was found, and the recorded LeanFinder, Loogle, and grep searches returned no exact Mathlib theorem.
- Step 1: checked against the restriction portions of 08DW/08DX and the statements of `lem-pc-kflat-resolution`, `lem-pc-kflat-pullback-preservation`, `def-pc-derived-pullback`, and `def-pc-tensor-complex-sheaves`; corrected the restriction domains and made the K-flat resolutions explicit.
- Step 2: checked against 08DW(2) and the cited K-flat and derived-pullback statements; the affine associated-sheaf identification is now stated degreewise and cited through `lem-pc-affine-qcoh-derived-equivalence`.
- Step 3: checked against 08DX(2), `def-pc-kflat-complex`, and the total tensor-complex definition; the K-flat computation and totalization compatibility are explicit.
- Small cases: identity ring map and zero complexes reduce to identity isomorphisms; the affine formulas also specialize to a field and to the zero module complex.

Changes made: fixed `created.item` to this delivery item; repaired Step 1's ill-typed use of `P|_U` by restricting to `V` before pulling back to `U`; added the affine associated-sheaf equivalence dependency and citation; clarified Step 2's degreewise tensor identification.
