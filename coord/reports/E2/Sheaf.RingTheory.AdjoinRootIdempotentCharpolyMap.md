## What changed

Proved `Polynomial.adjoinRoot_idempotentCharpoly_map` from a new, strictly partial
coordinate theorem `Polynomial.adjoinRoot_crt_matrix`. The original signature and
all original public imports are unchanged. Added only proof imports of
`Sheaf.RingTheory.AdjoinRootCRTMatrix` and
`Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly`.

Five private lemmas are fully proved: compatibility of `idempotentCharpoly` with
coefficient maps, reindexing and simultaneous conjugation; its two block projection
formulas; and the characteristic polynomial of root multiplication in a monic
quotient. These supply the full determinant calculation after the CRT coordinate
construction. The zero residue ring is handled separately by `nontriviality`.
Empty matrix blocks are included in the proved generic formulas, with no
nontriviality assumptions on the factor algebras.

Both modules compile without warnings through `lcompile.py --all`.

## Proved and sorry left

Closed: `Polynomial.adjoinRoot_idempotentCharpoly_map`
(node `lem-weil-pbc-adjoinRoot-idempotent-charpoly-map`). No sorry remains in the
item's module, including its five private lemmas.

Added: `Polynomial.adjoinRoot_crt_matrix`
(node `lem-weil-pbc-adjoinRoot-crt-matrix`, module
`Sheaf.RingTheory.AdjoinRootCRTMatrix`). This is the only sorry left in the delivery.
It asserts simultaneous matrix coordinates, with no determinant or characteristic
polynomial conclusion. Its statement is strictly the CRT and scalar-reduction part
of the argument; the original theorem then requires the proved determinant algebra.
Thus this delivery is a decomposition: one upper hole closed, one lower hole added,
net zero holes. It is not a sorry-free proof of the original import closure.

The remaining theorem's docstring and node explain coefficient-reduction compatibility,
the CRT equivalence, concatenated power bases, the invertible coordinate matrix and
both multiplication intertwining identities. The witness U is used only in the
proof, and no definition chooses data from this existence statement.

## No longer needed

No original import was removed. An experimental proof import of
`Mathlib.Tactic.NoncommRing` was removed because the final proof uses explicit
associativity and distributivity rewrites instead.

The direct dependency `lem-weil-pbc-charpoly-free-module-properties` is removed
from this item's proof route. No module for general finite-free characteristic
polynomial base change or basis independence is needed: the relevant determinant
invariances are proved directly in the item. Its statement remains useful elsewhere;
this report makes no claim that it leaves the entire target closure.

`lem-weil-pbc-monic-quotient-free` remains needed through the new coordinate theorem,
and the existing multiplication-root characteristic-polynomial leaf remains used.
No unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or signature change was found. The old first step combined
coefficient reduction, the CRT ring equivalence and compatibility of both
multiplication matrices without a Lean declaration for that combined coordinate
assertion. Mathlib provides `Ideal.quotientMulEquivQuotientProd`, but no direct
AdjoinRoot CRT multiplication-matrix statement was found. The new node isolates
exactly this missing part; the rest of the existing plan is now implemented in Lean.

LeanSearch returned Internal Server Error. Loogle, LeanFinder and local searches
were used and recorded. Searching all blueprint nodes for “Chinese remainder”
found no exact existing blueprint node. The Stacks source was read from the fetched
`more-algebra.tex`, Tag 09XI, proof of (3) implies (1), product decomposition and
characteristic-polynomial paragraphs.

## New nodes

`lem-weil-pbc-adjoinRoot-crt-matrix`: simultaneous conjugation of the reduced root
and e multiplication matrices into CRT block coordinates. The residue ring is
assumed nonzero to state the power-basis index equivalence; the original theorem's
zero residue case is proved separately. Degree-zero g or h gives an empty block,
so the theorem permits either factor quotient to be the zero ring. No change
record is needed: no existing statement, definition or public import changed.

## Second reading by E2

1. Unchanged interface: read the complete repository/sandbox diff of
   `AdjoinRootIdempotentCharpolyMap.lean`. The sole existing declaration's signature,
   universe, hypotheses, let-bound matrices and both conclusions are byte for byte
   unchanged. Its docstring and the four existing public imports are also unchanged.
   The two added imports are plain proof imports. The other module is new; neither
   file contains any definition or a change to an existing definition. Verdict: pass;
   no change record is required.

2. Proof and axioms: independently compiled both modules in import order with
   `lcompile.py --all`, without errors or warnings. Inspected every proof. The map
   helper maps the determinant through the polynomial ring homomorphism; the reindex
   helper uses the reindex algebra equivalence; conjugation lifts U to constant
   polynomial matrices and cancels its inverse. The block helper explicitly computes
   both projection matrices, and `root_charpoly` uses `minpoly.unique'` with the
   power-basis lower degree bound, followed by `charpoly_leftMulMatrix`. The main
   theorem actually combines these results with the CRT coordinates. There is just
   one textual sorry, the named public `Polynomial.adjoinRoot_crt_matrix`; no forbidden
   declaration or attribute, and no hollow definition. Scratch-copy `#print axioms`
   checks cover all five private helpers and both public theorems. The main theorem
   depends on the new hole, so this is a decomposition with zero net holes closed,
   not a proof of the full import closure. Verdict: pass subject to that stated hole.

3. New statement: read `adjoinRoot_crt_matrix`, its docstring and node against
   `more-algebra.tex`, Tag 09XI, `lemma-characterize-henselian-pair`, proof of
   (3) implies (1), specifically B/IB's product decomposition. Monicity and nonzero
   residue ring preserve degree; coprimality provides the product quotient; the two
   specified images of e give the first projection. Concatenating power bases gives
   one common invertible coordinate matrix, in the stated conjugation direction.
   The statement has no determinant conclusion and isolates just the coordinate
   part; the proved determinant computations are still necessary to obtain the item.
   Tested the cases g=1, h=1, and both equal to 1: the respective empty blocks and
   singleton zero-dimensional matrix group give the required identities. Also checked
   the concrete nonempty example A=Q, I=0, f=X*(X-1), g=X, h=X-1, e=1-X:
   evaluation coordinates give root blocks 0 and 1 and projection blocks 1 and 0.
   The zero residue ring is intentionally outside the new lemma and is handled by
   `nontriviality` in the unchanged original theorem. No assumption of idempotence
   before reduction is used. No data definition selects its existential witness.
   Independent searches used LeanFinder “simultaneous similarity multiplication
   matrices polynomial quotient coprime factors product basis” and Loogle
   `Matrix.fromBlocks, Algebra.leftMulMatrix`; the former found generic conjugation
   and power-basis multiplication formulas, the latter no hit. Local searches of
   Mathlib, lean/Sheaf, lean/WeilConjectures and the chapter DAG found CRT ring
   equivalences but no duplicate simultaneous coordinate lemma. The apparently
   shorter `AdjoinRoot.minpoly_powerBasis_gen_of_monic` is field-only, so does not
   replace the ring-general root-charpoly proof. Verdict: true, needed, strictly
   partial, with a complete construction argument; not closable in a few minutes.

4. Route and pruning: checked `dag/units/sk-thm-p1.json`'s complete `realized` list.
   This item and its pruned finite-free characteristic-polynomial leaf are below
   its realized unit steps; no realized statement or step is removed or bypassed.
   All imports supply signature/definition vocabulary or proved proof ingredients.
   The new module's reindex import is public because reindex occurs in its statement.
   Compared the old four proof dependencies: the idempotentCharpoly definition and
   monic-root charpoly leaf remain used; the monic-quotient-free leaf moves to the
   new CRT lemma rather than being pruned; the free-module charpoly-properties leaf
   is replaced by explicit determinant calculations and is listed above. No original
   module import is removed and no whole-closure pruning is claimed. Verdict: pass.

5. DAG agreement: read both delivered nodes, both Mathlib dependency leaf nodes,
   and the original item's node. Each updated proof step follows the code: CRT
   coordinates, determinant invariances, block calculation/root charpoly, combination.
   The new node's four steps give coefficient reduction, CRT, coordinates and
   multiplication intertwining, with `proof_deps` equal to the union of `uses`.
   Source, proof origin, searches, creation, blueprint ancestry, chapter/unit and
   Lean records are present and match the theorem. Verdict: pass after adding the
   omitted empty master/slopmaster2 `lean_audit` records to the new node.

Changes by the second reader: added the new node's explicit empty upstream audit
records and this review. No Lean proof or statement was changed; the working proofs
were retained.
