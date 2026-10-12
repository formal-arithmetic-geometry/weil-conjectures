## What changed

Proved `Polynomial.adjoinRoot_crt_matrix_for_degree_equiv` in
`Sheaf.RingTheory.AdjoinRootCRTRootBlockAux`, without changing any existing signature,
visibility, or public import. Added the proved private helper `root_matrix_entry`.
The proof constructs the CRT algebra equivalence using Mathlib's quotient CRT,
proves coefficient reduction of the power-basis matrix by monic remainders, and
constructs the conjugating unit from the matrices of the equivalence and its inverse.
The node `lem-weil-pbc-adjoinRoot-crt-matrix-root-block-aux-matrix` now records those
steps explicitly. It needs no Sheaf or WeilConjectures proof dependencies.

Source read: Stacks Project, Tag 09XI, `lemma-characterize-henselian-pair`, proof
of (3) implies (1), specifically the displayed decomposition of B/IB. The local
literature file was available in the shared literature checkout. The formal matrix
calculation supplies the coordinates of that decomposition.

Validation: the final module compiles through `lcompile.py` with no warnings.
The construction handles a constant factor equal to one and degree-zero/empty
matrix cases uniformly; no nontriviality of either factor quotient is introduced.

## Proved and sorry left

Closed the sole original hole:
`Polynomial.adjoinRoot_crt_matrix_for_degree_equiv`
(`lem-weil-pbc-adjoinRoot-crt-matrix-root-block-aux-matrix`).
This is a full proof using only proved Mathlib declarations, not a decomposition.

`Polynomial.adjoinRoot_crt_degree_equiv` was already proved and is unchanged.
The new private helper `Polynomial.root_matrix_entry` is proved.
No sorry remains in the module; zero holes were added elsewhere and zero were split off.

## No longer needed

None of the original imports, nodes, or modules is pruned. The two original public
imports are retained for the statements. An explicit proof import of
`Mathlib.RingTheory.Ideal.Quotient.Operations` was tried during development and removed
because its declarations are already available through the original imports.
No new dependency module is required. The unit route is preserved: the auxiliary
node lies below the unit's realized statements and steps.

## Where the brief, the DAG or earlier work was wrong

The matrix node's old plan included a degree-existence step even though its theorem
already receives an arbitrary degree-index equivalence d. Its proof field now records
only the needed CRT, coefficient-reduction, and matrix-conjugation steps.
The node had no named proof dependencies, so the complete glue was supplied directly
from Mathlib. No statement or definition correction was necessary.


## Second reading by R2

1. **Interfaces: pass.** Compared the entire delivered module with the repository
   using `diff -u`. The raw declaration headers of both existing public theorems
   are byte for byte unchanged, as are their visibility, docstrings, and both public
   imports. `adjoinRoot_crt_degree_equiv` is unchanged in full. Only the matrix
   theorem's proof and the new proved private helper differ. There are no definition
   or statement changes and no change records are needed.
2. **Proof and axioms: pass.** Independently compiled the delivered file with
   `lcompile.py`, without errors or warnings. Compiled a scratch copy containing
   `#print axioms` for `adjoinRoot_crt_degree_equiv`, `root_matrix_entry`, and
   `adjoinRoot_crt_matrix_for_degree_equiv`: all three use precisely the permitted
   axioms `propext`, `Classical.choice`, and `Quot.sound`. No sorry, forbidden
   declaration, external implementation, or hollow definition occurs. The CRT
   equivalence comes from Mathlib's proved quotient CRT, not an unproved existence
   assertion. Both matrix inverse laws are proved from the actual inverse map.
3. **Split statements: pass, none.** No hole or public statement was split off.
   The private helper's coefficient formula follows from the monic remainder
   coordinates of the power basis, and is used on both sides of coefficient
   reduction. Checked the constant-one and degree-zero cases: the helper has
   empty indices when the polynomial is one, and the quotient/product bases and
   zero-size matrix unit laws impose no extra nontriviality hypothesis. With a
   degree-one polynomial and the other factor one, the single multiplication
   entry is its root in either block, as required. No arbitrary data is chosen
   from an unproved theorem.
4. **Route and pruning: pass.** Read Stacks Tag 09XI,
   `lemma-characterize-henselian-pair`, the proof of (3) implies (1), including
   the displayed CRT decomposition and the following characteristic-polynomial
   argument. The proof supplies the coordinates of that decomposition. Searched
   the local Sheaf/upstream ring-theory and matrix files and Mathlib for
   multiplication-matrix reduction and CRT product formulas; independently
   queried Loogle for `Algebra.leftMulMatrix` through `msearch.py`. The available
   entry and composition lemmas are already used; no direct result replacing
   the construction was found. Both imports are required by the public statement;
   no proof-only import is made public. The old `proof_deps` was empty, so the
   report's `No longer needed` is complete. Read `dag/units/sk-thm-p1.json`:
   neither auxiliary node realizes a unit statement or step, and no unit route
   or realized record changes.
5. **Node agreement: pass.** The only delivered node changes only `proof`,
   `proof_deps`, and `proof_origin`. Its steps match the explicit principal-ideal
   CRT equivalence, monic-remainder coefficient reduction with degree reindexing,
   and matrix conjugation by the equivalence and its inverse. All facts cited by
   name are proved Mathlib declarations or the proved private helper; no Sheaf
   or WeilConjectures proof dependency is hidden. The provenance identifies the
   source decomposition and the agent's coordinate calculation. No new node is
   necessary, and no existing statement changes.

Second reading changed only this review report; the Lean proof and node were
correct and are retained. Confirmed holes closed: one,
`Polynomial.adjoinRoot_crt_matrix_for_degree_equiv`; holes added: zero;
split off: zero; pruned: none.
