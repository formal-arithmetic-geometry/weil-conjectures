## What changed

Completed the proof of `ExteriorAlgebra.exists_koszul_complementary_equivalences` in the sandbox module. The proof constructs the complementary coefficient pairing using the standard exterior-power basis, proves it bijective, and verifies compatibility with the Koszul differentials. Added proof-only imports of `Mathlib.LinearAlgebra.ExteriorAlgebra.Basis` and `Mathlib.LinearAlgebra.Dual.Basis`.

## Proved and sorry left

The declaration `ExteriorAlgebra.exists_koszul_complementary_equivalences` is fully proved; no `sorry` remains in the delivered module and no new holes were added.

## No longer needed

None. The proof uses the declared Koszul complex, Koszul differential, and dual-complex dependencies. The exterior-power basis node remains conceptually represented by Mathlib's basis API.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt had already developed a compiling proof, but it had not been delivered and the repository source still contained the original `sorry`. No statement or definition was changed.

## Second reading by P3

1. Compared the whole delivered module with the repository file. The existing public theorem's signature and docstring are byte-for-byte unchanged. The only Lean additions are private concrete pairing constructions, proved private helpers, two proof-only Mathlib imports, and the proof replacing the original `sorry`. No existing definition or visibility changed; no change record is needed.
2. Compiled the delivered module with lcompile.py: clean, 3.7 seconds. Compiled a scratch copy with `#print axioms ExteriorAlgebra.exists_koszul_complementary_equivalences`: exactly `propext`, `Classical.choice`, `Quot.sound`. Read every helper: the top coefficient and bilinear pairing are explicit constructions; the bijectivity proof supplies a basis equivalence, and no data is chosen from an unproved existence statement. No sorry or forbidden declaration remains.
3. No statements were split off and no holes were added. Checked the complementary-basis argument at degree zero, top degree, rank zero, and over the zero ring: the complement permutation and unit signs still give both inverse identities. The differential assertion requires j < r, which supplies precisely the subtraction equality it uses. There are no new open statements requiring searches or nodes.
4. Read the signed permutation pairing proof, the above-rank vanishing argument, the Leibniz reduction, and the final sign correction. The unsigned inverse anticommutes with the signed dual boundary; multiplication by (-1)^j gives exactly the unchanged requested equality. Mathlib's exterior-algebra basis multiplication API and dualBasis already implement the linear algebra used here; no shorter complete comparison was found in the repository search or the contraction source. Both added imports are proof-only and needed: removing Dual.Basis in a scratch copy fails at dualBasis; ExteriorAlgebra.Basis provides the top coordinate and wedge multiplication formulas. The sole public import provides both complexes used in the signature. None of the four old proof_deps is unused: the exterior-power basis node is a Mathlib leaf whose recorded match is used directly. Read sk-thm-picard-duality.json realized; this is an auxiliary node, and no unit step or realization is bypassed or changed. Nothing is pruned.
5. Read lem-sc-koszul-complementary-equivalences.json and the exterior-power-free-basis Mathlib leaf. The two existing proof steps match the actual pairing construction and Leibniz/sign calculation, and their proof_deps match the Lean. Updated only proof_origin to record the implemented argument and this independent reading; no statement or dependency change was necessary.

Second-reading changes: completed this report and updated the node's proof-origin metadata. The Lean proof was correct and was left unchanged. Holes closed: ExteriorAlgebra.exists_koszul_complementary_equivalences (one). Holes added: none. Split off: none.
