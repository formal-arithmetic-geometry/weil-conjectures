## What changed

Replaced the one missing proof in `Sheaf.RingTheory.MonicFactorizationOfIdempotent` with a
complete Lean reduction, preserving its declaration and all public imports. The factors are
explicit determinants on the power basis of `AdjoinRoot f`, rather than choices of glued
locally free characteristic polynomials. For the matrix T of multiplication by X and the
idempotent matrix P of multiplication by e, use
`D(T,P) = det(1-C(P) + charmatrix(T)*C(P))` and `D(T,1-P)`.

Added four modules: `Sheaf.LinearAlgebra.IdempotentCharpoly` defines D with complete data;
`Sheaf.LinearAlgebra.IdempotentCharpolyMulComplement` proves the determinant product identity;
`Sheaf.LinearAlgebra.IdempotentCharpolyMonic` states its Jacobson monicity step; and
`Sheaf.RingTheory.AdjoinRootIdempotentCharpolyMap` states its CRT reduction step. Each has its
own new node. The original node's proof, proof dependencies, and proof origin now follow
the implemented determinant route. The original theorem's docstring now describes the explicit determinant route (updated
during the second reading).

The main proof establishes idempotence and commutation of both projections, applies the two
new intermediate statements, proves the ambient characteristic polynomial equals f by
`charpoly_leftMulMatrix`, `minpoly.unique'`, and the power-basis degree bound, and assembles
the required conjunction. The generic determinant product proof uses matrix algebra and
`Matrix.det_mul`; it does not depend on either remaining missing proof.

All five delivered modules compile without warnings with lcompile.py. Separate scratch
examples compile for P=0 (D=1), P=1 (D=charpoly T), empty matrices (D=1), and the zero ring
(the only polynomial is monic). `#print axioms Matrix.idempotentCharpoly_mul_complement`
reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

The original `Polynomial.exists_monic_factorization_of_idempotent` has no missing proof in
its body: one of the original one sorries is reduced. It still depends on the following two
named intermediate theorems, and the delivery is not an axiom-free completion of the target.

- `Matrix.idempotentCharpoly_monic_of_map_monic`, in
  `Sheaf.LinearAlgebra.IdempotentCharpolyMonic`, node
  `lem-weil-pbc-idempotent-charpoly-monic`, is exactly `:= by sorry`.
- `Polynomial.adjoinRoot_idempotentCharpoly_map`, in
  `Sheaf.RingTheory.AdjoinRootIdempotentCharpolyMap`, node
  `lem-weil-pbc-adjoinRoot-idempotent-charpoly-map`, is exactly `:= by sorry`.

`Matrix.idempotentCharpoly_mul_complement`, node
`lem-weil-pbc-idempotent-charpoly-mul-complement`, is fully proved independently of those
statements. `Matrix.idempotentCharpoly`, node `def-weil-pbc-idempotent-charpoly`, is a genuine
explicit determinant definition and contains no missing proof or missing data.

The intermediate statements are strictly separate parts of the argument. The monicity
statement has arbitrary commuting matrices and no factorization or lifting conclusion.
The CRT statement only identifies the reductions of already specified determinants, and
requires neither the Jacobson hypothesis nor idempotence of e before reduction. Neither
statement asserts existence of the requested factors or their product identity.

## No longer needed

Removed the following proof-only imports from the item's module:

- `Sheaf.Algebra.CharpolyLocallyFree`.
- `Sheaf.Algebra.LocallyFreeCharpoly`.
- `Sheaf.Algebra.LocallyFreeCharpolyProdMap`.
- `Sheaf.RingTheory.FiniteProjectiveStandardFreeCover`.

The determinant route needs no glued locally free characteristic polynomial, its universal
base-change specification, or its locally free direct-sum theorem. Consequently the following
original proof dependencies and their corresponding modules are unnecessary on this branch:

- `def-weil-pbc-charpoly-locally-free`: `Sheaf.Algebra.LocallyFreeCharpoly`.
- `lem-weil-pbc-charpoly-locally-free-existence`: `Sheaf.Algebra.CharpolyLocallyFree`.
- `lem-weil-pbc-charpoly-locally-free-direct-sum`:
  `Sheaf.Algebra.LocallyFreeCharpolyProdMap`.

This does not assert they are unreached from every other target branch. The removed direct dependencies also include
`lem-weil-pbc-finite-projective-standard-free-cover` and
`lem-weil-pbc-finite-projective-rank-locally-constant`. Both remain in the natural-language proof
plan of the new monicity node; they have moved below that intermediate step and are not claimed
globally unnecessary. The monic-quotient power-basis node and characteristic polynomial of
multiplication by X node remain needed. No other existing module is edited.

## Where the brief, the DAG or earlier work was wrong

No statement was disputed or changed. The old DAG route is mathematically valid, but its
gluing machinery is unnecessary for this item because the summands have specified projectors
inside a finite free module. The ambient determinant already defines their characteristic
polynomials. The node is not one of `sk-thm-p1`'s realized statement or step nodes; that unit's
statement, steps, and route are unchanged.

The listed local `literature/stacks-project/` files are absent from this remote clone. Read
Stacks Tags 09XI and 00NX directly at the official Stacks site, and obtained their actual
`more-algebra.tex` and `algebra.tex` sources from the Stacks repository into the sandbox's
scratchpad. The sources confirm the splitting, constant-rank, and characteristic-polynomial
paragraphs. The explicit matrix realization and its omitted-details argument are marked as
written by G2 in proof_origin. No literature or coordination file in the read-only clone was
edited by the worker.

LeanSearch returned Internal Server Error for all four new-node queries. Recorded that
unavailability without claiming an absence verdict from it; Loogle/LeanFinder and source grep
were also performed. No existing declaration was found for the new formula, Jacobson monicity,
or CRT determinant calculation. `Matrix.det_mul` is the existing tool used for the proved
multiplication lemma. Searches of the DAG and whole blueprint found no duplicate determinant
summand statements.

Edge cases of both new missing statements were checked mathematically before writing them:
zero base and quotient rings; empty matrices; constant monic factors; e=0 and e=1; and an
ordinary nontrivial CRT splitting. The Jacobson hypothesis in the monicity statement matters:
over A=Z×Z, I=0×Z, T=0 and the one-by-one projection P=(1,0), D reduces to X modulo I but has
leading coefficient (1,0), so it is not monic over A. This ideal is not contained in Jac(A).
The CRT statement only concerns reduction and remains valid for an element that is not
idempotent before reduction.

## New nodes

`def-weil-pbc-idempotent-charpoly` defines the explicit ambient determinant polynomial for
arbitrary matrices T,P. It replaces no existing definition and is used only through new
proof imports of the item. Its source is the characteristic-polynomial paragraph of Tag 09XI,
with the explicit matrix realization written by G2.

`lem-weil-pbc-idempotent-charpoly-mul-complement` states and proves that the determinant
polynomials for complementary commuting projections multiply to the ambient characteristic
polynomial. Its source is the same paragraph, made into elementary matrix algebra; its Lean
proof is complete and has only the three accepted axioms.

`lem-weil-pbc-idempotent-charpoly-monic` isolates the constant-rank/Jacobson argument for
one arbitrary commuting idempotent. Its complete proof in words uses finite standard covers,
locally constant rank, monic degree preservation at residue fields, and coefficientwise
injectivity on a standard cover. Its only remaining proof is the named theorem above.

`lem-weil-pbc-adjoinRoot-idempotent-charpoly-map` isolates coefficient reduction and the
CRT block-matrix calculation. Its proof in words explains power-basis base change, the CRT
projection, determinants of the two blocks, and the characteristic polynomial of the monic
quotients. Its only remaining proof is the named theorem above.

Each new node records real searches of all three prescribed kinds, including LeanSearch's
unavailability, and inherits the original node's chapter, unit, and blueprint ancestor.
No change record is needed: existing statements, definitions, and publicly visible imports
are unchanged.


## Second reading by G2

1. Interface: PASS. Compared the existing module with the repository using `diff -u`
   and compared its complete theorem signature byte for byte. The signature and four
   public imports are unchanged. The existing node changes only `proof`, `proof_deps`,
   and `proof_origin`. The four additional modules introduce new declarations only;
   no existing definition or target statement is modified, so no change record is needed.
2. Proof: PASS as a partial reduction. Independently compiled all five delivered modules
   using `lcompile.py --all`, without errors or warnings. Scanned every delivered source:
   precisely the two reported public named theorems have whole-proof `sorry`; there is
   no hollow definition, forbidden declaration, or hidden unfinished proof. Added
   `#print axioms` to a temporary scratch copy and compiled it: the determinant definition
   and complementary product theorem use only `propext`, `Classical.choice`, `Quot.sound`;
   the target and the two open intermediate theorems additionally use `sorryAx` only.
   Removed the scratch copy before delivery.
3. Split statements: PASS. Independently checked the constant-rank argument: the differing
   rank locus is closed because rank is locally constant; any nonempty such locus contains
   a maximal ideal, which contains I, contradicting monicity of the reduction. Coefficient
   descent on a standard cover proves actual monicity over A, not merely monicity over
   residue fields. Checked the CRT argument: after base change P is the specified projection,
   so the determinant is the characteristic polynomial of the selected quotient, including
   empty blocks. Rechecked zero rings, empty matrices, P=0/P=1, degree-zero factors, and
   e whose reduction alone is idempotent. Both statements have complete docstring proofs
   and matching nodes, and each is strictly a part of the original argument. Independent
   LeanFinder searches used direct-summand/projector/constant-rank and scalar-extension/CRT
   wording; the returned free-module characteristic-polynomial and universal-factorization
   results do not state either missing step. Repository searches likewise found no duplicate;
   the existing field theorem about the characteristic polynomial of an idempotent itself
   differs from the characteristic polynomial of T on its summand. Neither remaining
   statement can be closed in a few minutes from these results.
4. Route and pruning: PASS after documentation repair. The explicit determinant gives a
   genuine shorter route below the unit level. Inspected `dag/units/sk-thm-p1.json`:
   the item is absent from its realized statement and step lists, which remain unchanged.
   Checked the imports against the signatures and proof: public imports supply statement
   or definition symbols; new imports needed only by the existing proof are plain imports.
   The report now enumerates all five old direct dependencies omitted from the new target
   proof, distinguishing the three removed globally on this branch from the rank and cover
   nodes still used below the monicity step.
5. Nodes: PASS. Checked all five node records against the Lean declarations and argument;
   every `proof_deps` equals the union of its proof steps' `uses`. New nodes have sources,
   proof origins marking the agent's explicit matrix calculation, search records, creation
   records, blueprint ancestry, chapter/unit, and matching Lean records. The determinant
   has complete data; the product node has a complete kernel-checked proof; the two open
   nodes state the exact separate reductions used by the target.

Changed only the existing theorem's proof docstring to match the actual determinant
argument and the report's description and complete direct-dependency pruning list.
No proof, signature, definition, public import, or node needed repair.
