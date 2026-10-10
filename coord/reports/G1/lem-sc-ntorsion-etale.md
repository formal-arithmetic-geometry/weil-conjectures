1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-ntorsion-etale.json`: split item.
- `dag/nodes/sec-abelian-varieties/lem-sc-coprime-torsion-decomposition.json`: Mathlib leaf, `Submodule.torsionBy_isInternal`.
- `citations.json`: verbatim statement quotes for every step citation.

2. Attachments:

- `AlgebraicGeometry.etale_torsionSubgroupScheme` remains attached to this item but is not closed: the slopmaster2 audit says it rests transitively on sorry declarations.
- `AlgebraicGeometry.bijective_toUnit_comp_torsionSubgroupScheme` remains attached to this item but is not closed for the same reason.
- `AlgebraicGeometry.nonempty_addEquiv_torsionBy` remains attached to this item but is not closed for the same reason.

3. WANTED:

None.

4. Problems found and corrected:

The imported proof had an uncited second paragraph and cited `lem-sc-isogeny-facts` even though the route only needs the more precise finite-flat node. I replaced it with three complete steps. The first uses the existing finite-flat, étale-kernel, and finite-étale-points statements. The second spells out divisibility, commutativity, the kernel-point identification, and the prime-power structure argument. The third isolates the coprime decomposition as a Mathlib leaf and states the Chinese-remainder identification explicitly. The item and new node now have blueprint references and all searches are recorded, including LeanSearch's unavailable result.

## Review by G1

I read the imported item and the unit proof in `sk-prop-av-ntorsion-etale`, the Lean declarations in `WeilConjectures/AlgebraicGeometry/AbelianVariety/Torsion.lean`, and the statements of every cited DAG node. Step 1 takes exactly finite flatness and kernel order from `lem-sc-mult-n-finite-flat`, étaleness under the characteristic hypothesis from `lem-sc-mult-n-etale-kernel`, and point cardinality/base-change bijectivity from `lem-sc-finite-etale-points`; these statements include the required algebraically closed field and extension hypotheses. Step 2 uses the stated surjectivity of multiplication, the abelian-group conclusion, the finite kernel order, and the divisible-group prime-power classification. Step 3 uses only the Mathlib leaf's internal direct-sum decomposition; the remaining kernel identification and Chinese-remainder isomorphism are elementary consequences of the definitions and Bezout. I checked that no cited statement is being used for proof material absent from its statement, and that the new leaf is an exact statement of `Submodule.torsionBy_isInternal` at Mathlib line 534. The small cases n=1 and n a single prime power reduce respectively to the trivial decomposition and the prime-power step.

## Second reading by G1

- Item statement: checked against the blueprint node `lem-sc-ntorsion-etale` and unit `sk-prop-av-ntorsion-etale`, clause by clause; finite etaleness, algebraically closed extension base change, and the `(Z/nZ)^(2g)` group description agree, including `n` prime to `char k`.
- Step 1: checked the statements of `lem-sc-mult-n-finite-flat`, `lem-sc-mult-n-etale-kernel`, and `lem-sc-finite-etale-points`; they provide finite flatness/order, etaleness under the stated characteristic hypothesis, and point cardinality/base-change bijectivity. No unproved non-elementary fact is used.
- Step 2: checked `lem-sc-isogeny-surjective`, `lem-sc-av-commutative`, `lem-sc-mult-n-finite-flat`, `lem-sc-finite-etale-points`, and `lem-sc-divisible-group-structure`; their hypotheses apply to `A(k)` and to each prime-power factor of `n`, and the subgroup/kernel identifications are definitional.
- Step 3: checked `lem-sc-coprime-torsion-decomposition`; its torsion-by decomposition applies to the `Z`-module `A[n](k)`. Identifying kernel points and applying Chinese remainder are elementary Bezout consequences, so the step is correctly marked elementary.
- New node `lem-sc-coprime-torsion-decomposition`: checked B1-B7 against `Submodule.torsionBy_isInternal` in `Mathlib/Algebra/Module/Torsion/Basic.lean:534`; the statement is self-contained, cites its direct-sum definition, has no proof content, and records LeanFinder, Loogle, grep, and unavailable LeanSearch searches.
- Small cases: `n=1` gives the trivial group and empty prime-power product; one prime-power factor reduces Step 3 to the identity decomposition. The zero-dimensional case gives the trivial torsion group, consistent with the statement.

No changes were required after this second reading: the worker's three-step repair already removes the uncited paragraph and the unnecessary isogeny-facts dependency. The dry-run delivery check passed.
