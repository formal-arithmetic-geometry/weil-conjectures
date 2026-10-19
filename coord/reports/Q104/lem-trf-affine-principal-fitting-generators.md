# Worker report: lem-trf-affine-principal-fitting-generators

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-affine-principal-fitting-generators.json`: statement item split into five steps, statement unchanged.
- `citations.json`: one entry per step/node pair, using the exact statement of each cited node.
- `searches.jsonl`: actual msearch results; `repair.py`: sandbox-only preparation script.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. Existing Fitting-ideal, finite-module, adjugate, and determinant nodes cover the ingredients.

## Attachments

None. The slopmaster2 and upstream master `WeilConjectures/` searches for the exact blueprint id and for principal/Fitting terminology found no project declaration stating this item. No source compilation was run.

## WANTED

None.

## What was wrong and what changed

The imported item agrees exactly with Stacks Tag 080Z, `lemma-principal-fitting-ideal`, and had no proof. Its statement and statement dependencies are unchanged. I expanded the proof, including the `f=0`, `n<=k`, and `k=0` cases. No finite presentation hypothesis is added: only a finite free surjection is needed, and its kernel need not be finitely generated.

The first draft confused kernel-row and kernel-column orientations and asserted divisibility of the lower adjugate block without the determinant calculation. I repaired it before delivery: the final relation matrix is explicitly `Z=(D E)` with kernel rows, multiplication is on the left by `adj(D)`, and Step 4 computes each entry of `adj(D) E` as a replaced-column determinant. The initial dry run also rejected three citations because I had omitted literal TeX dollar signs/reference text. I regenerated all quotes directly from the node statements.

The current blueprint ancestor is `lem-trf-local-term-locality`, through the existing alteration/flatification chain. I read its current main-20261015 proof and the unit `sk-i-curve-zero`: neither has a literal Fitting-ideal sentence. This is a generic local-algebra tool below the inherited geometric chain, not a replacement of any unit-level step. Searches of the whole blueprint with `blueprint_refs.py search 'Fitting'`, `'080Z'`, and `'principal Fitting ideal'` returned no match; `same_as=[]`. I leave chapter, unit, and ancestry unchanged and identify the concrete Stacks proof in `from.place`.

## Review by Q104

I read Stacks More on Algebra Tag 080Z (`more-algebra.tex`, `lemma-principal-fitting-ideal`, including its entire proof), and Algebra Tag 080R (`algebra.tex`, `lemma-matrix-right-inverse`, including its cofactor proof). Every hypothesis matches: the ring is commutative and local, the module is finite but not necessarily finitely presented, `k` is any nonnegative integer, the Fitting ideal equals `(f)`, and the quotient removes the elements killed by exactly `f`, not by an unspecified power. The item remains unchanged.

Step 1 uses the full definition statement of `def-weil-finitely-generated-module`, which supplies the finite spanning family. Its quotient images span by applying the quotient map to a linear combination. If `f=0`, the quotient is zero; if `n<=k`, the original family already gives the bound. These are elementary and avoid empty or negative minors.

Step 2 uses precisely the statement of `lem-trf-fitting-ideal-independence-base-change`, which defines the ideal as the minors of relation rows and asserts presentation independence. Here `n>k`, so the specified minors have size `r=n-k>0`. The local Nakayama consequence is written out in three lines without another theorem: `f=sum a_l delta_l`, `delta_l=b_l f`, and if all `b_l` are nonunits then `1-sum a_l b_l` is a unit annihilating nonzero `f`. In a commutative local ring nonunits form its maximal ideal, and `1-s` is outside that ideal when `s` is in it. Thus one minor is `uf` with `u` a unit, even with zero divisors; no cancellation by `f` is used. This is an elementary step from the cited ideal description and the local-ring definition, not a new Nakayama node.

Step 3 uses exactly the cofactor entry formula and `adj(D) D=det(D) I` of `lem-weil-pbc-matrix-adjugate-identity`. The relation matrix has `r` rows and `n=r+k` columns, so `H Z` still has relation rows and its first block is `uf I_r`. This corrects the first draft's orientation error. The cited node states the required identity over any commutative ring; no invertibility of `D` is assumed.

Step 4 uses the Leibniz formula from `def-weil-pbc-matrix-determinant`: grouping permutations according to their selected row in the replaced column gives the displayed cofactor sum. This is the routine finite-sum calculation in Tag 080R, transposed, rather than an omitted matrix-comparison lemma. Each replaced-column determinant uses the same distinct relation rows and distinct generator columns as a valid Fitting minor, up to its order sign; the kernel-minor statement of `lem-trf-fitting-ideal-independence-base-change` therefore puts it in `(f)`. This proves every entry is an `f` multiple without cancelling a zero divisor. No extra right-inverse node or clause-equivalent node is created.

Step 5 uses only the constructed relations. The elements `u x_i+sum c_il x_(r+l)` are in the specified annihilator submodule, so the inverse of the unit `u` expresses each of the first `r` quotient generators in terms of the last `k`. No torsion freeness or equality of Fitting ideals after quotienting is asserted. For `k=0` these relations show the entire quotient is zero.

I checked the edge cases `f=0`, zero module/zero generating family, `k=0`, `n=k`, and `n<k`. I also tested a field, the free module `A^k` with `f` a unit, and `A=Z/4Z`, `M=A/(2)`, `k=0`, `f=2`: the latter has a nonzero zero divisor but the module is killed by `f`, so its quotient is correctly zero. A case with a nonzero quotient and a zero divisor is `A=Z/4Z`, `M=A + A/(2)`, `k=1`, `f=2`; its quotient is generated by the class of the free summand's generator. These tests rule out an illicit cancellation of `f` and confusion between the annihilator and power torsion.

For B--E: there are no new-node form, Mathlib-match, duplicate, or restatement issues. I searched the whole DAG for 080Z, principal Fitting ideals, matrix-right-inverse, Nakayama, and adjugates and opened every cited statement. Quotations are verbatim, not claims from their proofs; proof_deps is their exact union. The matrix/finite-sum calculations are explicit, no step exceeds 2000 characters, no non-elementary lemma is hidden in a long step, and all sources are Stacks (no SGA). The item itself was searched with msearch using LeanFinder, Loogle, grep, LeanSearch, and a second semantic phrasing; results are appended verbatim from searches.jsonl, preserving all inherited research. The first grep used an unhelpful `Mathlib` subdirectory and returned zero hits; the final unrestricted grep corrected it and found only unrelated Fitting decomposition/Lie-module names. None of the search hits states this Fitting ideal criterion.

## Not duplicates

No new nodes were created, hence no new/existing pairs require comparison.

## What could not be finished

Nothing remains unfinished for this stage-1 split.
