## Worker report

1. Files written: `dag/nodes/sec-trace-formula/lem-trf-polynomial-nonzero-ideal-quotient-dimension-bound.json` (item, statement, split using existing nodes; not an exact Mathlib match); `citations.json` (verbatim statement excerpts for all seven step citations). No new nodes or Mathlib leaves were created. The item's original statement, source, ancestry, and earlier recorded searches were retained; five actual logged searches were added.
2. Attachments: none. Searched `lean/WeilConjectures/` for the item tag and for polynomial quotient/nonzero-kernel dimension terminology. No project declaration proves this item exactly. `AlgebraicGeometry.topologicalKrullDim_spec_le_of_quasiFinite_over_mvPolynomial` in `WeilConjectures/RingTheory/DimensionQuasiFiniteOverPolynomialAlgebra.lean` gives a weak polynomial-source bound in a different situation, not this strict quotient bound.
3. WANTED: none.
4. The unsplit item was mathematically correct. Its source's final kernel inference omitted the dimension-drop argument. This split supplies that argument without introducing a renamed copy of the item. The current blueprint `latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md` follows the contracting-correspondence route, while this existing deep auxiliary retains its historical nearby-cycle/valuation-fibre ancestry. I have not changed the unit, its route, or any target. The auxiliary proves precisely the polynomial-quotient input used by its direct parent.
5. Unfinished mathematics: none at this split level. Delivery checks are run with the authorized delivery tool on the server. No Lean was written or compiled, and no repository or launcher file was changed.

## Proof and sources

Read `literature/stacks-project/algebra.tex`, Tag 00QK, label `lemma-finite-type-domain-over-valuation-ring-dim-fibres`, especially its final sentence: a nonzero residue-polynomial kernel forces dimension less than the number of variables. The item isolates the polynomial quotient part of that inference; it neither asserts nor uses a quasi-finite dimension comparison. Its proof is an agent-written expansion of that omitted commutative-algebra inference, honestly recorded with `proof_origin.by = agent`.

Read installed Mathlib `RingTheory/KrullDimension/NonZeroDivisors.lean:37-66` and `RingTheory/KrullDimension/Polynomial.lean:118-133`. The former gives the successor inequality for any surjection killing a nonzerodivisor, without Noetherian or locality hypotheses; the latter gives dimension of a polynomial algebra over a Noetherian ring. Read `Algebra/MvPolynomial/Basic.lean:203-204` for the domain instance. All are already represented by existing DAG nodes. The field's ideals and the arithmetic of finite natural dimensions are written out as elementary steps, not new nodes.

Logged searches used LeanFinder, Loogle, grep, and LeanSearch. The second LeanFinder phrasing about a surjective polynomial homomorphism with nonzero kernel found `ringKrullDim_succ_le_of_surjective`. This is an ingredient, not an exact or one-line match for the item's entire conclusion. Loogle's indexed polynomial-dimension signature differs slightly from the installed version, so the installed source was read and used. Existing DAG nodes already cover both signatures' finite-variable specialization. The old imported searches remain evidence of the previous search question, and no unrun search was recorded.

## Not duplicates

No new nodes. Reused `lem-trf-surjective-kernel-nonzerodivisor-dimension-drop`, `lem-sf-noetherian-polynomial-dimension`, and `lem-weil-pbc-polynomial-ring-domain`, rather than duplicating those ingredients. Whole-DAG concept searches and `tools/blueprint_refs.py search` for polynomial dimension, polynomial ring, and nonzerodivisor yielded no imported blueprint node stating the exact item. `blueprint.same_as` remains empty. The latter two reused nodes are Mathlib leaves; the surjective-bound node is in this item's own unit, so no undeclared route departure is needed.

## Review by Q12

I checked the unchanged statement against the final nonzero-kernel inference in Stacks 00QK, and read the statements of every dependency used below. There are no new nodes whose independent sources or hypotheses need review. The proof has five short steps, with a total of less than 3000 characters; none is longer than 2000 characters or hides a comparison lemma.

Step 1 uses `def-weil-pbc-noetherian-ring` only for its actual finite-generation definition, and `def-weil-pbc-krull-dimension-ring` only for the prime-chain definition. The argument that a nonzero field ideal contains 1 explicitly verifies that the field has finitely generated ideals and exactly one prime ideal; this proves the two facts needed in step 2, rather than assuming them from a definition citation.

Step 2 uses the statement of `lem-sf-noetherian-polynomial-dimension`: the coefficient ring is the commutative field k, its Noetherian hypothesis was proved in step 1, and the variable set has finite cardinality n. That statement really gives dimension k plus n, so substituting dimension k = 0 computes dimension P = n.

Step 3 uses `lem-weil-pbc-polynomial-ring-domain` for precisely its assertion that a polynomial ring over a domain is a domain. The field is a nonzero domain. With the chosen nonzero f in I, the zero-product property proves that multiplication by f is injective; no additional nonzerodivisor theorem is silently invoked. `def-weil-pbc-algebra-hom-quotient` explicitly states that the quotient map is surjective with the stated kernel, so this is a legitimate use of that definition node's statement, not a theorem assumed from its proof. It applies even when I is the whole ring.

Step 4 uses `lem-trf-surjective-kernel-nonzerodivisor-dimension-drop` exactly as stated. Both rings are commutative, q is unital and surjective, f is a nonzerodivisor in the source, and q(f) = 0. Crucially its statement allows a zero target and requires neither a local source nor a proper ideal. Thus it gives dimension R + 1 at most dimension P; I did not use the local equality theorem for a nonzerodivisor quotient.

Step 5 reads the extended dimension convention from `def-weil-pbc-krull-dimension-ring` and handles bottom, infinity, and finite values separately. With n finite, infinity is excluded by the successor bound; with n positive, ordinary integer arithmetic gives the claimed n-1 bound. This also checks n=1, where every proper quotient in question has dimension zero. For I=(t_1) the bound is attained; for I=P or any ideal containing a nonzero constant, the quotient is zero and dimension is bottom. I=(0) is correctly excluded by the hypothesis. No assumption that I is prime, principal, radical, or proper was introduced.

Against delivery-errors B-E: all cited ids already exist, each non-elementary step cites the statement actually used, every definition-only step contains its elementary argument, and every citation has a verbatim excerpt in citations.json. There are no new nodes, disguised restatements, circular constructions, missing source documents, false edge cases, or changed hypotheses. I checked that the proof only adds edges to pre-existing generic tools and definition/Mathlib leaves. Nothing was corrected in the statement, and no STATEMENT-DISPUTED issue was found.

## Delivery validation

The first dry run rejected the polynomial-dimension excerpt because it was shorter than the citation tool's minimum of 40 characters. I replaced each excerpt with the cited node's complete statement, retaining exact verbatim text and all hypotheses. No mathematical change was needed.
