## Files written

- dag/nodes/sec-zeta-weil/lem-embedding-extension.json: item, statement retained, seven proof steps, status split.
- dag/nodes/sec-zeta-weil/lem-weil-padic-algebraic-closure-cardinality.json: statement-only node, not an exact Mathlib match; project attachment candidate below.
- dag/nodes/sec-zeta-weil/lem-weil-complex-cardinality.json: statement, Mathlib leaf Cardinal.mk_complex, Mathlib/Analysis/Complex/Cardinality.lean:25.
- dag/nodes/sec-zeta-weil/lem-weil-countable-base-transcendence-cardinality.json: statement, Mathlib leaf IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt, Mathlib/FieldTheory/IsAlgClosed/Classification.lean:122 (same-universe version :149).
- dag/nodes/sec-zeta-weil/lem-weil-complex-algebraically-closed.json: statement, Mathlib leaf Complex.isAlgClosed, Mathlib/Analysis/Complex/Polynomial/Basic.lean:52.
- citations.json: verbatim statement quotes for every step's every cited node.

Four new nodes, three Mathlib leaves. All new nodes have empty proof/proof_deps; the p-adic node is left unsplit pending the maintainer's attachment verification. The unit's key node is sk-thm-intfactors, not this lemma, so its realized fields are untouched.

## Attachments

PadicAlgCl.mk_eq_continuum belongs to lem-weil-padic-algebraic-closure-cardinality, WeilConjectures/Mathlib/NumberTheory/Padics/Complex.lean:58-63 in /home/ubuntu/weil-src-slopmaster2. The new node states precisely the canonical PadicAlgCl algebraic closure, not a chosen arbitrary algebraic closure. Its proof is sorry-free. I read its project dependencies Padic.mk_le_continuum (:41-51) and Padic.mk_eq_continuum (:54-55): their proofs have no sorry and use Mathlib only. The declaration was not in the archived compressed sorry maps; this is source evidence for the candidate, not a regenerated audit. The candidate is recorded in lean_candidates, with final audit/attachment left to the maintainer.

There is no attachment for the item. Searching the blueprint tag, its id, extension/embedding and intrinsic-weight concepts in WeilConjectures/ found no declaration of all three clauses. PadicAlgCl.nonempty_ringEquiv_complex (:67) does not assert agreement with a prescribed embedding of a number field, nor the intrinsic-weight and Galois clauses. Mathlib is not treated as a project attachment. Master source is reference material only.

## Wanted literature

None. The blueprint statement/proof, Stacks field-theory source and all pinned Mathlib/project declaration sources used here are available locally. No literature was downloaded.

## What was wrong

The statement agrees with main-20261015, whose node markdown contains the statement but no proof; no blueprint_update is present. The master node includes the proof I checked. No statement dispute or change is needed.

The imported first step cited only an algebraic-closure definition while using cardinality, existence of transcendence bases and extension/uniqueness theorems. The imported second step did not ensure that any realization existed, so a universal assumption over realizations could have been misread as vacuous. It also used finiteness of the simple algebraic extension without a theorem citation. The imported final step had an incorrect non-elementary marker for a direct composition-of-embeddings argument. These points are repaired in the proof.

The direct-base variant takes transcendence bases over the original countable number field L, with the complex L-structure given by sigma, rather than first passing to the two relative algebraic closures of L. This omits an unnecessary intermediate object while retaining exactly the unit's embedding-transport route: match bases, identify rational function fields, and extend to algebraic closures. It changes no unit/chapter statement or route. The proof is marked agent-written because this is a simplification of the blueprint proof, not a verbatim literature proof.

## Unfinished work

No part of the item's natural-language argument is left unfinished. The statement-only p-adic cardinality node awaits the ordinary independent attachment check, not a Lean proof from this worker. Stage 1 only: no Lean file written, compiler/Lake/build run, agent started, or live repository/launcher changed.

## Not duplicates

lem-weil-countable-base-transcendence-cardinality vs def-weil-pbc-transcendence-basis: the existing node defines algebraic independence and algebraicity over the generated field; the new lemma computes the size of a basis of an uncountable algebraically closed field over a countable base.

lem-weil-countable-base-transcendence-cardinality vs lem-exc-transcendence-basis-algebraic-closure: the existing node says the ambient field is an algebraic closure of the basis-generated fraction field; it asserts no cardinality equality. Both existing statements are cited, not copied.

I searched every DAG node and the whole imported blueprint by cardinality, countability, transcendence, transcendence basis, complex numbers, fundamental theorem, extension of embeddings, and the precise candidate declaration names. No existing statement gives any of the four new facts. In particular 030F only gives existence/equipotence of bases of a single extension; it does not compare an ambient uncountable field with its basis. The four children supply general tools or ambient-field facts, and none restates the prescribed-extension, intrinsic-weight or Galois-stability clauses.

## Review by Q153

I read the item in the master and main-20261015 blueprints, its chapter and its integral-Frobenius-factor unit. The unit needs this lemma specifically to transport weight conditions between realizations and embeddings; the new proof still supplies that algebraic input. I read delivery-errors B-E in full and checked the actual statements of every cited node, not their proofs. I also compared the potential project attachment PadicAlgCl.nonempty_ringEquiv_complex with the full item; it is strictly insufficient for prescribed restriction.

For the new p-adic cardinality node I read the whole project file WeilConjectures/Mathlib/NumberTheory/Padics/Complex.lean: the upper bound uses rational Cauchy sequences and the lower bound completeness of Q_l, followed by algebraic-extension cardinality and the injective inclusion into the closure. Its exact proven declaration states the canonical closure, so the item separately transports it to its arbitrary chosen closure by 09GV. Mathlib searches for this node used two distinct semantic phrasings and two source patterns; they return ingredients, not the equality. For the complex cardinality node I read Cardinal.mk_complex and its proof at line 25: C is equivalent to R times R, and infinite cardinal multiplication leaves continuum unchanged. For the basis cardinality node I read Classification.lean:122-151 and the preceding cardinal bound: countability of the coefficient ring and strict uncountability of the ambient field are both essential. For complex algebraic closedness I read Complex.exists_root and Complex.isAlgClosed (:52). Each leaf's signature is an exact match or the documented one-line field specialization. Every recorded query was run through msearch.py; searches.jsonl records the actual results. No unavailable service was reported as absence.

Step 1 uses def-weil-number-field exactly for characteristic zero and a finite rational basis, and def-weil-field-extension-isomorphism exactly for injectivity and the extension structure specified by sigma. Countability is the explicit finite-coordinate argument Q^n; it is elementary, and is not made a new node.

Step 2 uses the assumption of an algebraic closure as defined by def-weil-algebraic-closure, the new complex algebraic-closedness statement, and the two exact ambient-field cardinality statements. I checked that lem-pc-algebraic-closure-exists-unique clause (2) actually gives an isomorphism commuting with the Q_l structure maps. Both closures are algebraic over Q_l; there is no completeness assumption on Q_lbar. The p-adic closure here is the algebraic closure, not its completion C_l. Cantor's inequality is elementary set theory and gives strict uncountability without the continuum hypothesis.

Step 3 cites lem-exc-transcendence-basis-exists for existence in each field extension. The new basis-cardinality lemma has precisely the countable-base, algebraically-closed and uncountable hypotheses just established. It gives equality with the ambient field, not merely equality of two bases within one extension; this distinction prevents a C4 error. Equipotence means a bijection, which is the chosen e.

Step 4 cites the definition def-weil-pbc-transcendence-basis for injectivity of polynomial evaluation and the generated rational function field. It writes the coefficient substitution a to sigma(a), the variable renaming, both inverse substitutions, and the fraction well-definedness equation. Thus it is a routine explicit polynomial/fraction argument, not a hidden assertion that an arbitrary field isomorphism happens to preserve L. This step is elementary in the sense of the brief: the two variable-renaming maps are inverse on generators, and cross-multiplication checks extension to fractions. No non-elementary existence theorem is silently used here.

Step 5 cites lem-exc-transcendence-basis-algebraic-closure for exactly its statement that the ambient field is an algebraic closure of the fraction field of the polynomial subalgebra. It then uses lem-pc-algebraic-closure-exists-unique clause (2) over the SAME base field K, after explicitly specifying C's K-structure through the constructed isomorphism and pulling polynomial coefficients back. This establishes the prescribed restriction iota(a)=sigma(a), rather than just an unqualified ambient isomorphism. I did not take a construction hidden in either cited node's proof. This also checks the non-elementary/elementary boundary: closure uniqueness is a cited theorem, and the coefficient pullback is the written elementary argument needed to meet its hypothesis.

Step 6 cites lem-weil-realization-exists for both existence and rational compatibility of jmath, and lem-weil-pbc-algebraic-generators-finite-extension for finiteness of Q(alpha). I read its statement and the Stacks 09GH lemma-algebraic-finitely-generated source; it permits a single algebraic generator in any ambient field and needs no finiteness of the ambient extension. def-weil-number-field and def-weil-simple-field-extension supply the notions of the finite extension and Q(alpha). The images of a finite basis show L_tau is a number field. The inverse of jmath is taken ONLY on its image L_tau, not on all Q_lbar. The first clause then applies with this new number field and its composite embedding, and the equality iota_tau(jmath(alpha))=tau(alpha) is explicit.

Step 7 uses def-weil-numbers exactly for the all-complex-embeddings condition, and def-weil-simple-field-extension for the smallest generated subfield. It restricts gamma to the correct domain and codomain and composes with tau'; gamma fixes Q and preserves nonzero elements. This proves stability for any Weil number, even without the antecedent involving all realizations. It does not infer a global stability claim only for the one alpha considered in step 6.

Edge cases checked: L=Q and the unique rational embedding; finite-degree number fields with different complex embeddings; q=2 and i negative (the radius stays positive); alpha=0 (the realization hypothesis cannot hold because the radius is positive); beta=1 at weight zero; gamma the identity and its inverse. An empty or countable transcendence basis is excluded by the strict uncountability hypothesis, not assumed impossible for all fields. No topology or continuity is imposed on the extension: a continuous Q_l-to-C isomorphism would be the wrong statement. No SGA source or geometric input enters.

Each proof step is under 2000 characters, with lengths 513, 732, 493, 1123, 959, 1099, 1012. I inspected the polynomial identification and coefficient pullback explicitly for a hidden lemma. Neither contains an independent non-elementary subclaim; the genuine tools are the separately cited existence, cardinality, algebraic-closure and finite-generation statements. Statement dependencies now include every notion used, proof_deps is the union of the step citations, and citations.json copies only text actually present in each cited statement. The new declarations do not depend on the item, so no new cycle is introduced. All off-unit proof citations are existing Mathlib leaves; no off-route theorem replaces the unit's argument.
