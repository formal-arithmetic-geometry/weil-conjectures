# Q70: lem-sfb-scheme-lqf-cancellation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-lqf-cancellation.json: statement item, split; no exact Mathlib match for the finite-type-inclusive Stacks predicate.
- citations.json: verbatim statement text for every step citation.
- report.md: this report. searches.jsonl was written by msearch.py.

No new nodes; no new Mathlib leaves.

## Attachments

None. Searched WeilConjectures/ for the exact blueprint tag, local-quasi-finiteness terminology, IsLocallyQuasiFinite with composition and LocallyQuasiFinite.of_comp. No project declaration states the item. AbelianVariety/Isogeny.lean:208 proves a special case only. Read QuasiFiniteMorphism.lean and QuasiFiniteMorphismComparison.lean: the latter proves a predicate comparison, not cancellation. Mathlib QuasiFinite.lean:103-105 and FiniteType.lean:72-74 cancel its component predicates, not the Stacks predicate directly.

## WANTED

None: all sources used are present locally.

## Problems found and corrections

The statement is correct and unchanged. Its empty proof is replaced by the source's affine/four-ring argument. I did not identify Mathlib's weaker LocallyQuasiFinite class with the Stacks definition. The inherited blueprint ancestor is null (blueprint_refs.py ancestor confirms None); its exact supporting source place and via chain are retained. Read the newest literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3); the auxiliary algebraic-geometry input leaves the chapter/unit route untouched.

## Unfinished work

None in this split. Existing dependency nodes retain their own proof status.

## Not duplicates

No new nodes. Searched the entire DAG by Tags 03WR, 01TK, 00PN, quasi-finite keywords, and the Mathlib candidate declarations. blueprint_refs.py searches for those tags returned no blueprint equivalents. The general affine criterion, four-ring lemma and affine-open basis already exist and are cited. The scheme composition node proves the opposite permanence direction. The algebraic-space calculus node is a user, not a prerequisite; it is not cited, so no cycle is introduced.

## Review by Q70

I read coord/delivery-errors.md sections B through E in full and checked each step against the cited statements and sources. The item's source is Morphisms Tag 03WR (lemma-permanence-quasi-finite, morphisms.tex:4002ff). Its proof explicitly reduces through Tag 01TK to the four-ring lemma with R=A, S=S'=C, R'=B. I also read Tag 01TK at morphisms.tex:3839ff, Algebra Tag 00PN at algebra.tex:30293ff, and the affine-basis Tag 01IT at schemes.tex:1952ff. There are no new nodes requiring separate source reviews.

Step 1 uses the statement of lem-weil-pbc-affine-opens-basis, which allows an affine neighborhood inside any specified open. Apply it successively in Z, Y, X to the whole space, g^{-1}(W), f^{-1}(V). Scheme maps are continuous by definition. This avoids assuming that intersections of affine opens are affine. No separatedness or quasi-compactness is used.

Step 2 uses def-weil-affine-spectrum for contravariant functoriality on restricted affine maps, and clause (1) implies (2) of lem-a1-scheme-lqf-affine-criterion. I opened both statements. The criterion explicitly includes finite type and quasi-finiteness at every prime for every compatible affine pair. The pair (U,W) is compatible because f(U) lies in V and g(V) lies in W; its hypothesis is exactly the assumption on the composite. Nothing is taken from a cited node's proof.

Step 3 uses the statement of lem-weil-pbc-quasi-finite-four-rings. I checked its commutative square, finite-type assumption, primes and generation condition: take S=S'=C and the identity on C, so every c is c times 1. The prime in S is the same r as in S'. The lemma explicitly gives finite type of B to C as well as quasi-finiteness at r, so no finite-type theorem is hidden here. This is precisely the specialization written in Tag 03WR.

Step 4 unpacks pqf-def-quasifinite, whose full statement I read: the constructed U,V and prime give its witnesses at x, and the universal condition is the local predicate. It is elementary because all substantive algebra was supplied in step 3. citations.json copies verbatim statement text for every cited node at every occurrence, including definitions.

Small cases checked: X empty is vacuous; either map an identity works; g can fail local finite type, separatedness or quasi-compactness; nilpotents and zero rings cause no problem because the algebraic lemma is for arbitrary commutative rings and is applied only at an actual prime. Spec Q to Spec Z is not an example satisfying the hypothesis: missing finite type is exactly the distinction from Mathlib. No new statement is asserted and no statement dispute occurs. All four steps are shorter than 2000 characters. The two non-elementary off-unit tools are declared in split_report.tool_uses as foundational inputs, not replacements of unit-level proofs. All writes are confined to the sandbox. No Lean was written or compiled, and no Lake/build tool was run.
