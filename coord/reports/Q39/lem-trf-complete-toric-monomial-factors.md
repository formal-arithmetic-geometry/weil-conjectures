## Files written

- `dag/nodes/sec-trace-formula/lem-trf-complete-toric-monomial-factors.json`: repaired split; statement preserved verbatim from current main.
- `dag/nodes/sec-trace-formula/lem-trf-complete-toric-kato-recognition.json`: one new statement-only literature interface, unsplit; Mathlib searches found no match.
- `citations.json`: statement quotes for both steps citing the interface.
- `searches.jsonl`: original search log retained and five changed-question searches appended by msearch.py.

The never-merged boundary-class and facet-primes nodes have been withdrawn from this proposed delivery. Their original files, the entire returned item proof, report and citations remain in `repair-history/returned/` in this sandbox. They are not deleted from the live DAG: neither child id exists there. The delivery contains one new node, not those two old candidates. Current main differs from the retained item in split fields and creation metadata; this repair starts from current-main metadata and replaces the split, preserving the statement and original Mathlib records.

## Attachments

None. Searched both the exact blueprint tag and log-regularity/divisorial/monomial-factor concepts under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; the only incidental divisorial hit was the Riemann--Roch line-bundle result, which is not this assertion. Read-only master source was also searched and supplies no finished proof for this interface. No Lean or compiler was run.

## WANTED

WANTED: Kazuya Kato (1994), Toric singularities, Theorem 11.6, for `lem-trf-complete-toric-kato-recognition` (complete-local divisorial recognition).

WANTED: Wiesława Nizioł (2006), Toric singularities: log-blow-ups and global resolutions, Proposition 2.6, for `lem-trf-complete-toric-kato-recognition`; ILO VI 1.4 explicitly cites this reference.

The existing normality node separately mentions Kato 4.1. The new proof does not use it. The interface's primary proofs remain open work; this delivery does not claim to have read or proved them. No documents were downloaded.

## Statement dispute and corrections

STATEMENT-DISPUTED: the returned boundary-class node's assertion that saturation and sharpness imply the full orthant equality is false. For
`P = <(1,0),(1,1),(1,2)>` and `lambda(a,b)=(b,2a-b)`, the group image consists of pairs with even coordinate sum. Thus `(1,0)` is nonnegative but not in the image. The correct formula is `lambda(P)=lambda(P^gp) intersect N^F`, not `N^F`. The A1 cone has the stated Z/2 class-group obstruction. The old report's claim that its A1 test validated the stronger equality was wrong. This delivery withdraws that node entirely rather than delivering an unused corrected class-group lemma.

The item's statement is true and is unchanged. Its previous source text claiming an algebraic sublemma/divisorial calculation after ILO VI 1.4 has been corrected: that paragraph states `M_X = O_X intersect j_* O_U^*` and cites Nizioł 2.6; there is no such algebraic sublemma. VI 1.6 gives the two completed models, with precisely the same condition on the Cohen parameter.

## Not duplicates

- lem-trf-complete-toric-kato-recognition vs lem-trf-complete-toric-monomial-factors: this is expressly the honest literature interface authorized in the return, namely the complete-local recognition equality for all functions invertible after chart localization. It implies the item by the explicit inverse calculation, and conversely the item gives it by clearing a localization inverse. I do not claim it is a strictly smaller independent class-group computation. The mathematical work remains exposed as an unsplit Kato/Nizioł literature theorem.
- lem-trf-complete-toric-kato-recognition vs lem-trf-log-regular-divisorial-structure: the existing node concerns an arbitrary locally Noetherian log regular fs log scheme and sheaf identification, together with openness, density and normality. Its current proof uses this item. It cannot be cited to prove its own complete-local input without a cycle. The new interface instead states the complete-model ring equality, including the arbitrary Cohen residue field case, without importing that parent theorem.
- lem-trf-complete-toric-kato-recognition vs lem-trf-log-regular-saturation-normality: normal-domainness alone does not identify units on the monomial localization with unit times chart monomials.
- lem-trf-complete-toric-kato-recognition vs lem-trf-regular-local-ufd-boundary-factorization: that node assumes an ordinary regular local ring and a subset of a regular system of parameters. The saturated cone models here can be singular; the A1 model is one such example.
- lem-trf-complete-toric-kato-recognition vs lem-trf-completed-monoid-support-projection: a supported-series embedding and module retraction do not themselves assert recognition of monomial-localization units, particularly after the Cohen quotient.

Searched the whole DAG by Kato 11.6, Nizioł 2.6, recognition, toric, divisorial, monomial and boundary-class concepts. Read the existing divisorial-structure, normality, regular-local-UFD, associated-log, monoidal-ideal-contraction, orthant-embedding and support-projection statements. Whole imported-blueprint searches for divisorial, toric, Kato and recognition returned zero matches; monomial returned seven unrelated polynomial/projective-space nodes. The ancestor tool still returns lem-trf-local-term-locality. No new blueprint-equivalent node was found. The retained ancestry and unit are unchanged.

## Review by Q39

I read the item and its returned proof beside current main, both returned children, the existing normality and divisorial-structure nodes, the current blueprint local-term statement and proof, and the sk-i-curve-zero unit and chapter. For the literature I read ILO Exposé VI 1.1--1.7, printed pp. 69--70 (PDF pp. 75--76). VI 1.4 really states the divisorial equality and references Nizioł 2.6; VI 1.6 really lists the equal-characteristic field and mixed-characteristic Cohen models. I cannot check Kato 11.6 or Nizioł 2.6 against their unavailable primary texts, so the new node is explicitly an unsplit literature interface, with WANTED lines above. This is the first alternative expressly offered by the maintainer's return. It is not represented as a new proof or a smaller equivalent theorem.

For the new statement I checked all ring data against the item's statement: P is finitely generated, integral, saturated and sharp; n is any nonnegative integer; coefficients are an arbitrary field or the given Cohen ring; theta-p belongs to the ideal generated by nonzero chart monomials and the t parameters. No perfection assumption was added. The completion and Cohen-ring definitions are exactly the three statement dependencies carried by the item. The localization is defined inline by fractions and their equivalence, and units mean elements admitting multiplicative inverses. This avoids a hidden normality assumption and any definition of class groups or Weil divisors. The new node has empty proof/proof_deps and explicit `lean_audit.master.state = none` and `lean_audit.slopmaster2.state = none`.

For step 1 I checked the definition of S and the localization map in the new statement. Since z^q is inverted, the displayed product of b with c/z^q is 1; commutativity gives the inverse in both orders. This is an elementary calculation using no divisor arithmetic. For step 2 I read the exact recognition equality in the cited statement: its right side supplies precisely r and u after step 1 supplies membership on its left side. Every hypothesis is already present in the item; both coefficient models are within the statement, so there is no mixed-characteristic transport assertion. This is the only non-elementary input. Step 3 uses no node: bc=1 gives the explicit unit inverse c when q=0, P={0} reduces to that case, and n=0 simply omits parameters. All steps are below 2000 characters; there is no long hidden comparison or unnamed lemma.

I tested the corrected recognition assertion on P={0} (localization at 1), q=0 and n=0; on k[[x,y]], where inverting x and y allows exactly a unit times nonnegative coordinate monomials among elements of the original ring; and on C[[x,y]]/(p-xy), where both coordinates become units on the boundary complement and their exponents still belong to P=N^2. On the A1 cone the admissible chart exponent vectors are only the even-sum sublattice points in the nonnegative orthant, so the new statement does not admit the nonexistent vector (1,0). These are consistency tests, not a replacement for the WANTED theorem.

I repaired the return point by point. E2: removed the false full-orthant node and recorded its explicit counterexample and correct lattice formula. D1/D2: removed the allegedly smaller class-group factorization and adopted the specifically permitted single honest recognition interface, openly acknowledging equivalence with the local factor statement. Minor (1): removed every nonexistent algebraic-sublemma citation from delivered nodes and proof steps. Minor (2): the sole delivered new node has both non-null Lean audits, after fresh project-source searches. Minor (3): withdrew the facet-primes candidate and all uses of it, so there is no theorem taking normality without an assumption. The old candidate's normality omission and its old audit/source records are not carried forward as live claims. Every non-elementary fact used now is the quoted interface equality. No off-unit tool, SGA source, or citation of the parent that depends on the item is used.

## What remains

The one unsplit recognition interface awaits the primary Kato/Nizioł references and its future split. The item itself has the complete explicit reduction to that interface. Required server dry run and push follow this review; their outputs determine the final delivery status.
