# Q157: lem-trf-valued-finite-ramification-calculus

## Files written

- dag/nodes/sec-trace-formula/lem-trf-valued-finite-ramification-calculus.json: item, split into nine proof steps, with the completeness scope corrected.
- dag/nodes/sec-trace-formula/lem-trf-galois-graded-wild-kernel.json: statement, unsplit; no Mathlib match. Defines the actual initial-form kernel P and its fixed field, with the ramification-field properties needed in the defect argument.
- dag/nodes/sec-trace-formula/lem-trf-tame-root-envelope.json: statement, unsplit; no Mathlib match. Characterizes numerical tameness by a finite etale extension of valuation rings followed by roots of prime-to-residue-characteristic order.
- citations.json: one verbatim statement quotation for every citation in every proof step.
- searches.jsonl: actual search-command log; all new-node searches were read. Earlier item searches were retained.

## Attachments

None. Searches for the item id and valuation/ramification notions in lean/WeilConjectures found no project declaration giving the item. Existing Mathlib leaves are cited as existing nodes, not counted as new attachments or new leaves.

## WANTED

WANTED: Temkin, Stable modification of relative curves, arXiv:0707.3953v3, section 2.1 pp.7--10 and section 6.2 opening p.41, for the item and both new nodes. The node's named local PDF is absent. I read the primary HTML at https://arxiv.org/html/0707.3953v3 instead; no source file was downloaded or written.

WANTED: Gabber--Ramero, Almost Ring Theory, sixth release (arXiv:math/0201175v3), section 6.2, especially Proposition 6.2.12, Corollary 6.2.14 and 6.2.16--6.2.18, printed pp.159--162, for lem-trf-galois-graded-wild-kernel and lem-trf-tame-root-envelope. I read the primary PDF online at https://websites.umich.edu/~bhattb/almost_purity_2011/almost_ring_theory.pdf. It constructs the inertia pairing, its p-kernel, prime-to-p radical extensions and the maximal tame extension. The new nodes state the finite descent/general-residue versions of these structural inputs, not proofs. The item's assembly is marked agent-written because these local archival sources are missing and the immediate-base-change argument is supplied explicitly.

## Source error

STATEMENT-DISPUTED: the imported item starts with arbitrary valued fields but asserts the prime-power defect theorem and residue lifting without a henselianity or completeness hypothesis. Take A=Q with its 7-adic absolute value, and embed B=Q(sqrt(2)) in Q_7. The simple residue root 3 of X^2-2 lifts to Q_7. Both value groups are 7^Z, and both residue fields are F_7, so B/A is immediate with e=f=1 and d=2. This is not a power of the residue characteristic 7. The two embeddings also give distinct prolongations before completion. Temkin's Lemma 2.1.5 explicitly assumes henselian fields; the present application is to complete analytic fields. I corrected the opening to say all fields below are complete. No conclusion is removed. This covers the parent analytic-type23-stability, whose fields are already complete. No target statement is edited.

The latest blueprint proof of lem-trf-local-term-locality now takes Varshavsky's contracting-correspondence route. The pre-existing auxiliary chain in this item's blueprint ancestry is recorded as such; I do not alter the chapter, unit, or parent nodes. The item is not its unit's key statement, so no realization record is changed.

## Not duplicates

lem-trf-galois-graded-wild-kernel vs lem-trf-valued-finite-ramification-calculus: the child describes a concrete Galois subgroup by its action on all initial forms and the fixed-field ramification structure; the parent has no such objects. Step 3 derives the defect result by Galois and tower arguments, rather than citing a renamed defect assertion.

lem-trf-tame-root-envelope vs lem-trf-valued-finite-ramification-calculus: the child is a root presentation after a finite etale valuation-ring extension, which the parent does not state; step 7 uses the presentation and actual etale base change to prove the parent's stability clause.

lem-trf-galois-graded-wild-kernel vs lem-sfb-epp-normal-ramification-filtration: the existing node assumes complete DVRs and concludes a filtration with four kinds of steps; the new node permits nondiscrete value groups and gives the initial-form kernel and its fixed field, including the p-primary value and residue quotient.

lem-trf-galois-graded-wild-kernel vs lem-per-tame-radical-kernel: the existing node concerns a specific strict-henselian DVR radical tower and its profinite subgroup; it does not state the finite nondiscrete Galois ramification-field properties.

lem-trf-tame-root-envelope vs lem-sfb-tame-radical-curve-normalization: that node is about normalization of a projective curve after adjoining roots of rational functions; it has no valued-field numerical characterization.

lem-trf-tame-root-envelope vs lem-trf-valued-tame-prime-tower: the existing node has p-power extensions over a complete field and prime-degree towers after tame base change, not a presentation of tame extensions themselves.

lem-trf-galois-graded-wild-kernel vs lem-trf-separable-valued-completion-factors: the existing node supplies henselian completions and completed tensor factors, not the graded wild subgroup.

lem-trf-tame-root-envelope vs lem-trf-henselian-valuation-etale-local-factors: that node describes etale local factors and unramified residue power bases; it does not adjoin roots with new values or characterize tame field extensions.

Whole-DAG statement searches and blueprint_refs.py searches for ramification, defect, unramified residue, wild inertia, tame, unramified, graded valued, and tame radical found no general version of either new statement. Mathlib's ValuationSubring.inertiaSubgroup is only a definition, as inspection of RingTheory/Valuation/RamificationGroup.lean (50--52 and the file's TODO) confirms. It is not the wild kernel theorem. The other hits are Dedekind/discrete ramification theory and ring-theoretic formal unramifiedness. Both new statements were searched by their own meanings, using two natural-language phrasings, Loogle, and logged source grep.

## Review by Q157

I read the stage-1 brief, the three blueprint levels and the unit/chapter records, and both complete B--E blocks of delivery-errors.md. I compared the node with Temkin section 2.1, Lemma 2.1.5 and its proof, and the opening of section 6.2 online. In Gabber--Ramero section 6.2 I checked the initial-form character formula (6.2.9), the p-kernel theorem 6.2.12, the radical description 6.2.14, and the maximal tame construction 6.2.16--18. For both new nodes, the quoted hypotheses allow arbitrary nondiscrete real value groups and imperfect residue fields; I did not substitute the discrete-only inertia statement from Stacks. The new nodes are statement-only, introduce their own fields, valuation rings, residue fields, groups and p=0 convention, and have no proof dependencies.

Step 1 reads four existing node statements: spectral-norm-algebraic-extension supplies an actual extending norm, algebraic-absolute-value-unique identifies all extensions, finite-normed-space-complete supplies completeness, and separable-valued-completion-factors explicitly says the valuation ring of the completion is henselian. Applying the latter to the complete field itself does not require the unrelated separable field extension to have positive degree; the identity extension is allowed. This establishes all later henselian hypotheses. These four nodes do not depend on the item.

Step 2 uses exactly the statement of valued-extension-degree-bound (finite positive e,f and ef at most degree). Coset representatives and products of vector-space bases prove tower multiplication; no norm is claimed to be discrete. The step is elementary relative to the cited degree bound.

Step 3 uses the full new wild-kernel statement, with finite Galois N, normal subgroup P, and fixed field T; that statement gives each numerical fact the step takes. N/B is Galois for an intermediate B even if B/A is not normal. Quotients of powers of p are powers with nonnegative exponent because ef is at most degree. This avoids assuming in advance that the arbitrary defect is an integer. In characteristic zero P is trivial.

Step 4 reads the actual separable-first-purely-inseparable and purely-inseparable-pth-root-tower statements. They give the required intermediate S and finite p-root tower and degree p^r. A finite value quotient killed by a p-power is a p-group; a finite purely inseparable residue extension has p-power degree. The fundamental inequality again supplies the nonnegative defect exponent. The field characteristic p case has the same residue characteristic; the characteristic-zero field case may still have positive residue characteristic, and is treated by the separable argument. These generic field results are declared off-unit tool uses, not changes to the unit route.

Step 5 uses the primitive-element theorem only for the finite separable residue extension, and henselian-local-root-lifting only for the monic coefficient lift with a simple root. The coefficients lie in A^circ and the root is lifted in B^circ, already henselian by step 1. The degree-bound statement then forces equality in both inequalities for A(b)/A, giving the numerical definition of unramifiedness. There is no appeal to a different definition of unramifiedness. If f=1, U=A works.

Step 6 is arithmetic from the preceding defect theorem, tower multiplication and the definition of separability. In particular d>=1 alone would not suffice to force both factors to be one; step 4 has first established integrality. The proof explicitly uses that stronger conclusion. Prime-to-p indices and separability pass to both parts of a tower. No extra lemma is hidden here.

Step 7 uses the root-envelope statement in both directions, etale-ring-base-change for the tensor algebra's actual etale structure, and henselian-valuation-etale-local-factors for the selected localization and its fraction field. The latter's statement explicitly gives the integral-closure valuation ring and finite etaleness, rather than merely defining an etale factor. The prime is selected by the valuation on the compositum; its contraction is the maximal ideal of C^circ. Finite base change makes the algebra finite as well. The equations and roots of unity remain valid after adjoining C. Then the already proved intermediate-field closure applies to BC inside RC. The etale base-change theorem is recorded as a generic off-unit tool use.

Step 8 gives the immediate-base-change argument itself. A residue basis and distinct value cosets give orthogonality by grouping equal-value terms and reducing their normalized sum. Because B/A is immediate, precisely the same independence argument works over B. The tensor image is a finite-dimensional domain, hence a field; this proves the degree equality without confusing intersection with linear disjointness. Matching leading coefficients in an immediate extension approximates each of finitely many coefficients with strictly smaller relative error. The orthogonal norm formula then gives the leading-term approximation by A', proving both value-group and residue-field equalities. This is an explicit calculation, not a new node restating the parent's immediate-base-change clause.

Step 9 uses only finiteness/algebraicity from the degree bound. A transcendence basis is preserved in an algebraic extension, and the finite value quotient disappears after rationalization. The statements are valid for infinite transcendence degree or rational rank too. In the divisible-group clause, divisibility alone is not being asserted to rule out all finite-index extensions in arbitrary groups: the conclusion uses the injective n-th-power map in positive real numbers. I checked the trivial extension, e=f=1, p=0, a positive-characteristic purely inseparable degree-p extension, an unramified extension whose degree is divisible by p, and the empty radical list. These tests preserve all hypotheses and conclusions. No step exceeds 2000 characters, and no new node is an elementary consequence or simply a clause of the item.

Each used node was opened and its actual statement copied to citations.json. Statement dependencies of both new nodes are definitions they actually use, with the absolute-value, finite-extension, normality, separability, fixed-field and purely inseparable meanings written inline where needed. I checked there is no reference back to the parent in either child's statement dependencies. No Lean was written, no compiler or Lake command was run, and no repository or launcher file was edited.

## Unfinished work

Only the two explicitly statement-only structural children remain unsplit, as required for a one-level split. No proof step of the item is left pending. The maintainer performs the independent mathematical review.
