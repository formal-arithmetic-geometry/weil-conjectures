# Q74 stage-1 delivery

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-laurent-stratum-formal-monoid-completion.json`: item, split into eight steps, no exact Mathlib match.
- `citations.json`: 20 step/node entries, quoting the full statement of every cited node verbatim.
- `report.md`: report and signed mathematical review.

No new nodes; no new Mathlib leaves. The statement is unchanged.

## Attachments

None. Searches of `lean/WeilConjectures/` by the exact blueprint id and by formal-monoid/completion and Laurent-stratum concepts found no project declaration stating the item. LaurentPoints and LaurentSeries declarations concern different objects, not this coefficient-prime completion.

## WANTED

None for this split. I read ILO VI 1.6, printed p. 70 (PDF page 76), locally. It motivates the formal monoid models but does not assert the Laurent-coefficient comparison. The proof is accordingly agent-written, using existing DAG results and the Stacks passages below; it does not invoke the unread Kato reference in ILO.

## Findings and repairs

The item arrived statement-only. Its hypotheses and all conclusions are retained. The substantive comparison is established on every finite quotient before passing to inverse limits. In particular, the inverse of a denominator is written as a finite geometric series, and coefficient reduction uses the mixed-ideal filtration, not a mistaken identification of the whole quotient with a uniform coefficient quotient.

The blueprint search commands `ancestor lem-trf-laurent-stratum-formal-monoid-completion`, `search monoid`, `search monoid algebra`, `search regular local`, and `search completion` found the existing ancestor and no blueprint theorem stating this item. I also searched the whole DAG by title and statement for Laurent, monoid, regularity/localization, coefficient filtrations, augmentation kernels and completions. Existing trace-unit nodes already give the orthant embedding, mixed filtration, inverse-limit comparison and augmentation quotient. Existing generic algebra nodes supply polynomial/localization regularity and completion properties. Thus no new node is justified.

The inherited ancestor chain names the historical nearby-duality/log-regular-chart branch below `lem-trf-local-term-locality`. I read the current latest locality statement and proof: they now use Varshavsky's contracting-correspondence theorem. This auxiliary algebra split does not claim to replace that route. The maintained `blueprint.from` and `via` records are preserved; `split_report.blueprint` identifies precisely the auxiliary calculation this item realizes. No chapter or unit records are changed.

The item is not an exact Mathlib leaf. Actual fresh msearch calls (LeanFinder twice, LeanSearch, Loogle and grep twice) are recorded in `searches.jsonl` and appended verbatim by tool/query to the item's existing search records. All services answered. I read the returned LaurentSeries equivalence context and AdicCompletion evaluation/local-ring sources. They supply generic components or special one-variable valuation completions, not the arbitrary sharp monoid and coefficient-prime statement. Older item search records are preserved.

## Not duplicates

No new nodes. `lem-trf-polynomial-power-series-monoid-completion` is related but compares polynomial coefficients with a fixed power-series coefficient ring at the origin; it does not handle an arbitrary prime in a Laurent coefficient algebra. It is not used as a substitute. `lem-trf-polynomial-monoid-lift-stratum` concerns a different base-changed algebra and its residue prime; it is not used to assert the local completion comparison. The generic filtration and augmentation nodes are cited directly rather than duplicated.

## Review by Q74

I checked delivery-errors B--E against the actual statements, not the proofs of the cited nodes. There are no new statement-only nodes to audit, no node that merely restates a clause of the item, and no claimed attachment. The item statement introduces every ring and ideal and already cites the definitions of its Cohen coefficient, sharp fs monoid, localization, completion, regularity and Noetherianity. I kept those statement dependencies unchanged. JSON is written with ordinary TeX escaping and a final newline.

Step 1 uses the zero-variable clause of `lem-weil-pbc-power-series-field-cohen-regular-complete` to obtain regular locality of L in BOTH cases. `lem-weil-pbc-regular-local-localization` expressly states that a regular local ring is regular as a ring. `lem-trf-polynomial-ring-regular-base` then applies to this regular coefficient ring, and `lem-weil-pbc-localization-of-regular-ring` expressly allows any multiplicative localization, hence inversion of the product of the Laurent variables. I wrote both maps of the Laurent presentation using a basis of K. `def-weil-regular-scheme` defines a regular ring as Noetherian with regular prime localizations, exactly what gives E_* regular local. I read Stacks algebra.tex 032C (remark-Noetherian-complete-local-ring-universally-catenary) and 0AFS (lemma-localization-of-regular-local-is-regular), and the recorded polynomial leaf. Zero variables really gives L, so no extra field perfection or coefficient residue hypothesis is used.

Step 2 applies `lem-weil-pbc-completion-regular-local` to the Noetherian local ring A proved in Step 1, and `lem-weil-pbc-adic-completion-noetherian` to its maximal ideal. The statement of `lem-weil-pbc-local-completion-local-ring` gives both the extended maximal ideal and the residue-field identification; `lem-weil-pbc-adic-completion-mod-ideal` gives completeness for that extended ideal. Finite generation follows from A being Noetherian. The residue field is computed directly with the fractions in `def-weil-pbc-localization-at-prime`; this calculation does not identify E/p with its fraction field unless it is already a field. Nonzeroness of D follows from its field quotient. I read more-algebra.tex 07NY (lemma-completion-regular), algebra.tex 05GG (lemma-hathat-finitely-generated), and the completion-local-ring node, whose stated kernel/unit criterion is the part used.

Step 3 uses exactly the injection and nonnegative coordinates provided by `lem-trf-sharp-fs-orthant-embedding`. Taking the coordinate sum gives positivity without requiring T itself to be free or replacing T by its group completion. Its image is finitely generated because T is. The finite monomial-generator presentation is explicitly described, so the finite-type hypothesis of `lem-weil-pbc-finite-type-algebra-noetherian` is met over E, A, and D. `lem-weil-pbc-localization-noetherian` applies to U localized at its prime r, whose primality is checked in Step 4. I read the finite-type and localization nodes and Stacks 00FN (lemma-Noetherian-permanence). Their conclusions are Noetherianity, not regularity of a possibly singular monoid algebra; I never assert the latter.

Steps 4--5 are elementary algebra with the explicit fraction equality in `def-weil-pbc-localization-at-prime`. Sharpness gives the augmentation ring map, its kernel modulo p gives primality, and each denominator has invertible constant coefficient in A. The inverse is a finite sum modulo the jth ideal power. The cross-product equality proves well-definedness, the generators prove the map kills the correct power, and fixing generators AND inverses proves both inverse identities. Reduction compatibility follows from uniqueness of the inverse of each denominator. Thus no unquoted localization/quotient comparison theorem is smuggled into these steps.

Step 6 reads the full statement of `lem-trf-positive-monoid-adic-filtration`: its coefficient membership is precisely m^(max(j-nu(v),0)), and it states that S_j is finite. The two applications have the same monoid, ambient group and weight. For v in S_j the exponent j-nu(v) is positive, so `lem-weil-pbc-adic-completion-mod-power` applies, with the finitely generated ideal m in A. The extended power is m_D to that power because Step 2 gives m_D=mD. The canonical ring map is coefficientwise the isomorphism on each finite summand, hence bijective; there is no assumption that the additive direct-sum formula preserves multiplication without checking the ring map. This is a routine application of the stated filtration formula, not a new hidden lemma. I read its existing statement and the full Stacks 05GG statement and proof.

Step 7 uses exactly the compatible ring isomorphisms required by `lem-trf-adic-inverse-limit-iso`, which I opened and read. That statement itself gives a ring isomorphism and the projection equations, not a topological claim. The topological claim is proved here: the equations carry each projection kernel onto its counterpart, and `lem-weil-pbc-adic-completion-mod-power` identifies these kernels with ideal powers because Step 3 gives finite generation on both sides. This proves continuity of both directions explicitly. Coefficients and monomials are preserved at every finite level and therefore in their tuples.

Step 8 uses the exact kernel assertion in `lem-trf-formal-monoid-residue-domain`, not merely its domain conclusion. Its hypotheses are a nonzero complete separated Noetherian local coefficient ring and a finitely generated positive submonoid of a finite rank free abelian group. Steps 2--3 establish all of them. Its augmentation and coefficient maps are precisely the maps requested by the item, so this gives the actual monomial ideal kernel, rather than merely a closure of that ideal. I read the existing statement and the ILO formal-model passage; the agent provenance is explicit.

I tested T={0}, K=0 and n=0, including all three together. For a field with these three zero cases, A=D=Z=H=L and the defining ideal is zero. For a Cohen ring with all three zero cases, A=D=Z=L and the construction is its already complete maximal-adic tower. For T=N, the quotient formula in Step 6 reduces to the usual sum over 0 <= v < j with coefficient modulus m^(j-v). For the nonfree saturated monoid {(a,b) in N^2 : a+b is even} in its own group completion, the orthant-weight argument still applies, so no hidden smoothness/freeness assumption was introduced. With K=Z and p a nonmaximal allowable coefficient prime, the residue calculation retains Frac(E/p), never silently E/p.

All eight steps are below 2000 characters (largest 1025 at writing). The non-elementary ingredients are cited nodes; the remaining maps and identities are written out. The proof-dependency list is exactly the union of step uses. Generic off-unit non-leaf tools are declared in `split_report.tool_uses`; this is a declaration for the maintainer's route review, not an edit to maintained `tool_uses`. The sources and hypotheses have been checked point by point; no statement dispute was found and no statement change was made.

## Unfinished work

None in the authorized stage-1 scope. This is a natural-language split, not a Lean proof. No Lean file or compiler/build was used. Required server checks and delivery results are recorded by deliver.py.
