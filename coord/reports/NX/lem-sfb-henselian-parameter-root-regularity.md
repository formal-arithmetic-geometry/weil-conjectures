# Worker report: lem-sfb-henselian-parameter-root-regularity

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-henselian-parameter-root-regularity.json`: split statement, nine proof steps; no complete Mathlib match. All mathematical clauses and hypotheses of the original statement are retained.
- `citations.json`: twelve verbatim statement excerpts covering every node citation in every proof step.
- `searches.jsonl`: actual search-command results, including two semantic phrasings and a second grep phrasing. Original imported searches remain in the item, and current NX searches are appended, with their actual results.
- `report.md`: this report. `prepare.py` is a sandbox-only preparation script.

No new nodes and no new Mathlib leaves.

## Attachments

None. Searched `lean/WeilConjectures` for the exact blueprint tag and parameter-root/henselian-regular notions; no matching declaration was found. The related local files in `lean/Sheaf` supply presentations or still-sorried larger claims, not a finished project attachment.

## WANTED

None. The ILO PDF and relevant Stacks algebra source are present and were read locally.

## Corrections and findings

The item had a statement only. I supplied the actual argument rather than making separate nodes for its finite-free, local, regular and henselian clauses. No mathematical statement was changed and no hypothesis was added. In particular, arbitrary positive n remains allowed. ILO IX Proposition 2.1(i), printed p.133 (PDF p.139), supplies the simultaneous parameter-root presentation in the prime-to-characteristic Kummer discussion; it does not itself state all the general arbitrary-n algebra conclusions of this item. Accordingly the expanded proof is marked agent-written and supported by individual existing Stacks nodes. No SGA argument is used.

The ancestor command returns `None`: this created algebra input has no imported blueprint ancestor. Its existing precise `blueprint.from.place` and via chain are retained. Searches of all imported blueprint statements for `parameter root`, `monic quotient`, and `regular local ring` found no second imported formulation of the full item. The regular-local-domain match is reused as `lem-sc-regular-local-domain`.

Generic off-unit tools are declared in `split_report.tool_uses`: integral injective dimension preservation, regular local implies domain, finite local henselian ascent, and the existing parameter/henselian definitions. These do not replace any unit-level step. The item serves the existing coefficient-specific tame-boundary algebra subargument beneath direct-image stability.

## Not duplicates

No new nodes were created. All substantial ingredients were found in the existing DAG and reused: monic quotient basis, finite implies integral, finite algebra Noetherian, maximal-ideal contraction for finite algebras over a local base, integral injective dimension preservation, regular local implies domain, and finite local henselian ascent. In particular no second node with Tags 04GG, 00GK, 00FN, 00OK, 00NP or 04GH is introduced.

## Review by NX

I read the item and its parent-route description, its chapter and unit records, GOAL.md, the three levels in SETUP.md, and both copies of delivery-errors B through E. For the mathematical source I read ILO IX Proposition 2.1(i), printed p.133, with the adjoining proof, and the local Stacks statements/proofs for 04GG (`lemma-characterize-henselian`), 00GK (`lemma-finite-is-integral`), 00FN (`lemma-Noetherian-permanence`), 00OK (`lemma-integral-sub-dim-equal`), 00KU (`definition-regular-local`), 00NP (`lemma-regular-domain`), and 04GH (`lemma-finite-over-henselian`). The proof adds the arbitrary-n algebra calculation explicitly; it uses neither Kummer torsor classification nor any source's SGA citation. There are no new-node source statements to review.

I opened and read the full statement of every cited node before writing the steps. Step 1 uses the exact polynomial universal property stated by `def-weil-pbc-mv-polynomial-ring`; the two presentations have inverse evaluation maps fixing coefficients and every variable. This is an elementary presentation calculation, not an invoked unnamed comparison theorem. Step 2 uses `lem-weil-pbc-monic-quotient-free`, which actually provides the specified power basis over any commutative coefficient ring. Its hypothesis holds for every intermediate ring because n is positive and X^n-t is monic of degree n. The induction starts with A_0=R, and uniqueness is proved at both coefficient levels; this avoids an unsupported claim about composing free bases. The zero exponent vector exists even when r=0, proving injectivity directly.

Step 3 uses exactly the finite-module hypotheses of `lem-weil-pbc-finite-algebra-is-integral` and `lem-weil-pbc-finite-algebra-noetherian`, with finiteness proved in step 2 and Noetherianity assumed on R. Step 4 again uses only the polynomial universal property; both closed-fibre maps are written out, their relations checked, and their composites fix all generators. Thus it does not assume a generic tensor/base-change theorem or mistake the closed fibre for the residue field. Killing the variables as well gives the coefficient-induced isomorphism with k=R/m and proves the displayed ideal is maximal.

Step 5 uses `lem-weil-pbc-finite-algebra-local-radical`, whose statement explicitly says every maximal ideal contains mB. In each field quotient x_i^n=0 forces x_i=0, so every maximal ideal contains the already maximal displayed ideal. This proves locality before any henselian ascent is invoked. Step 6 uses `lem-weil-pbc-integral-injective-dimension-equal`, which explicitly assumes precisely the injectivity and integrality established in steps 2 and 3 and concludes equality of Krull dimensions. No regularity or flatness assumption is being smuggled into that use.

Step 7 uses the definitions in `def-weil-pbc-regular-system-of-parameters` and `def-weil-regular-scheme`. I checked that these really use generation of the maximal ideal by exactly dim(B) elements, not an unstated regular-sequence or cotangent-basis criterion. Substituting t_i=x_i^n establishes the two inclusions of ideals in writing. Step 8 then applies `lem-sc-regular-local-domain` only after every hypothesis (Noetherian local, d-dimensional, d generators) is proved. Step 9 uses `lem-weil-pbc-finite-local-henselian`, which states henselianity for a local algebra finite over a henselian local base. Its locality hypothesis comes from step 5, not from the desired conclusion. The definition `def-weil-pbc-henselian-terminology` explicitly includes separable closedness of the residue field; the isomorphism from step 4 gives this final strict clause, with coefficient transport of polynomial roots explained.

The actual current Mathlib searches returned henselian criteria, the one-variable monic basis theorem, and regular-sequence dimension formulas; none states the whole item. I read the candidate monic basis/free/finite declarations in Mathlib/RingTheory/AdjoinRoot.lean and the regular-sequence dimension and scale-root hits. The former is already represented by the cited existing leaf; the latter require a regular sequence or concern polynomial root multiplicities, and do not provide the combined claim. The second semantic phrasing was tried before recording absence of a complete match. Search entries are copied from searches.jsonl and do not invent any call.

For small cases I checked r=0 (the ring and maps are R and identities, the basis is 1), n=1 (evaluation gives R), d=0 (necessarily r=0 and R is a field), r=d (the new maximal ideal is generated only by root coordinates), and n divisible by the residue characteristic (the closed fibre may be nonreduced but is still local; nilpotent images vanish in its field quotients). The zero ring is excluded by the initial local-ring hypothesis. No step uses n invertible, separability of X^n-t, excellence, completeness, or a chosen root of unity.

Every citation in citations.json was checked as an exact substring of the cited node's statement (C4), and every substantial imported theorem used in a step is in its uses list (C1). Definitions and explicit evaluation/ideal calculations suffice for the elementary steps. All nine steps are shorter than 2000 characters. New nodes have not been used to restate clauses, and no circular induction is present. There are no statement disputes and no unfinished mathematical part.

## Validation

The required server dry run exited 0 and printed OK (not pushed) at a268a4bd4db: preflight passed. The delivery tool ran the server validation, including check_dag and review_split. This final report update is validated again before pushing. No Lean source was written and no compiler or build command was run.

## Unfinished

None mathematically. Server validation passed; direct delivery follows the final report validation.
