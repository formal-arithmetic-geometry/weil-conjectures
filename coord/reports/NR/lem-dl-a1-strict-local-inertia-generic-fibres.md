# Worker report — NR

Item: lem-dl-a1-strict-local-inertia-generic-fibres. Stage 1 only, 2026-10-23.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-strict-local-inertia-generic-fibres.json: statement unchanged, ten proof steps, 22 existing proof dependencies; not a Mathlib leaf.
- citations.json: a verbatim statement quotation for each of the 25 step/node citations (including repeated citations where used again).
- report.md: this report. searches.jsonl is the search command's own log.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter record changed.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint id and for inertia, and read the relevant normal-local ring and fundamental-group files. InertiaStrictHenselization.lean proves strict henselianity of inertia invariants and closedness of inertia; StrictlyHenselianNormal.lean proves strict henselianity of the localized normalization; DecompositionGroup.lean gives trivial action of normalization inertia on finite etale covers. These are ingredients only. None is an attachment proving all clauses of this item, notably arbitrary normal-local strict henselization embeddings, their conjugacy, and the affine-prime comparison. No Lean was written or compiled.

## WANTED

None. All sources used are present under literature/.

## Findings and changes

The item had no proof. Its statement is correct and is retained word for word. I read pione.tex Tag 0BTD, lemma-normal-pione-quotient-inertia, its setup and first proof paragraph; Tag 0BSD, section-ramification; Tag 0BSW, lemma-identify-inertia; and the trivial-composition paragraph of Tag 0BSM, lemma-local-exact-sequence-normal. The reviewed existing lem-dl-a1-henselian-global-inertia-comparison states the needed normal-local comparison for arbitrary normal local domains, without a DVR or Noetherian restriction. Reusing it removes the need to create a new normalization/strict-henselization comparison lemma.

I also read the chapter and unit records and rem-dl-a1-conventions in the current main-20261015 blueprint. The unit has no proof steps to realize, and this item is not its key statement. The argument supplies the local algebra underlying the unit's inertia-at-infinity convention, without changing its route or coefficient category.

The extra written arguments are: extension of arbitrary field embeddings; the stabilizer conjugacy calculation; splitting a finite etale algebra using full faithfulness of henselian reduction; the action on actual geometric generic points; normality of every affine coordinate domain; and localization of normalization inertia at a possibly nonclosed point. No assertion about algebraic closedness of the normalization residue field is used: for imperfect fields such an assertion would be false. The existing local comparison is stated without that assertion.

## Mathlib and duplicate searches

Ran the required search command with LeanFinder, Loogle, grep and LeanSearch, then a second LeanFinder phrasing about splitting finite etale schemes over strictly henselian local rings. The five actual queries and returned names are recorded in searches.jsonl and appended verbatim as queries to the item's mathlib_searches; the five inherited 2026-10-22 searches are preserved. Read Mathlib FieldTheory/Galois/Basic.lean:444-451, RingTheory/Etale/Field.lean:271-286, FieldTheory/Extension.lean:339-348 and RingTheory/Algebraic/Basic.lean:491-498. The field product classification and embedding-extension facts are ingredients already represented by DAG nodes. They do not give the complete item over arbitrary normal local rings. All services answered; no unavailable search was represented as an absence result.

Searched the whole DAG by tags 0BTD, 0BSW, 0BSM, 06DI, 04GU, 0BSQ and 0BSU and by the local-ring, finite-etale splitting and integral-closure notions. Ran tools/blueprint_refs.py ancestor for the item and search for inertia, strict henselization, henselian and normal integral. No blueprint node states the whole item. The relevant existing normal-local comparison is reused. The DVR-only lem-wf-strict-henselian-fraction-inertia is not used as a substitute for a general normal-local statement.

## Not duplicates

No new nodes. In particular, no new copy of lem-dl-a1-henselian-global-inertia-comparison, lem-weil-pbc-integral-closure-commutes-localization or the henselian finite-etale equivalence is introduced.

## Review by NR

I read the sources with the item and the cited statements open. There are no new-node sources to check. Each citation in citations.json is copied from the cited statement itself, including its hypotheses; I did not quote proofs or Lean docstrings as if they were statements.

1. The two existing integral-scheme field lemmas give the same generic stalk K as the fraction field of both a stalk and a nonempty affine coordinate ring. The affine-open-stalk-localization statement explicitly gives A_p isomorphic to the stalk through the germ map. Normality of those stalks therefore says that A is a normal ring in def-weil-pbc-normal-ring. The normal-ring-integrally-closed-total statement then gives integrally closedness in K because for a domain its total fraction ring is its fraction field. I checked these against schemes.tex 01HV, morphisms.tex 01RV and algebra.tex 034M. This avoids assuming that normal local stalks imply affine normality without a supporting result.

2. The lying-over statement requires an injective integral map; A_x into its integral closure satisfies both. The prime-over-maximal statement makes the chosen prime maximal because its contraction is the maximal ideal of the local ring A_x. I read algebra.tex 00GS and the local setup of pione.tex 0BSD. The existing general local comparison gives both the domain assertion and a compatible embedding into the localized normalization, so it gives the fraction embedding by the explicit fraction formula. Its hypotheses require neither a DVR nor Noetherianity.

3. The separable-closure-exists-galois statement gives algebraicity and splitting of every minimal polynomial, as required by embedding-extension-sepclosed. The intermediate field is i(L), and its prescribed map sends i(a) to j(a); this is a map on the entire possibly infinite intermediate field. The algebraic-endomorphism-bijective statement makes the extended map an automorphism. I checked the exact quantifiers in the Mathlib declarations at Extension.lean:344 and Algebraic/Basic.lean:491. No finite-extension assumption is slipped into this step.

4. The equality of subgroups is proved by writing g^{-1}hg on each i(a). This is elementary and cites no theorem. The direction of conjugation is J_j = g J_i g^{-1} when j = g i.

5. Finite-morphism-permanence explicitly supplies finiteness after arbitrary base change and affineness over an affine base; the finite-morphism definition identifies the coordinate algebra as module finite. Etale-base-change-finite-limits clause (1) explicitly supplies etaleness after arbitrary base change. Strict-henselization-local-structure supplies local and strictly henselian, and the terminology definition supplies henselian plus separably closed residue field. This uses none of the residue-field identification absent from the local-structure statement. I read the finite and etale base-change source places, including morphisms.tex 02GO.

6. I read algebra.tex 04GK, lemma-henselian-cat-finite-etale, and its proof. The cited equivalence is on finite etale algebras with all algebra homomorphisms, so it supplies the full faithfulness needed to lift the residue isomorphism and its inverse. The field-product statement gives all finite separable field factors, and sepclosed-finite-sep-trivial kills each such extension. The composites are identities by faithfulness. The finite product R^n is a finite etale R-algebra (finite free as module and locally the identity on its n open-and-closed summands). Thus this is an actual algebra isomorphism, not just a count of closed-fibre points. The n=0 case is included.

7. The coproduct-base-change statement identifies the strict local generic fibre as n copies of Spec L, including the projections. The affine-spectrum definition identifies the morphisms on each one-point summand. The fibre-product lifting condition is imposed over the chosen i:L into Omega. Each geometric point is the scalar extension of an L-section, so composing with an automorphism fixing i(L) leaves that point unchanged. This is the explicit content of the trivial-composition paragraph of pione.tex 0BSM; it does not infer trivial monodromy just from a disconnected geometric base change.

8. I read algebra.tex 0307, lemma-integral-closure-localize, and the cited statement: it applies to an arbitrary ring map and multiplicative subset, so inverting M=A minus p in Omega gives exactly the integral closure over A_p. The resulting prime is over the maximal ideal of A_p and is maximal by the cited prime-over-maximal statement. Its quotient is a field inside Frac(C/r) containing C/r, so it equals that fraction field. This verifies the residue field in the item's inertia definition, even when x is not closed in V.

9. Both the original and localized integral closures are stable under each K-automorphism because the monic relations have fixed coefficients. Each automorphism fixes every denominator in M. The prime stabilizers agree by extension/contraction, and the residue actions agree by the displayed fraction formula. This comparison is elementary localization, written explicitly rather than concealed in a word such as "transports".

10. The general local comparison explicitly identifies I with Aut_{K^sh}(Omega) for its compatible embedding. It applies to the particular maximal prime constructed from r in Step 8, not only to the prime chosen in Step 2. Steps 3-4 then prove conjugacy for every other compatible embedding. This is the first proof paragraph of 0BTD using 0BSW. I checked that the local comparison's dependency list does not cite this item, avoiding a circular appeal.

Edge cases: X=Spec k, including imperfect k of characteristic p; x generic in a positive-dimensional normal integral X; a strictly henselian normal local base; the empty finite etale cover and the identity cover; nonclosed x in an affine normal scheme; and a non-Noetherian normal local domain. For a field, L is its separable closure and J is trivial; its normalization in Omega is Omega and the defined inertia is trivial. For nonclosed x, Step 8 uses Frac(C/r), not the generally nonfield quotient C/r. No finiteness of normalization, of the strict-henselization fraction extension, or of the residue extension is used.

B–E checklist: all objects already occur in the unchanged self-contained statement; no new unsplit statements, new definitions or duplicate nodes; TeX has single mathematical backslashes after JSON decoding; sources use tags and labels; searches are actual logged queries; blueprint provenance is preserved and same_as is searched. Every non-elementary ingredient is a cited statement with its hypotheses checked above, and citations.json contains exact quotations (C1/C4). The proof has real algebraic and conjugacy arguments rather than transferring the whole item to a new node (D1/D2), and no source's omitted details are appealed to without a statement. All ten steps are under 1100 characters, so there are no long steps hiding a separate lemma. No statement repair, extra hypothesis, route change or SGA citation was needed. Off-unit generic tools are declared in split_report.tool_uses; they are algebra/scheme tools, not a different unit's geometric route.

## Unfinished work

None for this one-level split. The existing cited nodes retain their independent proof and formalization states.
