# Stage 1 delivery: lem-sfb-simple-bruhat-double-coset-product

1. Files written: dag/nodes/sec-six-functors-basics/lem-sfb-simple-bruhat-double-coset-product.json (statement, split; no Mathlib match), citations.json, report.md. New nodes: 0. Mathlib leaves: 0. The sandbox helper write_split.py records the construction; it is not a delivery file.
2. Attachments: none. Searches by the blueprint tag and Bruhat/bruhat/BNPair/TitsSystem in lean/WeilConjectures returned no declarations.
3. WANTED: none for this split. All arguments follow the locally available Milne iAG2017 PDF. The prior node requested Brion--Kumar; this proof does not need that unavailable book.
4. The imported item has no proof and no Lean audit. Its statement is correct and is preserved verbatim. Its source field previously named an unavailable Brion--Kumar PDF but already mentioned Milne 21.75. The proof and source now use Milne directly. The last display of Milne's negative-root T3 proof drops a terminal w; the explicit calculation below supplies it. No statement correction is needed.
5. Unfinished: none within this one-level stage-1 split. No Lean was written or compiled. No repository or launcher files were changed.

## Source error

Milne, Proposition 21.75, printed p.448, last line of the T3 proof, ends its displayed containment in B(k); the expression on the left still contains w. Its intended containment is in B(k)wB(k). For example in SL2 take w=s and use the Weyl-matrix representative n. The expression BnBn n is the double coset BnB, not a subset of B. Step 6 computes each nonzero lower-unipotent term using a 2 by 2 identity, and retains n_w throughout. This is a typographical error in the proof, not a false product statement. The zero term separately gives D_sw. No characteristic restriction is introduced.

## Searches and reuse

Read SETUP's three levels, GOAL, the item unit and chapter, and the current literature/blueprint/latest direct-image proof. This inherited chain supports the alteration argument of its step (3); the unit/chapter route is unchanged. blueprint_refs.py ancestor returns None, as it does for the inherited node: its existing place and via chain are preserved. Blueprint searches for Bruhat, root length, inversion and word length found no equivalent blueprint assertion (the inversion hits concern Fourier inversion).

Whole-DAG searches by Bruhat, simple reflection, length, inversion, root sign, rank one, and Milne 21.75 identified existing nodes. In particular the second broader word-length search found lem-sfb-root-sign-word-deletion, which avoids creating a new root-length node. Read its full statement. Also read the full statements of every node cited below. No new nodes, so no duplicate pairs require certification.

Ran msearch.py for the item, preserving its older searches. Read all hits from LeanFinder, Loogle, LeanSearch and grep. DoubleCoset.doubleCoset and doubleCoset_eq_image2 are definitions/set rewrites (Mathlib/GroupTheory/DoubleCoset.lean:37,40); they do not imply the Borel product theorem. RootPairing.RootPositiveForm.rootLength (RootPositive.lean:171) is a squared norm, not word length. RootPairing.Base.IsPos.reflectionPerm (Base.lean:578) is the simple-root sign fact, written explicitly in step 1. CoxeterSystem.length_simple_mul (GroupTheory/Coxeter/Length.lean:204) and the inversion/descent hits presuppose an abstract Coxeter system and do not identify signs for the algebraic-group normalizer quotient. We instead cite the already existing geometric-Weyl identification and root-sign deletion nodes. Every appended search record is copied from searches.jsonl with the actual query and hits; none was inferred or fabricated.

## Not duplicates

No new nodes. Reused the existing root-sign deletion statement instead of adding an inversion-count/length statement. No new node restates any clause of the item.

## Review by NJ

I read Milne iAG2017 Theorem 21.68 and Remark 21.69 (printed pp.445--446), the Bruhat section through 21.75 (pp.446--448), the root-system appendix C.8--C.22 (pp.609--612), and the existing root parametrization/reflection statements linked to Theorem 21.11 and paragraph 21.24. The only source needed is the obtained Milne PDF. I checked the item against its original statement and retained every hypothesis and clause, including algebraically closed extensions, both exact set equalities, the two length alternatives, reduced expressions and the identity case.

Step 1 uses the Borel-pair statement for reductivity, the sign expansions and independence of simple roots. Weyl-reflection-realization states precisely faithfulness on the rational root span and identification with the reflection group; simple-root-reflection-generation then applies after scalar extension and finite-group averaging. The averaging and simple-coefficient argument are explicit elementary linear algebra, not a claimed extra root-system theorem. No semisimple rank or characteristic-zero Lie-algebra identification is assumed.

Step 2 uses exactly root-sign-word-deletion's deletion conclusion. Step 1 verifies its sign-partition and positivity-permutation hypotheses. Applying it to a shortest word for w inverse gives the descending length inequality; the reverse word and one-letter bound give equality. Applying that same result to sw gives the increasing case. There is no circular use of the Bruhat product or any Coxeter presentation.

Step 3 uses the root-subgroup statement's uniqueness for conjugation, its all-algebra torus-action identity, and the opposite-root-SL2 statement's upper/lower subgroup isomorphisms and diagonal coroot restriction. I checked the torus conjugation calculation on the two unipotent matrix factors and identified the Weyl representative by the separately cited faithful action. This explicitly proves the normalizer property rather than assuming the image of the SL2 Weyl matrix normalizes all of T. Arbitrary K/F is allowed because these are scheme homomorphisms and formulas on all algebras.

Step 4 uses arbitrary-order positive-root product coordinates and B=U semidirect T, exactly as their statements give them. V denotes only an ordered product of other root groups; no unproved subgroup property is used. The argument proves both inclusions in the intermediate set equality. Its product is B-bi-invariant, which justifies saturating the representative to D_sw.

Step 5 uses the already verified root conjugation, the positive-root inclusions from the product-coordinate statement, and step 2's sign-length criterion. It gives equality, not just the Tits-system inclusion.

Step 6 uses the opposite-root-SL2 map for the displayed identity and the positive-root inclusions when -w inverse alpha is positive. I multiplied the matrices: the right hand side is [[1,0],[a,1]]. The restriction to a nonzero is stated, with a=0 handled separately. For a=1 the nonzero term lies in D_w; B-bi-invariance gives the entire coset, establishing the reverse inclusion missing from a bare T3 citation. The terminal n_w is retained, correcting the source typo. No field-closure choice or division by 2 is used.

Step 7 is elementary induction on the suffix length, including the argument that each suffix is reduced. It accounts separately for the empty word and D_1=B; it does not incorrectly call the singleton identity the identity among B-bi-invariant subsets.

I tested SL2 for w=1 and w=s, including characteristic 2: the formulas give D_s B=D_s and D_s D_s=B union D_s, and h(-1) remains valid in characteristic 2. For a reducible root system roots in different components are unchanged by the simple reflection, so the positivity argument still applies. For the trivial rank-zero group there are no simple roots and only the identity clause remains. All steps have fewer than 2000 characters. I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the actual files: no new statement nodes, no unquoted cited statement, no hidden geometric lemma, no off-unit tool and no cycle introduced. citations.json contains the full verbatim statement for every cited node at every step; the paragraphs above identify the exact portions used.
