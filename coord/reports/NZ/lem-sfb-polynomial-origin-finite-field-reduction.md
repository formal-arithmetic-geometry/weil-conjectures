## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-origin-finite-field-reduction.json`: item, statement unchanged, seven complete proof steps. Mathlib verdict: no declaration states the whole construction; all required general results are existing Mathlib leaves.
- `citations.json`: thirteen step/node entries, each quoting the cited statement verbatim.
- `searches.jsonl`: the six searches performed through the prescribed command, including both semantic phrasings and their actual results.

No new nodes; no new Mathlib leaves. The earlier searches embedded in the imported item are retained unchanged and supplemented with the searches actually run for NZ. `prepare.py` is sandbox preparation only, not a delivery file.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for polynomial-origin, transcendence-basis, finite-extension and domination terminology. `MvPolynomial.polynomial_origin_regularLocal` concerns a polynomial ring over a field and neither gives this local-domain construction nor its field-extension clause. No project declaration found states every clause of the item.

## Wanted

None. The required Stacks text and installed Mathlib sources are available locally.

## Findings and corrections

The item was unsplit, with no prior sandbox split or report. Its statement is correct and was retained verbatim. The first paragraph of Stacks Tag 00PH (`algebra-lemma-exists-dvr`, algebra.tex:29312 onward) abbreviates this construction as a replacement of R. I wrote out its kernel, embedding, fraction-field, contraction and nonfield arguments. The finite basis, algebraic-generator finiteness, finite-type Noetherianity and localization Noetherianity already have nodes, so they are reused rather than recreated. In particular, `lem-trf-mvpolynomial-noetherian` only asserts the case over Z; it cannot supply Noetherianity over arbitrary R. The existing, more general `lem-weil-pbc-finite-type-algebra-noetherian` supplies exactly that input.

The ancestry command prints a null nearest ancestor. The inherited item has a complete, non-unspecified place and via chain; I retained it, rather than inventing an imported ancestor. I read the newest blueprint through `literature/blueprint/latest/`, specifically the chapter, the stability unit, and `sk-thm-sf-ctf-stability-direct-images.proof.md` (3). The current blueprint assembles proper and open direct image; our item is the inherited algebraic prerequisite deeper in that route, not a replacement of the unit. The recorded unit file has older chapter metadata; this delivery does not change that unit or any parent. Whole-blueprint searches for `transcendence basis`, `localization noetherian` and `polynomial origin` found no exact imported statement. The existing generated field and ring nodes were found by searching the whole DAG.

## Unfinished work

None in the one-level split. There are no new unsplit nodes. The server `review_split` check passed before this report was written; the required full dry run and push follow.

## Review by NZ

I read Stacks algebra.tex Tag 00PH, first proof paragraph, as the source for the item, and checked the supporting source statements in Fields Tag 030F (`lemma-transcendence-degree`, including the generating-set argument), Fields Tag 09GH (`lemma-algebraic-finitely-generated`), Algebra Tag 00FN (`lemma-Noetherian-permanence`), and the paragraph after the local-ring definition giving locality of a prime localization. For the final zero-variable identification I read Tag 00E9 (`lemma-characterize-local-ring`) and used the existing local-ring unit-criterion leaf. No new node needs an additional source. I also read the Mathlib source signatures returned by search: FinTrdeg.lean:35–36,86–91, IntermediateField/Adjoin/Basic.lean:586–594, FiniteType.lean:187–193, Localization/Submodule.lean:82–88 and AtPrime/Basic.lean:155–173. These are separate ingredients, not an exact match to the item.

Step 1 uses the finite-transcendence-basis statement for L/K. Its statement really gives a finite algebraically independent family and algebraicity over K(x); the definition node explicitly spells out both conditions. The algebraic-generators node is applied over the field K0 to the original finite generators a_i. I checked K0(a_i)=L by both containments, so no unmentioned finite-type assertion is used. Step 2 uses the polynomial definition for evaluation and its image, the transcendence-basis definition for injectivity over K, and the finite-type Noetherian leaf with zero ideal for the polynomial presentation over R. The restriction from K-coefficients to R-coefficients is injective because R is a subring of K; no flatness claim is needed.

Step 3 uses the quotient-field node with the actual maximal ideal m_R, and the polynomial definition for evaluation and the finite monomial expansion. Its kernel calculation is written explicitly. Maximality is proved directly by lifting an inverse from the residue field, rather than silently citing an ideal correspondence; primality follows by multiplying residues in a field. Step 4 cites only the definition of K(x) as the smallest containing subfield; the displayed set of ratios is checked to be a field by the common-denominator and inverse formulas, contains K because K=Frac(R), and contains the x_i. This is a few-line argument, not a new rational-function theorem.

Step 5 uses the localization-at-prime node only for its actual fraction description, locality and maximal-ideal formula, all explicitly in that node's statement. The prime hypothesis was proved in step 3. The equality of cross products establishes the embedding in K0 and therefore the domain property; the existing localization-Noetherian leaf applies since step 2 gave Noetherianity. The fraction-field assertion follows from step 4 and P contained in B. Step 6 cites no outside theorem: extension of the residue evaluation by p/s -> epsilon(p)/epsilon(s), with nonzero denominator, directly proves the contraction, and the chosen nonzero t in m_R remains nonzero under the established embedding. This is where the nonfield hypothesis is essential.

Step 7 checks the algebraic case independently by choosing the empty basis, not by assuming the arbitrary basis chosen earlier was empty. I corrected my initial draft to cite the existing local-ring unit criterion explicitly for the assertion that denominators outside m_R are units; that assertion was not left hidden behind maximal-ideal existence. Its hypothesis is exactly the unique-maximal-ideal hypothesis on R. All citations have been reopened and their full statements copied verbatim to citations.json; no proof or definition is cited for a stronger unstated conclusion.

For delivery-errors B, every object remains introduced in the unchanged statement, no new statement-only nodes or duplicated notions were introduced, and TeX and blueprint ancestry are preserved. For C, each non-elementary input has an existing cited node saying it; definition-only and elementary steps contain their actual calculations, and there are no new dependency cycles or off-route unsplit tools. For D, the steps carry the polynomial-origin construction rather than moving its clauses into replacement nodes. For E, I checked r=0, L=K, n=0, nontrivial algebraic extensions, and a transcendental example R=Z_(p), L=Q(t): B=Z_(p)[t]_(p,t), whose fraction field is Q(t), whose maximal ideal contracts to (p), and which is not a field. Purely inseparable algebraic extensions in positive characteristic cause no problem because the algebraic-generators lemma assumes no separability. The excluded field case R=K would fail the nonfield conclusion at r=0, exactly as the hypothesis m_R != 0 prevents. No step exceeds 2000 characters and none hides a separate non-elementary lemma.

## Not duplicates

No new nodes, hence no new/existing pairs sharing a Stacks tag. All available general-purpose leaves were reused.
