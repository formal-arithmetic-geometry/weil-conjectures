## Files written

- `dag/nodes/sec-trace-formula/lem-trf-normalization-completed-product-comparison.json`: statement, now split into eight steps; no exact Mathlib match.
- `citations.json`: fourteen entries, one for every step/node citation, quoting the entire cited statement verbatim.
- This report. `searches.jsonl` retains the five new searches actually run with msearch.py; the item retains its inherited searches as well.

New nodes: 0. New Mathlib leaves: 0. The item statement, statement dependencies, source, historical blueprint ancestry, chapter, and unit are preserved.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item id and for normalization/completion, normalized branches, integral closure, and the relevant ring notions. The normalization/completion hits concern normalized adic coefficient systems, not integral closures of local domains; the ring-theoretic declarations inspected do not state this comparison. No sorry-free project declaration states all clauses. The upstream master checkout was not used as evidence of completion.

## WANTED

WANTED: Swanson–Huneke, *Integral Closure of Ideals, Rings, and Modules*, Proposition 4.7.3, printed pp. 81–82 (PDF pp. 95–96), for lem-trf-normalization-completed-product-comparison; local path `literature/swanson-huneke-integral-closure.pdf` is absent. I read the author-hosted [PDF](https://www.math.purdue.edu/~iswanso/book/SwansonHuneke.pdf) online, including the component construction and reverse inclusion. No document was downloaded. The delivered proof is explicitly agent-written, with its usable algebra inputs sourced to the local Stacks text.

## Audit findings and corrections

The item was unsplit with no proof, rather than a completed earlier attempt. Its statement is correct: neither excellence nor reducedness of the completion is needed. The important missing argument was passage back from the component equations through a possibly nonzero nilradical. I gave that passage explicitly instead of identifying the completion with its reduction.

The current main-20261015 blueprint ancestor `lem-trf-local-term-locality` concerns contracting correspondences. Its proof explains specialization to the normal cone; it does not contain an Orgogozo/Heinzer or normalization sentence. I read the chapter, unit, current ancestor statement/proof, and the parent normalization split, and kept the existing honest historical ancestry. This split supplies the comparison used by `lem-trf-normalization-integral-closure-krull` Step 4; it does not change a unit or chapter route.

No statement dispute or source error was found. No hypotheses or conclusions were changed. Generic completion structure and quotient results from another unit are declared as tool uses; the remaining imported statement inputs are Mathlib leaves. The proof does not use any SGA source.

## Searches and reuse

Whole-DAG searches by completion, faithful flatness, minimal primes, nilradical, radical intersections, and quotient completeness found all necessary inputs. Whole-blueprint searches with `tools/blueprint_refs.py search` for `completion`, `normalization completion`, `integral closure`, `nilradical`, and `quotient complete` found no node stating this comparison. `blueprint_refs.py ancestor` confirmed `lem-trf-local-term-locality`. The item's `same_as` remains empty.

Five Mathlib searches were run with the required command: two distinct LeanFinder phrasings, one LeanSearch phrasing, Loogle for `"integralClosure", "AdicCompletion"`, and grep for `integralClosure|IsIntegralClosure` in `RingTheory/AdicCompletion`. I read every returned hit. The semantic results concern almost-integrality, integral norms/localization, or Dedekind valuation completions; none states this local-completion branch comparison. In particular, `completeIntegralClosure_eq_integralClosure` uses the word complete for almost-integral elements, not adic completion. Loogle and the completion-directory grep returned no hits. All services returned successfully, and no unavailable service was recorded as absence. Inherited searches were retained unchanged.

## Not duplicates

No new nodes. In particular I reused the existing radical-intersection node rather than creating a nilradical/minimal-prime theorem; reused faithful-flat ideal contraction rather than creating an integrality-descent lemma; and kept coefficient lifting, homogenization, expansion, and division as explicit steps.

## Review by Q16

I read Swanson–Huneke Proposition 4.7.3 online and the local Stacks `algebra.tex` passages with labels `lemma-completion-Noetherian-Noetherian` (0316), `lemma-hathat-finitely-generated` (05GG), `lemma-quotient-complete-local` (0325), `lemma-Noetherian-irreducible-components` (00FR), `lemma-completion-faithfully-flat` (00MC), `lemma-flat-going-down` (00HS), `lemma-Zariski-topology` (00E0), and `lemma-faithfully-flat-universally-injective` (05CK). The book's first comparison specializes to the local-domain assertion, and the component construction uses the quotients before normalization, just as the item requires. The expanded argument is written independently with the local Stacks inputs. There are no new-node sources to certify.

For Step 1 I opened `lem-weil-pbc-adic-completion-noetherian`, `def-weil-pbc-noetherian-ring`, and `lem-weil-pbc-adic-completion-mod-ideal`. Their statements give exactly Noetherianity, finite generation of the ideal m, completeness for mH, and the residue-field quotient. The locality argument is explicitly coordinatewise: a nonzero first residue gives a unit at every level, and the unique inverses are compatible. Thus completeness is for the actual maximal ideal, as needed in the next step.

For Step 2 I opened `lem-weil-pbc-noetherian-finitely-many-minimal-primes`, `lem-weil-pbc-prime-contains-minimal-prime`, and `lem-weil-pbc-complete-local-quotient`. The first applies to the Noetherian H from Step 1. The second applies to its prime mH and proves nonemptiness, so an empty product cannot accidentally occur. The third applies because each q_i is a proper ideal of this complete Noetherian local ring. Domain and nonzero properties of H/q_i follow from primeness; no normality of these quotients is assumed.

For Step 3 I opened `lem-weil-pbc-local-completion-faithfully-flat` and `lem-sc-flat-going-down`. The first has precisely the given Noetherian local hypotheses and states flatness as well as faithful flatness. The second genuinely supplies a prime BELOW the selected q_i, over the prime zero of the domain R. Minimality forces that prime to be q_i, proving contraction zero for EACH branch. This is stronger than merely finding one dominant branch, and is exactly what the fraction formulas require. Injectivity and fraction-field extension are verified from cross multiplication, not taken from a definition node as an unstated theorem.

For Steps 4 and 5 I opened `def-weil-pbc-integral-closure`. It defines integrality by a monic equation of positive degree and identifies integral-closure membership with that condition. Step 4 maps such an equation along j_i. Step 5 chooses coefficients in the quotient B_i and lifts them through H to B_i, keeping leading coefficient one. Multiplication by the nonzero branch denominator clears the fraction equation; the field embedding of B_i detects that its numerator is zero. These are direct polynomial and quotient calculations, so they are marked elementary. There is no appeal to preservation/descent of normality or to a completed fraction field.

For Step 6 I reopened `lem-weil-pbc-prime-contains-minimal-prime` and `lem-weil-pbc-zero-locus-eq-iff-radical-eq`. The latter's statement includes the full formula sqrt(I) = intersection of primes containing I and the power definition of sqrt(I). Thus, for I = 0, the cited statements really imply u^e = 0 after checking every prime contains one q_i. I corrected the tempting but unjustified inference u = 0; taking a positive power handles a nonreduced H without adding a hypothesis.

For Step 7 I opened `lem-weil-pbc-faithfully-flat-ideal-contraction`, whose exact formula is preimage(JH) = J. I checked that J is an ideal of R, with generators a^r b^(M-r), and that the expanded homogeneous equation says precisely a^M lies in its extension. Faithful flatness is already established for R to H, not for the generally nonflat maps to individual B_i. Coefficients t_r in R then exist by the definition of the ideal generated by this finite list. The monic X^M coefficient stays one through every product and power.

For Step 8 I reopened the same integral-closure definition. Dividing by b^M is permitted in K since b is nonzero; it produces the required positive-degree monic equation. The final identification of the intersection uses the already established nonempty family of field embeddings. No surjectivity or product-finiteness of normalization is used.

I checked B1–B9: there are no new nodes, proof sketches disguised as statements, duplicate lemmas, or missing new-node searches. For C1–C4, every non-elementary input is the statement of a cited node; fourteen complete verbatim statements in citations.json witness this. The original statement's three definition dependencies all define the notions it uses. C5–C8 and D1–D5 were checked by reusing the existing tools and retaining the explicit polynomial argument in the item. I checked generic tool citations against their own hypotheses rather than importing any proof of a dependency. No step exceeds 2000 characters (the longest is 806), and none hides a standard comparison lemma.

Small cases checked: when R is a field, m = 0, H = R, s = 1, and the comparison reduces to integrality in the same fraction field. For a complete local domain again there is one branch. For x = 0 choose a = 0 and b = 1; the monic-equation calculation still works. If b is a unit, descent remains valid. For several branches, a common degree is NOT assumed: the sum of the individual degrees and their product are used. With a nonzero nilradical the positive exponent e is essential and is retained. Zero rings are excluded by the domain hypothesis; minimal primes are never an empty list here. No characteristic restriction enters the expansion.

## Unfinished work

None in this one-level split. The existing unsplit dependencies remain their own items; no Lean was written or compiled. Validation and delivery results will be recorded below.
