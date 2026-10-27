# Stage-1 report: lem-sfb-involution-deletion-presentation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-involution-deletion-presentation.json: existing statement, now split; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-involution-two-descent-prefix.json: new statement-only supporting lemma; unsplit, no Mathlib match.
- citations.json: verbatim statement excerpts for both occurrences of the supporting lemma.
- searches.jsonl: actual msearch results, retained unchanged.

## Attachments

None. Searches for the exact blueprint tag and Coxeter/dihedral terminology in lean/WeilConjectures found no declaration of the criterion. Also inspected the relevant Mathlib Coxeter sources and searched lean/Sheaf; nothing supplies this implication without already assuming a CoxeterSystem.

## Wanted literature

WANTED: Bourbaki, Lie Groups and Lie Algebras, Chapters 4–6, Chapter IV §1.5 Theorem 1 and its proof, for lem-sfb-involution-deletion-presentation and lem-sfb-involution-two-descent-prefix; the local PDF named by the original node is absent.

WANTED: Christopher H. Cashen, Notes on Coxeter groups, version 31 October 2023, Chapter 4 §§1.3–1.4 and §4 (especially Lemma 4.0.14(2), pp.120–121), https://www.mat.univie.ac.at/~cashen/Notes_on_Coxeter_groups.pdf, for the word-comparison and minimal-coset supporting arguments. Read online, not downloaded.

Read online Mühlherr–Weiss, Coxeter's enumeration of Coxeter groups, §6 Theorem 6.2(D), https://doi.org/10.1112/jlms.70379. It confirms the exact abstract criterion but refers elsewhere for its proof. No SGA source is used. No Stacks tag states this group-theoretic criterion; an unrelated Stacks tag would not provide a source. The proof is explicitly agent-written, not passed off as a proof read in the missing Bourbaki volume.

## Problems and changes

The imported item had no proof. Its statement is correct and is retained verbatim, including finite pair orders and the empty generating set. No STATEMENT-DISPUTED correction is needed. The Mathlib hits CoxeterSystem and IsCoxeterGroup cannot be used to prove the presentation: CoxeterSystem contains the presentation isomorphism in its definition (Basic.lean:153–158). Its length and alternating-word lemmas require that structure. Basic.lean:80 lists Matsumoto's theorem as TODO.

The inherited blueprint.from.node is null. The read-only command tools/blueprint_refs.py ancestor reports None, so the new node uses null too and adds the item to the existing via chain; I did not invent an ancestor. The inherited place is already precise, through the proof-(3) constructibility chain and the root-datum Coxeter presentation. The latest blueprint chapter and unit were read. No unit or chapter change is made. Searches of the full DAG and blueprint for Coxeter, dihedral, deletion, exchange and parabolic cosets found no blueprint statement supplying the generic two-descent assertion. In particular, root-system sign deletion assumes a root system and cannot replace a generic involution-group lemma.

## Not duplicates

lem-sfb-involution-two-descent-prefix vs lem-sfb-involution-deletion-presentation: the new lemma gives a reduced alternating prefix for an element with two specified left descents; it says nothing about free groups, relators, normal closures, arbitrary word reduction or presentations. The item proves those by induction and explicit relator bookkeeping.

lem-sfb-involution-two-descent-prefix vs lem-sfb-based-root-datum-coxeter-presentation: the existing node assumes a finite based root datum and proves its Weyl presentation by citing the present item; the new lemma assumes only deletion for an abstract group and proves a local length-factorization fact, with no root datum and no presentation hypothesis. Reusing the existing presentation here would be circular.

lem-sfb-involution-two-descent-prefix vs lem-sfb-root-sign-word-deletion: that statement deletes one letter in a root-system word when the image of a simple root is negative. The new statement has no root system and gives a common length-m prefix from two abstract left descents.

No Stacks-tag collision occurs: this is abstract Coxeter combinatorics and has no applicable Stacks tag.

## Argument behind the new statement (not part of its unsplit node)

There is a direct deletion-only route for its eventual worker. Write s=t_i, t=t_j, H=<s,t>. Deleting successively in any H-word gives a globally reduced H-word, so intrinsic H-length is the restriction of G-length. With r=st of order m, cancellation reduces every H-word to r^a or r^a s. These 2m elements are distinct. Within either family equality contradicts the order of r. If the families intersect then s is a power of r; s conjugates r to r^{-1}, so r=r^{-1}. Thus m<=2; m=1 contradicts s!=t, while for m=2 nonidentity s in <r> would be r and force t=1. Hence H has the usual 2m-cycle Cayley graph. Its unique element with both s,t as left descents is its opposite vertex, of length m, represented by both length-m alternating words.

Choose v of least G-length in the right coset Hg. For any u in H choose an intrinsic reduced H-word A (globally reduced as above), and a reduced word B for v. If AB is nonreduced, deletion applies. Both deleted positions cannot lie in A, by cancellation of the unchanged suffix and minimality of A. If at least one lies in B, the resulting factorization u v = u' v', with u' in H, puts v' in Hv while representing it with fewer than ell(v) letters, contradicting the choice of v. Consequently ell(uv)=ell_H(u)+ell(v) for every u in H. Write g=u v. The two left descents of g become the two left descents of u in the cycle. Thus u is its length-m opposite vertex. Take h=v. The equality of lengths implies both alternating-word concatenations with any reduced expression of v are reduced. This route uses deletion and the order of st, never the item's presentation or a CoxeterSystem.

## Review by Q36

I read the stage-1 brief, the chapter/unit records, the three-level rule, GOAL.md, and delivery-errors B–E, including their repeated imported section. For the item I checked the deletion characterization in Mühlherr–Weiss Theorem 6.2(D). I read Cashen Chapter 4 Theorem 1.3.2 (deletion gives exchange), Theorem 1.3.5 (word operations), Theorem 1.4.1 (passage to presentation), and the statement/proof of Lemma 4.0.14(2) for length-additive coset factorization. These are online supporting sources; neither the missing local Bourbaki proof nor Cashen's already-Coxeter hypotheses are silently assumed. I wrote the independent argument above for the exact new statement. The source's already-presented Coxeter group is not used as an input in either node.

For step 1 I checked from the definition of finite products of conjugates that N is a normal subgroup and that every relator has trivial image. The positive-letter replacement uses x_i^2 explicitly. Reversing either alternating block shows, for both parities of m, that the braid difference becomes (x_i x_j)^m modulo squares. A local replacement inside P(-)Q changes a word difference by conjugation by P, so normality gives the required stability. These are elementary group identities, not an uncited group-presentation theorem.

For step 2 I opened the complete new node statement and checked exactly the formula and reduced concatenations quoted in citations.json. Both distinct initial letters are left descents because their reduced tails have length n-1, and the pair product has finite order by the item's hypothesis. The induction compares tails of length n-1, never words of the current length n; the new reduced prefixes give the bridge on which one braid move acts. The common tail h really is the same for both alternating prefixes, as the cited statement expressly says. No clause of the new statement is inferred from the presentation being proved.

For step 3 I checked the induction on total word length. Reducing the suffix first is allowed by the induction hypothesis. Deletion yields a word of length r-1 when iR is nonreduced, and multiplication by t_i gives the reverse length bound, so a reduced Q has exactly r-1 letters. Thus iQ and R are both reduced words for v and step 2 applies. This is why arbitrary deletion is not asserted to be a legal square/braid operation. The node citation records the supporting statement already used to establish step 2, not a stronger word-reduction assertion absent from that statement.

For step 4 the only reduced word for the identity has length zero by the definition of ell. Combining this with steps 1 and 3 proves the actual kernel equality and not merely a quotient surjection. I checked the empty I case separately, the singleton case (only squares), and commuting distinct involutions (m=2, the new lemma gives st as the length-two opposite vertex). The same rank-two argument works when m is odd, in particular m=3; no commutation or evenness is presumed. G itself is not assumed finite anywhere. The new lemma only needs finite order for the one pair, weaker than the item requiring it for every pair. Nonidentity and injectivity ensure m>=2 and exclude the degenerate rank-two cases.

The new node is statement-only, introduces its own group, generating family, deletion, length, reduced words, exact pair order and alternating blocks, and cites the finite-set definition. I read the finite-set definition node; it defines precisely the one imported notion. It is a statement dependency, not a theorem used for length calculations. Every non-elementary external fact used by the item is the common-prefix assertion, with verbatim quotations for each citation. No proof step exceeds 2000 characters. The new lemma is strictly below the item: the braid comparison induction and all word reduction and free-group kernel bookkeeping remain in the item. All searches in its mathlib_searches were run with msearch.py and their logged results read; a second semantic phrasing found only already-Coxeter length facts. No new definition or elementary lemma node was created. I retained the old item searches and all imported metadata, and wrote only in the sandbox.

## Unfinished work

The new prefix lemma is deliberately unsplit, as required for one-level stage-1 delivery. Its complete self-contained statement, search evidence and suggested direct proof are available for its future worker. The item itself has a complete proof relative to this named dependency. No Lean was written and no compiler, Lake or build command was run.

Finite-case verification: an independent breadth-first enumeration of the explicit groups of pairs $(a,b)$ with multiplication $(a,b)(c,d)=(a+(-1)^b c,b+d)$ modulo $(m,2)$, for m=2,3,4,5,6, found exactly 2m elements, exactly one double left descent at distance m, and equality of the two length-m alternating products. This checks both parity cases and the commuting boundary without compiling Lean.
