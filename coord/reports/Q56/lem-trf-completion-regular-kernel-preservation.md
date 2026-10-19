# Q56 stage-1 delivery

Item: lem-trf-completion-regular-kernel-preservation. Statement unchanged.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-completion-regular-kernel-preservation.json: statement, split into seven steps; no exact Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-local-regular-generators-same-length.json: statement-only unsplit lemma; no Mathlib match after LeanFinder (two phrasings), Loogle, LeanSearch and source grep.
- citations.json: one verbatim statement quotation for each of the 18 step/node citations.
- report.md: this report. searches.jsonl is the search command's append-only record.

## Attachments

None. I searched the project's WeilConjectures tree for the blueprint tag, completion/regular-sequence terminology and same-length/change-of-generators terminology. The project Regular/RegularSequence.lean file proves flat ascent of weak regularity, not the present completed-kernel equivalence. The pinned Mathlib Regular/Flat.lean gives IsRegular.of_faithfullyFlat (lines 86 and 92) and ascent of weak regularity (lines 34 and 47), but these do not state the item or its generator-change lemma. No master sorry declaration is treated as a proof.

## WANTED

None. All mathematical sources used here are available in literature/stacks-project/.

## Problems found and corrected

The unsplit item had no proof. Its statement is true without assuming that R is regular. Its protected source field mentions regularity of the completed local ring and Tag 07NY, but that additional result is unnecessary: the statement only concerns regular sequences. I retained the field and did not add any regular-ring hypothesis.

One cannot reflect existence of regular generators merely by applying faithful-flat descent to a tuple chosen in the completion: its entries need not be images of elements of R. The split supplies that missing generator-choice argument. The conormal basis counts the generators, reduction of the completed module I identifies the two generator spaces, and Nakayama supplies generators in I of precisely that length. A separate, general change-of-generators lemma then applies to their images. This is strictly smaller than the completion claim and is not one of its clauses.

The exactness argument also spells out reflection of each nonzerodivisor condition. In step 6 I use two short exact sequences, including the image of multiplication. This ensures that the cited exactness statement for short exact sequences actually identifies the kernel of the completed endomorphism; it does not assume that the multiplication was injective before proving it.

## Unfinished work

Only the new lemma remains unsplit, as required for a one-level stage-1 delivery. No proof gap is left inside the item's seven steps conditional on its cited node statements.

## Blueprint and route

I read the chapter record sec-trace-formula, unit sk-i-curve-zero, the current main-20261015 unit and lem-trf-local-term-locality proof, and the existing ancestor chain through lem-trf-regular-quotient-completion-kernel-test. This is a commutative-algebra tool below the nodal-completion argument; it does not replace a step of the unit. The item's existing blueprint.from place already specifies the canonical completion comparison in 09Q1, and is retained. The new node follows that ancestry through the item, with via [lem-trf-completion-regular-kernel-preservation, lem-trf-regular-quotient-completion-kernel-test].

Whole-blueprint searches for regular sequence, minimal generators, flat-increases-depth, generators, 066A, 00LM and regular, and whole-DAG searches for the tags and mathematical terminology, found no existing same-length generating-tuple theorem. The existing conormal, graded-polynomial, quasi-regular and regular-local maximal-ideal nodes are distinct. No unit realization fields need changing: this item is not the unit's key statement. The existing completion and conormal tools are in sk-thm-p1, already inside this unit's route; the new lemma inherits this item's unit. No SGA source is used.

## Not duplicates

lem-trf-local-regular-generators-same-length vs lem-weil-pbc-regular-sequence-conormal-free: the existing 00LN node gives the specified basis of J/J^2 from a regular tuple; the new node proves regularity of another generating tuple and has no conormal conclusion.

lem-trf-local-regular-generators-same-length vs lem-pur-regular-sequence-graded-polynomial: the existing 00LN node identifies the associated graded algebra for a given regular tuple; the new node changes the generating tuple, with a Noetherian local hypothesis.

lem-trf-local-regular-generators-same-length vs lem-pur-quasi-regular-noetherian-local: the existing 061S node assumes the graded polynomial map for the specified tuple is an isomorphism; the new node assumes a different tuple is regular and only that the specified tuple generates the same ideal with the same length. The missing step is the independence-of-generators result 066A.

There is no existing node with source Tag 066A. The regular-local-generators node only treats a minimal set generating the maximal ideal of a regular local ring, whereas this lemma treats any ideal in any Noetherian local ring.

## Review by Q56

I read Algebra 00MA (lemma-completion-tensor), 00MB (lemma-completion-flat), 05GG (lemma-hathat-finitely-generated), 05GI (lemma-radical-completion), 0316 (lemma-completion-Noetherian-Noetherian), 00DV (lemma-NAK), 00IK (lemma-Noetherian-basic), 00LF (definition-regular-sequence) and 00LN (lemma-regular-quasi-regular), and Divided Power Algebra 09Q1 (lemma-quotient-regular-ring), including their proofs. For the new node I read More on Algebra 066A (lemma-independence-of-generators), its statement and proof, and Algebra 061S (lemma-quasi-regular-regular), with 00LN. Tags were checked in tags/tags. The new node is the combination regular implies quasi-regular, independence of a generating tuple of the same length, and quasi-regular implies regular in the Noetherian local case. Its future proof may cite the existing 00LN/061S nodes when it is split; no proof is embedded in its statement now.

I opened the full statement of every cited node, and citations.json copies those exact statements rather than paraphrasing them.

Step 1 uses local-completion-local-ring for precisely the maximal ideal and residue-field identification, adic-completion-noetherian for S Noetherian, quotient-local-structure for the maximal ideal of B, local-completion-quotient for the canonical surjection and kernel IS, and completion-exact-finite-modules for the S-linear injection of the module completion of I with that image. R is Noetherian local, I is finite by hypothesis, and R and R/I are cyclic finite R-modules, so every exactness hypothesis holds. The completion of the module B is the completion of the ring B because the filtrations are termwise equal.

Step 2 uses module-completion-complete clause (2), with ideal m, module I and exponent 1, not a ring-only reduction theorem. The ideal m is finitely generated since R is Noetherian. Under the S-linear identification of step 1, the R-submodule mI^ maps to mJ; expanding an element of mS shows that mJ=nJ. Thus the isomorphism really carries the classes of a in I to the classes of c(a), not just an abstract equality of dimensions. This is a short calculation from the cited statements, marked elementary.

Step 3 uses the regular-sequence definition for the prefix multiplication injections, exact completion for their short exact sequences of finite cyclic quotients, and local-completion-quotient for the actual completed prefix rings. Because each completion map is coordinatewise and S-linear, its conjugate is multiplication by the image of the same f_i. The final quotient is nonzero since the generating elements lie in the proper maximal ideal n. The empty sequence requires no prefix argument.

Step 4 takes exactly the basis conclusion from regular-sequence-conormal-free. Since J is inside n, J^2 is inside nJ, and the quotient of that displayed isomorphism by n/J is componentwise k^r. This gives the length of the basis of J/nJ and explains why all r generators can be matched downstairs. No assertion about the basis is taken from an unstated part of the source or from a proof of the cited node.

Step 5 applies nakayama-local-generators to the finite R-module I, after choosing and lifting a basis of I/mI. The images of its r generators generate IS directly by expanding coefficients. The new same-length lemma is applied only after step 1 has established that S is a nonzero Noetherian local ring, and with J inside its maximal ideal. Both tuples have length r, lie in J, generate J, and the y tuple is regular by the reverse hypothesis. These are all the new lemma's hypotheses.

Step 6 uses noetherian-submodule-finite for both the kernel and image of multiplication in a cyclic module, exact-finite-module completion twice, and local-completion-quotient for the prefix quotient and its explicit multiplication. The quotient by the image is finite because the quotient of a finite generating list generates it. After regularity upstairs forces K_i^=0, module-completion-complete implies K_i/mK_i=0 and nakayama-local-generators with N=0 implies K_i=0. The regular-sequence definition then gives the result, since R/I is nonzero. This avoids any uncited preservation or reflection theorem about tensor products or faithfully flat maps. Step 7 is the elementary combination and empty-sequence check.

I checked small cases for the item: I=0 in a field (empty tuple); I=(x^2) in k[x]_(x), with kernel (x^2) in k[[x]]; I=(y) in the nonregular local ring (k[x,y]/(x^2))_(x,y), where y remains a nonzerodivisor; I=(x) in that same ring, where x is a zerodivisor before and after completion; and I=(x^2,xy) in k[x,y]_(x,y), where the two minimal generators do not form a regular sequence on either side. These check that no regular-local hypothesis has been smuggled in and that regularity is not inferred just from finite generation.

For the new node I checked r=0, J=0; r=1 with a principal nonzerodivisor ideal; two generating tuples (x,y) and (x+y,y) in k[x,y]_(x,y); and the reason the length condition cannot be dropped: (x,x) also generates (x) but is not regular. The maximal-ideal and Noetherian assumptions are retained because the quasi-regular-to-regular implication uses them. The comparison node does not claim arbitrary ideals in a regular local ring are generated by regular sequences.

I checked B through E of delivery-errors point by point: the new node introduces every object, defines local ring inline, cites the notions it needs, has no proof, records actual logged searches and has complete blueprint ancestry. I ruled out a duplicate, an elementary two-line fact, a restated clause, and an exact Mathlib leaf before creating it. The item's proof_deps is exactly the union of uses, and every non-elementary invoked fact is a cited statement. Every proof step is shorter than 2000 characters; the short comparisons are explicit applications of the displayed node statements and elementary quotient computations. No target, unit route, protected metadata, compiler state or live file was changed.
