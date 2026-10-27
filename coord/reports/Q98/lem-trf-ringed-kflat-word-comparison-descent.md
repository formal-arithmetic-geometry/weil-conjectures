# Q98 stage-1 delivery: lem-trf-ringed-kflat-word-comparison-descent

## Files written

- dag/nodes/sec-trace-formula/lem-trf-ringed-kflat-word-comparison-descent.json: existing statement, now split into ten proof steps. Mathlib verdict: not a leaf; generic comparison and localization APIs cover only parts.
- citations.json: one entry per step/node citation, quoting the cited statement verbatim.
- report.md: this report. searches.jsonl records five fresh searches; the item's six inherited search records were retained.

New nodes: 0. New Mathlib leaves: 0. No Lean, unit, chapter, repository or launcher file was changed. The local write_split.py only prepares the sandbox JSON and citations.

## Attachments

None. Searched the live WeilConjectures library for the exact blueprint tag, KFlat/K-flat, and word/comparison terminology. Its existing resolving-class extension declaration is only an ingredient, not the whole item. No declaration states all clauses of this item with a closed proof.

## WANTED

None. All source material used is available locally.

## Problems found and changes made

The item was statement-only, with no proof or proof dependencies. Its statement is correct with its specified flat-term K-flat normalization; it is retained verbatim. The existing six Mathlib searches are retained and five searches actually run by Q98 were appended. No source or statement dispute was found.

A mere appeal to edge left-derived universal properties would leave composite counit invertibility and whiskering unresolved. Instead the split first proves preservation along words, then explicitly descends the normalized comparison on a common resolving class. Both precomposition and postcomposition are calculated with the same composite counits. Postcomposition uses naturality of the edge counit on the actual chain map, not preservation of arbitrary quasi-isomorphisms by a nonexact functor.

The chapter and sk-thm-trace-transport unit were read. This item is not the key unit node, so no realized field is edited. Its generic homological algebra serves the coefficient-pullback compatibility in the existing ancestor chain, ultimately the Frobenius transport sentence in prop-trf-karoubi-independence.proof.md. The unit's coefficient-reduction and field-extension route is retained. Five off-unit generic tools are declared in split_report.tool_uses, with the role each serves.

## Not duplicates

No new nodes were created. Whole-DAG searches by 06YS, 0G7E, 06YY, 0D6D, K-flat resolution and localization/natural-transformation terminology found the existing ingredients used here. Blueprint searches for K-flat, resolving and word comparison found no blueprint node stating the full item. In particular the ringed-space-only pullback preservation node was not substituted for the arbitrary-ringed-site statement; the existing site-level lem-weil-pbc-ringed-topos-kflat-pullback was reused.

## Review by Q98

I read the item source in sites-cohomology.tex: 06YS (lemma-K-flat-resolution), 0G7E (lemma-pullback-K-flat), 06YY (lemma-derived-base-change), and 0D6D (lemma-derived-pullback-composition). These prove the resolution, preservation and computation ingredients, not the entire arbitrary-natural-transformation assertion. The latter is an agent argument using the existing resolving-class extension theorem and localization full faithfulness. I also read derived.tex's 05RT and the dual left-derived part of lemma-find-existence-computes, categories.tex's 04VK, and sites-modules.tex's 03EK tensor definitions/formulas. The blueprint ancestor proof's final transporting-isomorphism assertion was read in main-20261015. There are no new-node sources to audit.

For Step 1 I opened the complete statements of lem-pc-kflat-resolution and lem-weil-pbc-ringed-topos-kflat-pullback. The former gives one incoming quasi-isomorphism of entire complexes, with flat terms; the latter gives both K-flatness and flat terms for arbitrary ringed-topos pullbacks without structural flatness. These are exactly the two induction inputs. They apply to the independently sized small sites after choosing the sufficiently large coefficient universe of the statement. No boundedness or enough-projectives hypothesis is introduced.

For Step 2 I checked that lem-weil-pbc-pullback-resolving-computation explicitly asserts invertibility of the counit of the supplied complex-level universal derived pair on a flat-term K-flat complex. It is not merely an existence theorem or a computation for a differently chosen derived functor. The composite formula has the correct order: first apply LF_a to the preceding word counit, then use the edge counit on the ordinary intermediate complex. The base is the identity counit for the empty word.

Step 3 cites def-weil-abstract-derived-category precisely for the homotopy-category presentation and localization. The conjugation formula is checked directly by naturality of the two counits and the ordinary transformation. Additivity sends a displayed chain homotopy to a chain homotopy, so every homotopy morphism between resolving objects satisfies that naturality equation. This uses no full-faithfulness claim about inclusion of resolving complexes in the derived category.

For Step 4 I opened the statements and the short existing proof of lem-sc-nattrans-from-resolving-class, and read its project Lean source. It requires a right calculus, an incoming weak equivalence from a resolving object for every source, inversion of weak equivalences by A, and naturality on every morphism between resolving objects. The split supplies each hypothesis: 05RT through lem-pc-quasi-isomorphisms-multiplicative-system, Step 1, the localization Q, and Step 3, respectively. Both A and B are functors on the homotopy category with derived-category target. I opened lem-weil-pbc-localization-universal-property; clause (2) is exactly natural-transformation descent, not just descent of functors. This is the non-elementary extension step and is cited as such.

Step 5 uses clause (3) of that same localization node only after writing the naturality conjugation along an incoming resolution. Since Q(p) is invertible, all components at Q(K) are forced. This also proves determination for arbitrary derived word transformations, independently of whether they arise from an ordinary cell. Steps 6-8 use this proved uniqueness and carry out identity, vertical-composition and both whiskering checks directly. In Step 7 the pre-edge output remains resolving. In Step 8 the edge counit naturality square relates LF_a(Q(C(t))) to Q(C(F_a t)); the proof never applies F_a to a general resolution and calls the result a quasi-isomorphism. These are short calculations from the preceding steps, not uncited standard comparison lemmas.

For Step 9 I opened def-pur-sheaf-tensor-product; it defines the tensor as the sheafification of the sectionwise tensor and the corresponding change of rings. The associator and identity scalar map are given with their explicit inverses. Balancing proves the composites are identities and makes the maps natural; restriction compatibility gives the sheaf maps, and termwise naturality gives chain maps. Steps 4-6 then give precisely the required unique derived normalizations, without moving an associator clause into a new node.

For Step 10 I opened def-coef-ringed-sequence-site. Its statement expressly realizes strict quotient-semilinear systems as module sheaves on the sequence site and specifies their ordinary unbounded derived category. That is all this step takes from it. The input resolution is therefore a complex of whole systems; it is never a collection of independently chosen levelwise resolutions. No inverse limit or preservation statement about evaluation is invoked.

I checked delivery-errors B-E point by point. All non-elementary inputs are statements of cited nodes, and citations.json quotes those statements literally. There are no new elementary, duplicate, Mathlib-covered, or clause-restating nodes. The proof is not circular: the normalization is first constructed on resolving objects, then extended by an independent generic theorem, and only then used to establish coherence. The original statement and metadata are retained. All non-elementary steps are under 2000 characters; the longest is Step 4 at 896 characters and simply instantiates the extension and localization statements, with no hidden comparison lemma.

Small cases checked: empty words and identities; the zero complex and zero ring; a single scalar change and its identity map; two successive nonflat scalar changes such as Z to Z/4 to Z/2 (no exactness of scalar change was assumed); arbitrary noninvertible ordinary cells; and a sequence system not satisfying normalization. The proofs require no excluded nonzero, flat-structural-map, boundedness, normalization or finite Tor-amplitude hypotheses. The ordinary associator inverse also works for the zero ring. The final whole-system application does not infer equality merely from levelwise evaluations.

## Unfinished work

None in this one-level split. Existing unsplit dependencies remain their own items. Server dry-run and delivery results are recorded by the delivery tool.
