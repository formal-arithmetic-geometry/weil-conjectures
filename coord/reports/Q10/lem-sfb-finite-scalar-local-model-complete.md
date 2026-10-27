# Stage-1 delivery: lem-sfb-finite-scalar-local-model-complete

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-scalar-local-model-complete.json`: item, statement unchanged, five proof steps, eighteen existing proof dependencies. Mathlib does not state the item.
- `citations.json`: one verbatim statement quotation for each step/dependency pair.
- `report.md`: this report.

No new nodes; no new Mathlib leaves. Sandbox research aids `bhatt-scholze.txt` and `write_split.py` are not project files.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag and finite-scalar/local-model terminology found no declaration stating this item. The derived completeness declarations in the existing integral/constant-coefficient development have different coefficient conventions or extra hypotheses; they are not attachments of this arbitrary-scheme, actual-unit statement.

## WANTED

None.

## Findings and corrections

There was no prior sandbox split. The current item was unsplit and has no released repair order. Its statement is retained in full. In particular, the scalar modules may have torsion, the scheme need not be Noetherian or qcqs, rank zero is included, and the specified augmentations and quotient transitions are retained.

The cited blueprint Local models paragraph proves a finite free resolution and Tor amplitude, rather than the present completeness assertion. I therefore mark the completion assembly as agent-written, using the actual Bhatt--Scholze text and existing strict cone/Roos comparison statements. The proof does not invoke the Noetherian stratification completeness criterion, whose hypotheses would not apply. It also does not assume arbitrary scheme inverse image commutes with countable limits: the locality argument is only for objects in a covering site and uses literal slice restriction.

I read the chapter `sec-six-functors-basics`, the recorded unit `sk-prop-sf-comp-coherence` (filed in smooth purity), and the item's blueprint ancestry. This coefficient calculation serves the existing refinement closed-complement calculation and changes no chapter or unit route. The cross-unit proof citations are declared individually as generic tool uses in split_report; none replaces the compactification argument.

## Not duplicates

No new nodes were created, so there are no new/existing pairs. Whole-DAG title/statement and blueprint searches for completion, replete, finite constant, and derived complete found the reusable resolution, integral-limit and strict-completion tools. In particular, I reused the existing general covering-conservativity node `lem-zl-condensed-cover-restriction-conservative`; the Noetherian stratum-completion nodes cannot be used with this statement. `lem-sf-perfect-over-derived-complete-ring` concerns ordinary ring modules rather than ring sheaves. `lem-pur-completed-line-complete` concerns lines with the older finite-field coefficient presentation, and does not state this item.

## Review by Q10

I checked delivery-errors B--E against the actual node statements and the sources. There are no new nodes to conceal a restatement of a clause, a trivial specialization, a proof sketch inside a statement, or an unsearched Mathlib leaf. Each proof step is below 2000 characters; none moves the conclusion to a fresh black box. All original item metadata was preserved, blueprint.from.place was already specific, and blueprint.same_as remains empty after the whole-blueprint search. The statement is not disputed.

I read the current blueprint source `sec-proetale-coefficients/sk-def-localizing-closure/sk-def-localizing-closure-ctf-equals-bc.proof.md`, especially Local models and Locality. I read Bhatt--Scholze, The pro-etale topology for schemes, Propositions 3.1.9--3.1.11, Section 3.4's paragraph after Definition 3.4.1, and Proposition 3.5.1 with its proof. Section 3.5 concerns a constant Noetherian ring: I do not apply it directly to the continuous ring sheaf B. Instead, the existing principal/Roos statements already identify the strict model with the completion stipulated by the item. I also opened Stacks sites.tex Tag 03CE (lemma-localize-given-products), the restriction/relocalization framework, and Tag 04TQ (lemma-glue-maps); sites-modules.tex Tag 03DJ (lemma-extension-by-zero-exact); and derived.tex Tags 014A (lemma-third-isomorphism-triangle) and 0152 (lemma-derived-canonical-delta-functor). No SGA source is used.

For Step 1 I opened all six cited statements. The integral-limit node gives B = lim k_n on every scheme, and the constant/completed comparison gives flatness and B/pi^n = k_n. The local-field node gives a DVR with nonzero uniformizer. These are exactly the domain/flatness/nonzero-scalar hypotheses of the cyclic-resolution lemma. The principal-cone node supplies the strict transition and augmentation formulas, and the cone/short-exact lemma gives the quotient quasi-isomorphism. I wrote both commuting equations in coordinates; I do not infer a strict tower isomorphism from unrelated isomorphisms in each derived category.

For Step 2 I opened the surjective-tower theorem: its hypotheses allow arbitrary schemes and arbitrary module ring sheaves. The transitions here are epimorphic because the quotient map from B^d factors through the preceding quotient. Its Roos sequence and projection normalization, together with the integral-limit statement, prove the free-case unit is invertible. I opened the Roos-calculus and completion-triangle statements to check that they preserve the augmented strict map and that its augmentation is precisely c, including its zero shifted-product coordinate. The finite coordinate rearrangement is a definition-level calculation, not an extra theorem about infinite tensor products.

For Step 3 I opened the DVR, flat coefficient comparison and scalar-model resolution statements. The resolution node explicitly includes arbitrary finitely presented scalar modules with torsion and does not impose Noetherianity on the site scheme. The SES-triangle statement supplies its distinguished triangle. The completion-triangle node gives a morphism of distinguished triangles including the last square, rather than just three independently natural arrows. The triangle-isomorphism node then applies because the two free units are invertible by Step 2.

For Step 4 I opened the weakly-etale localization, coefficient-sections localization, exact restriction, sectionwise products, localized-site definition, principal-cone, Roos-calculus and completion-triangle statements. The first two identify the actual ring and scalar identifications on U, so the restricted scalar pi is the same scalar. The products theorem explicitly states its sectionwise formula, and the localized-site definition explicitly states F|U(V/U) = F(V); these formulas prove the product comparison without an additional limit-preservation assertion. Exactness and finite sums give the cone comparison. Applying these formulas termwise to the strict principal/Roos constructions proves their compatibility with transitions and augmentations; descending an exact functor through quasi-isomorphisms gives the stated natural unit square. This is the direct cochain argument underlying Bhatt--Scholze's locality paragraph, not an uncited general derived base-change theorem. I did not invoke the Noetherian adic-stratum-completion-unit node.

For Step 5 I opened the completion-triangle statement for naturality and the condensed-cover restriction-conservativity statement for joint reflection of derived isomorphisms. The latter explicitly assumes only a scheme, a condensed ring and a pro-etale covering family, exactly the situation here; it identifies the functors with slice restriction. The local model is one of the global scalar models handled in Step 3. Thus the actual unit, and not only the existence of an abstract isomorphism to a limit, descends.

Small cases checked: T empty; d = 0 and P = 0; P = A and P = A/pi^r with r >= 1; n = 1; arbitrary non-Noetherian T; and an infinite covering family. For P = A/pi^r the derived reductions can have H^-1, so I deliberately use the finite resolution and completion-unit triangle rather than falsely identifying its reduction tower with ordinary quotients. Only the free case uses that identification, where multiplication by pi^n is injective. There is no torsion-freeness assumption on P. An ancestry traversal of all selected dependencies found no path back to this item.

I ran the required Mathlib search command with two semantic phrasings, LeanSearch, Loogle and source grep; every new record is copied from searches actually run. The hits included ordinary `IsAdicComplete`, scalar `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`, sheaf finite presentation, and condensed module constructors. I read Mathlib/RingTheory/AdicCompletion/Basic.lean:47--56 and AsTensorProduct.lean:320--330: these are ordinary scalar-module adic completion statements and do not supply the pro-etale derived assertion or actual-unit normalization. All searches and any service failures are retained accurately in searches.jsonl and mathlib_searches.

## Unfinished work

None at the level of this split. The cited existing nodes remain separate items in the project. Server dry-run and delivery results are reported by the delivery tool.
