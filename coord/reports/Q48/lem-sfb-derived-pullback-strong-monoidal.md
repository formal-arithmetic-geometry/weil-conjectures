# Q48 — lem-sfb-derived-pullback-strong-monoidal

## Files written

- `dag/nodes/sec-six-functors/lem-sfb-derived-pullback-strong-monoidal.json`: statement unchanged; four proof steps; status split. No new nodes and no new Mathlib leaves.
- `citations.json`: nine verbatim statement quotations, one for each step/node citation.
- `searches.jsonl`: actual msearch log, retained without rewriting.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint identifier, the instance name and the derived pullback/tensor notions. The relevant declaration is `AlgebraicGeometry.ProEtale.CondensedRing.monoidal_leftDerivedUpperStar` in `SixFunctors/ProEtale/ModuleObject/Derived/Monoidal.lean:305`. Its associativity, left-unitality and right-unitality fields are all `sorry` (314–316). Thus it is not a finished project proof. The generic construction in `lean/Sheaf/` is useful corroborating source, but is not offered as an upstream attachment.

## WANTED

None. All sources used were already present. No downloads, Lean edits, compilation or builds were performed.

## What changed and what was wrong

The imported item had no proof. Its statement is correct, including the specified maps; it was left verbatim. Its contextual blueprint source `det-proper-image-localizing-open` states the extension-by-zero/localizing assertion and supplies no tensor-coherence proof. I therefore marked the proof as an agent-written identification using the existing module-derived-pushpull and derived-monoidal constructions, rather than claiming that the contextual blueprint text proves these identities.

The whole DAG search found `new-proetale-derived-module-pullback-monoidal`, an existing split-and-reviewed node, whose statement already includes the arbitrary-condensed-ring monoidal pullback, both universal tensor counits, invertibility, and the exact unit formula. I reuse that statement instead of creating any nodes for the same theorem or its coherence clauses. Its maintained source field cites Bhatt–Scholze places which its own proof_origin and previous review explicitly say are not a source for this full theorem. I did not use those places as a proof or edit that node. Its actual split and the local derived-monoidal blueprint proof give the formal route.

I added `def-sfb-strong-monoidal-functor` to the item's statement dependencies to name its structure and coherence convention. All maintained metadata, including the upstream Lean records, source and blueprint ancestor, is preserved. No target, chapter or unit statement is changed. The item's unit is the open-ctf unit; the reused derived pullback theorem is declared as an off-unit categorical tool in split_report.tool_uses, supplying the monoidality input without changing the extension-by-zero proof route.

## Not duplicates

No new node was created. The potential duplicate is precisely the existing `new-proetale-derived-module-pullback-monoidal`, which is cited. Whole-DAG keyword and declaration searches and `tools/blueprint_refs.py search` for pullback and monoidal found no additional imported blueprint node stating these prescribed maps. In particular `lem-sfb-derived-monoidal` constructs the monoidal derived category, not this functor, while `lem-sfb-derived-pullback-tensor-comparison-iso` gives invertibility without the three coherence axioms. Neither is silently used for the stronger claim.

## Mathlib searches

The seven actual queries are recorded in searches.jsonl and appended, with the same tool and exact query, to the item. LeanFinder was tried for the condensed-module version and then the general exact strong monoidal functor version. Its hits concerned light condensed monoidal categories and Tor/total-derived-functor constructions, respectively. LeanSearch returned underived sheaf-module pullback, its adjunction and ordinary module-category monoidal instances. Loogle returned no joint leftDerived/Monoidal match, and the CoreMonoidal.toMonoidal query returned only the constructor and its projections. The two grep phrasings returned no derived-monoidal construction in Mathlib. I read CoreMonoidal at Mathlib/CategoryTheory/Monoidal/Functor.lean:620–651 and toMonoidal at 727–730: they require the associativity and two unit proofs, so they do not prove the item by a one-line specialization. All services answered; none was recorded as unavailable or as a match to the full item.

## Review by Q48

I read the item, its six-functors chapter, the open-ctf unit, the contextual main-20261015 blueprint node, and the actual module-derived-pushpull and derived-monoidal proof files. I read the full statement and split of `new-proetale-derived-module-pullback-monoidal` and compared its data against the upstream Monoidal.lean definitions (the two derived counits, universal comparison, unit isomorphism and final instance). I also read Stacks sites-cohomology.tex, Tags 0FPQ (lemma-symmetric-monoidal-cat-complexes) and 0FPT (lemma-symmetric-monoidal-derived), and the strong-monoidal convention node with source Tag 0FFL. Those Stacks results concern complexes/derived monoidal structures; I do not attribute the arbitrary-condensed functor theorem directly to them. No prohibited SGA source is used.

Step 1 uses the module-derived-pushpull definition to identify LF as the derived functor of the full composite Ext_alpha composed with mapMod, and the derived-tensor-hom definition's Layer B to fix the relative derived tensor. The existing pro-etale theorem's statement introduces exactly these objects and has no finite-coefficient or boundedness restriction: it says all assertions hold for arbitrary Lambda, f and unbounded complexes. Thus all of its hypotheses are already the item's hypotheses. This step uses its strong monoidal existence assertion, not an unquoted detail of its proof.

Step 2 checks actual maps. I opened both `def-sfb-upper-star-tensor-counit` and `def-sfb-derived-pullback-tensor-left-counit`: the former states Q_X(b) after the localization tensorator, and the latter states E(mu_Y) followed by the derived counit. Tensoring the unary counits gives exactly r, while the second definition gives exactly l. The reused theorem's statement explicitly displays these same r and l, says they exhibit total left derived bifunctors, and characterizes delta by r delta = l. The item's comparison is the unique universal lift for those counits, hence delta = m as transformations. This is equality of the specified comparisons, rather than choosing an isomorphism between their objects. No unnamed tensor-coherence or comparison-identification lemma is hidden here.

Step 3 uses the reused theorem's explicit unit clause: its inverse unit is gamma at Lambda_Y[0] followed by the ordinary unit comparison in degree zero. I checked the coefficient direction F(Lambda_Y) to Lambda_X and the inverse direction needed for the lax unit. They coincide with leftDerivedUpperStarUnitIso and its inverse in the upstream construction, with the native derived units Q_T(Lambda_T[0]). This step is just identification of those identical formulas.

Step 4 uses the existing theorem's strong structure and `def-sfb-strong-monoidal-functor`. I read the latter's displayed equations and checked the positions and directions of each associator, tensorator and unit. Substituting delta = m and the explicit unit into those equations yields exactly the three displayed laws for nu = m inverse and e = c inverse. The inverse of a natural isomorphism is natural, so this also accounts for both tensorator naturality fields. These elementary substitutions do not assert a new general descent theorem.

For B–E of delivery-errors, I checked that no new node restates a clause or elementary fact; every proof citation is to a statement I opened, and every non-elementary input is the statement of an existing node. citations.json records verbatim parts used by each step. The two non-elementary steps are below 2000 characters (all four steps are below that limit). No proof is inferred from a mere definition of flatness, no preservation of quasi-isomorphisms is mistaken for preservation of K-flat objects, and no internal-module category is replaced with sectionwise modules. I checked the dependency closure for a return path to this item before delivery; the cited pre-existing theorem predates this item and does not depend on it.

The edge cases do not impose hidden hypotheses: for f an identity the two counit formulas are the usual identity-derived ones; the zero ring and empty schemes give zero module categories and the same unit equations; complexes concentrated in degree zero recover the ordinary tensorator; unbounded complexes are covered by the reused theorem's explicit final sentence. No finite Tor dimension, flat coefficient ring, scheme finiteness or boundedness was introduced. Since no statement was changed and no new lemma was created, no statement dispute or unproved edge case remains to report.

## Unfinished work

No part of the requested stage-1 split is left unfinished. This delivery supplies a natural-language DAG proof; it does not claim to fill the upstream Lean sorries.

## Dry-run repairs

The first server dry run rejected two occurrences of the phrase “the item's” as non-self-contained references. I replaced them with the locally introduced comparison m and the prescribed monoidal data. The mathematical argument and statement are unchanged.
