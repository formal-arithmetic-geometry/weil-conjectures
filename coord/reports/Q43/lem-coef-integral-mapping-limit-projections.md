# Stage-1 delivery: lem-coef-integral-mapping-limit-projections

## Files written

- `dag/nodes/sec-six-functors/lem-coef-integral-mapping-limit-projections.json`: existing statement, now split into four assembly steps. Statement and statement dependencies retained. No new nodes; no new Mathlib leaves.
- `citations.json`: nine step/node entries, each quoting a verbatim part of the cited statement.
- `searches.jsonl`: five actual msearch.py searches for the item, including two semantic phrasings. Previous imported search records retained in the item; this attempt's actual queries appended.
- `report.md`: this report.

## Attachments

None. Searched the project source under `lean/WeilConjectures/` for the exact blueprint id and the mapping-limit/projection notions. No declaration stating this item was found. The ordinary etale derived Hom definitions concern different coefficients and do not provide an attachment for this pro-etale varying-coefficient assertion.

## WANTED

None. All sources used for the assembly are present in the read clone. The assembly follows the blueprint and the explicitly agent-formulated enriched calculus, not an assertion that a Stacks tag alone proves this coefficient-system result.

## Corrections and scope

No statement dispute; the statement is retained verbatim. The item was an unsplit statement created for the exceptional-adjoint proof. Its proof must distinguish Roos completeness from the invertibility of the specified unit. The definition `def-weil-derived-complete` explicitly declines to single out an actual completion map, so it cannot by itself justify the asserted canonical lambda. I use the existing stronger theorem `lem-pur-normalized-actual-reconstruction-maps`, which expressly proves invertibility of that actual unit. The existing `lem-coef-derived-system-evaluation-calculus` expressly supplies gamma as an isomorphism of derived mapping complexes and computes its projections; the scalar extension/restriction node alone only supplies a Hom-set adjunction, so I do not use it as an enriched adjunction theorem.

The completed sheaf R_W is retained throughout; no replacement by a discrete constant sheaf or by ordinary etale coefficients is made. Finite coefficients act on the second input by restriction and on the first by extension. No tensor/base-change assertion for integral internal Hom is used. No inference that projections jointly distinguish morphisms into a homotopy limit is made.

## Not duplicates

No new nodes. Whole-blueprint searches for `mapping limit`, `mapping-complex`, `Hom.*limit`, `reconstruction`, and `derived complete`, together with DAG searches for Roos reconstruction, actual units and mapping-limit comparisons, found the required existing reconstruction and system-calculus nodes. These are cited rather than recreated. The item's blueprint ancestor is `prop-coef-integral-exceptional-adjoint`; its paragraph 2 is the precise place retained in blueprint.from.place. No other blueprint node located states the entire enriched mapping comparison with its actual projections; same_as remains empty.

## Mathlib search review

Ran only the required msearch.py command for Mathlib searches. LeanFinder's first phrasing returned sheaf cohomology, local cohomology, Ext representatives and underived presentation maps. Its second phrasing returned fully faithful functors for discrete/condensed objects and the derived localization functor; their printed types do not concern the completed coefficient ring, strict semilinear systems or enriched derived limit adjunction. LeanSearch returned construction/localization of derived categories and exact-functor derived maps. Loogle with `"DerivedCategory", "Adjunction"` returned no hits. The source grep `derivedHom.*[Ll]imit|[Ll]imit.*derivedHom|mappingLimit|derivedComplete` returned no hits. All five queries and results are recorded exactly from this attempt in searches.jsonl and appended to mathlib_searches. No new node's unrun search is asserted.

## Review by Q43

I read the fixed chapter record `dag/chapters/sec-six-functors.json`, the inherited unit record `dag/units/sk-prop-sf-biduality-general.json`, and the current blueprint proof `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`. Its paragraph 2 reconstructs global mapping complexes at the two ends of the exceptional-adjoint calculation; the present four steps realize precisely that part, without changing the unit or chapter. I also read the reconstruction-coherence proof in the current blueprint and Stacks `sites-cohomology.tex`: Tag 07A6, label lemma-adjoint; Tag 0941, label lemma-derived-limit-is-ok; Tag 0A95, label lemma-RHom-well-defined; and Tag 08JA, label lemma-section-RHom-over-U. These support the derived adjunction, total-limit and Hom models used by the existing nodes. The enhanced varying-coefficient compatibility is explicitly the statement of the system-calculus node, not claimed to be verbatim Stacks material. No new node needs a source review.

For step 1 I opened `def-weil-derived-complete-integral-detailed` and checked that membership requires Roos completeness. I then read the entire statement and proof of `lem-pur-normalized-actual-reconstruction-maps`: its statement gives normalization of every reduction system and invertibility of the actual unit for every Roos-complete object, with no boundedness or Tor hypotheses. Its only extra geometric assumption, invertibility of ell on W, follows because W is over k of characteristic p different from ell. Small skeleton and module universes are the ones already fixed in the calculus. This avoids the invalid shortcut of claiming uniqueness of a lift to a homotopy limit.

For step 2 I opened `lem-coef-derived-system-evaluation-calculus`. Its final paragraphs state gamma for any ambient P and normalized N, as a natural isomorphism in D(Ab), and expressly include unit, counit and composition compatibilities. Step 1 supplies exactly normalization of N. Applying the derived Hom functor to the invertible actual unit is elementary functoriality; gamma then gives the displayed lambda, with exactly the same direction and second input as the item. Naturality at a composable g is written explicitly as u_T g = (L R g) u_Q before invoking the stated enriched composition compatibility. This uses the statement, not hidden resolution choices from the calculus proof.

For step 3 the same calculus statement gives both facts needed: gamma's nth projection is postcomposition with the actual total-limit projection followed by scalar adjunction, and the actual unit's projection is the reduction unit. It also gives the triangle identity. Consequently the Hom-set formula is e_(RQ),n (u_Q)_n h_n, and the evaluated triangle identity cancels the first two factors. This step is elementary relative to the stated formulas: it performs substitution and one triangle-identity cancellation. In particular, it does not assert that equal finite components imply equal maps into Rlim.

For step 4 I read the statements of `def-weil-derived-complete`, `def-weil-integral-derived-reduction`, `def-pur-derived-internal-hom` and `lem-pur-rhom-global-sections`, as well as the cited calculus. Shifting a distinguished Roos triangle preserves completeness, exact reduction commutes with shifts, and the displayed Hom-complex terms and differential give the usual target-shift identification. Hence step 3 applies to Q[r], with no sign introduced by reducing a degree-zero map P -> Q[r]. The cited global-sections lemma gives the precise H^0-to-derived-Hom identification; applying it with target Q[r] proves the assertion for every integer r. This is an elementary shift of the already proved projection identity, rather than an additional cohomological comparison theorem.

I checked the statement dependencies against their current statements, including the completed ring definition, the integral category definition and the finite scalar adjunction. No extra finiteness, perfectness, common Tor interval or constructibility condition is added by any use. The two off-unit statements are declared as generic tools in split_report.tool_uses: actual reconstruction and global Hom identification. The proof route is still reconstruction followed by enriched coefficient adjunction.

I tested the formulas on P=0, Q=0 and W empty (all mapping objects vanish), on W a geometric point and P=R (the comparison is the completion unit for Q), and on the identity h=1_Q (its projection is the finite identity by the actual triangle identity). Torsion Q, for example R/(varpi), is allowed: no flatness of Q and no false internal-Hom tensor base-change claim is used. Negative as well as positive shifts use the same exact reduction functor. The common support interval shifts with r, so these cases remain in the stated category.

Against delivery-errors B--E: there is no new statement-only node or potential duplicate; all proof objects and notions are already stated; citation statements were opened individually and quotations checked as literal substrings; all substantive ingredients have cited nodes; the remaining cancellations and shifts are explicitly elementary. The longest step is 712 characters, so no step exceeds the long-step threshold. The argument does not relabel the item's clauses into new nodes, and no source or statement change is concealed. Only the allowed sandbox files were written; no Lean, compiler, Lake, repository mutation or extra agent was used.

## Unfinished work

None in the stage-1 split. The existing lower nodes remain their own DAG obligations. The required delivery checks and push are performed by deliver.py after this report is written.
