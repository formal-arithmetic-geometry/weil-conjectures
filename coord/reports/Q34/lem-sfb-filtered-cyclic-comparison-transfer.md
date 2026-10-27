# Stage-1 report: lem-sfb-filtered-cyclic-comparison-transfer

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-filtered-cyclic-comparison-transfer.json: statement, split; no Mathlib match. Statement unchanged. Five proof steps; no new nodes and no Mathlib leaves added.
- citations.json: one verified verbatim statement extract for every cited node in every proof step.
- searches.jsonl: actual search-command results. Existing item searches preserved; five freshly logged searches appended to its mathlib_searches.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag, filtered/cyclic comparison terminology and condensed invariants. No declaration states this item. The existing Sheaf statements for the comparison and continuity are source material, not finished proofs or attachments.

## WANTED

WANTED: an external non-SGA reference stating this precise normalized internal condensed cyclic filtered-passage assembly, for lem-sfb-filtered-cyclic-comparison-transfer. The proof is agent-written from already recorded theorem statements; the current blueprint is not asserted to contain this auxiliary lemma verbatim.

## Corrections and source scope

No statement dispute or correction. The current blueprint is literature/blueprint/latest, snapshot main-20261023-1620, commit 7284bb09daf97437d544c51882b325f9c52cd345. I read its six-functors-basics stability unit and direct-images proof, especially paragraph (3). This paragraph now delegates open direct image to sk-prop-open-coefficients. The item's historical source path is preserved as required, but the proof_origin points to latest and explicitly identifies the argument as an agent assembly. blueprint_refs.py ancestor reports None for this item; the inherited null ancestor and full via chain are retained, rather than inventing an ancestor. The blueprint search for 'cyclic comparison' returned zero matches.

DAG searches found lem-sfb-profinite-invariants-filtered-continuity, already split, which supplies exactly the nontrivial continuity assertion and creation of the sheaf colimit. Its supporting action-site/cohomology nodes were also read to check scope: this is internal sheaf cohomology, not discrete continuous group cohomology or topological completion. Exactness by itself is used only for the two-term complex, never to justify the derived-invariants continuity theorem.

## Not duplicates

No new nodes. Existing lem-sfb-profinite-invariants-filtered-continuity supplies a_q; existing lem-sfb-arrow-exact-colimits supplies the kernel/cokernel preservation needed for b_q. No new node is a restated clause, elementary observation, or duplicate.

## Review by Q34

I checked the complete item against the latest blueprint and delivery-errors B through E. No new nodes require separate literature verification. I read Stacks sites-cohomology.tex, Tag 0739 (lemma-colim-works-over-collection), including its finite-cover and finite-fibre-product hypotheses and proof, as the source behind the existing internal continuity theorem. I also read sites-modules.tex, Tag 03DB (lemma-limits-colimits), including its proof of sheaf colimits, preservation by underlying abelian sheaves and filtered exactness. For detection of derived isomorphisms I read derived.tex, Tag 05RT (lemma-acyclic), its saturated quasi-isomorphism statement and derived-category definition. The normalized cyclic comparison is an existing agent-formulated theorem, not an external source masquerading as a proof.

Step 1 cites the actual statement of lem-sfb-profinite-invariants-filtered-continuity. It quantifies over an arbitrary profinite group, an arbitrary condensed commutative ring, every small filtered diagram and every nonnegative q, and states that forgetting creates the sheaf colimit. In particular it states that the legs are those induced by the actual coprojections. These are precisely the hypotheses and normalization needed for a_q; no density or uniform bound is smuggled in.

Step 2 cites the exactness sentence of lem-pc-module-filtered-colimits-tensor, which applies to modules over a variable ring sheaf on any small site, hence to internal R-modules on the profinite site. I use no tensor clause. The arrow-colimit identification is written out using equivariance of each coprojection. The statement of lem-sfb-arrow-exact-colimits requires an abelian category, colimits of the given shape and finite-limit preservation of that colimit functor; filtered exactness in these module sheaves provides these hypotheses. Its conclusion explicitly preserves the canonical cocone legs. Reading def-weil-abstract-derived-category confirms that cohomology after localization is exactly complex cohomology. The only remaining calculation is the displayed kernel in degree 0, cokernel in degree 1 and zero elsewhere. This does not assume that evaluation on an arbitrary profinite parameter is exact.

Step 3 uses lem-sfb-condensed-derived-invariant-bar only for its statement that ordinary invariants on M[0] are represented by a bar totalization with compatible nonnegative resolutions. The resolution degrees and bar degrees are both nonnegative, so there is no negative total degree. This is a direct degree check, not an assertion that underived continuous cochains are acyclic. It applies independently to every N_i and N.

Step 4 uses lem-sfb-relative-cyclic-restriction-model exactly as a natural comparison: it explicitly states that beta is a natural transformation and lambda is a natural isomorphism, and defines c by their composite, with G=1 allowed. I expanded the inverse-naturality calculation and then precomposed with every coprojection. The leg equations for a_q and b_q give the equality before invoking colimit uniqueness. Thus no arbitrary abstract isomorphism is substituted for the specified comparisons.

Step 5 first gives an elementary reason why a colimit of the natural stagewise isomorphisms is invertible: the component inverses are natural and their inverse equations remain equations under the colimit functor. The preceding square then identifies H^q(c_N) with a composite of three isomorphisms. The cited lem-weil-pbc-unbounded-derived-iso-cohomology quantifies over every abelian category and every derived morphism, so it applies to the full ordinary internal module category, without geometric points, discreteness, or boundedness requirements. Its statement supplies the exact final detection implication.

Small cases checked: the zero ring and zero modules give zero comparisons throughout; a singleton index gives the usual naturality square and identities for both continuity maps; nonmonic transition maps are allowed by the exact-colimit statements; a filtered category with parallel arrows is allowed (no replacement by a directed poset); H trivial and u zero produce the differential zero without affecting kernel/cokernel continuity. The statement only concludes closure when every c_{N_i} is invertible; it does not assert that every comparison is invertible (for example H trivial need not make the two-term comparison invertible for a nonzero trivial module). In q<0 all four corner objects are zero; in q>1 the cyclic side is zero but the derived invariant side is not presumed zero before the final additional hypothesis.

The generic off-unit tools are declared in split_report.tool_uses: filtered exactness of module-sheaf colimits, arrow kernel/cokernel preservation, the derived-category definition, and the cohomology isomorphism criterion. They do not replace a unit step with another mathematical route. Every proof step is below 2000 characters. No proof text is hidden in a statement-only successor; there are none. All citation quotes were checked as literal substrings of the current cited statements. No compiler, Lake, local DAG checker, repository write or git command was used.

## Unfinished

Nothing mathematical remains in this one-level split. The existing unsplit descendants of cited nodes remain their own items. Required server dry-run and delivery results are recorded below when available.
