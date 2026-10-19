# Stage-1 report: lem-trf-unbounded-direct-image-section-presheaf

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-unbounded-direct-image-section-presheaf.json`: statement, split; no Mathlib match. Five proof steps, with existing dependencies only. The statement and its statement dependencies are unchanged.
- No new nodes; no Mathlib leaves.
- Sandbox evidence: `citations.json` contains a verbatim statement quotation for every step/dependency pair; `searches.jsonl` contains this run's actual Mathlib searches. The sandbox script `write_split.py` was used to prepare the initial JSON; the final JSON includes subsequent self-review repairs and is authoritative.

## Attachments

None. Searched the read-only slopmaster2 project's `WeilConjectures/` for the item id and blueprint tag, `hypercohomology`, `cohomologyPresheaf`, `describeHigherDirectImages`, and unbounded direct-image descriptions. The relevant project hits in `SixFunctors/Etale/SmoothBaseChange/HigherDirectImage/CohomologyPresheaf.lean` concern bounded-below etale complexes. They do not state this arbitrary-ringed-space unbounded result. No attachment is claimed. The exact upstream master remains reference material, not evidence of a finished proof.

## WANTED

None. All sources used were present locally.

## What changed and what was wrong

The item had a complete source-faithful statement but no proof. I retained every clause, including the comparison of full presheaves, arbitrary integer degrees, naturality, and the absence of boundedness or scheme hypotheses. I supplied the local Leray argument underlying Stacks 0D5X and then its sheafification step. The naturality detail is an agent-written expansion using one functorial global comparison, rather than independently chosen isomorphisms for each open. Accordingly `proof_origin.by` is `agent` and names the source argument expanded.

The open-restriction, resolution, acyclicity and sheafification tools already exist. No new statement-only node is needed. The nearest existing Leray/global-sections nodes for schemes cannot be applied as if they asserted arbitrary ringed-space results. I instead use `lem-pc-ringed-space-direct-image-kinjective-acyclic`, whose statement explicitly covers ringed spaces and does not assume the direct image itself K-injective. The full presheaf identification is proved in the steps, not transferred to a newly created copy of the item's clauses.

During self-review I replaced an uncited stalk justification for restriction preserving quasi-isomorphisms with the explicit exact-restriction theorem. I also expanded the right-derived-unit naturality equation: this shows precisely why acyclicity applies to the chosen resolution map after restriction. No source error or statement dispute was found. There are no Lean changes or compiles.

## Searches and blueprint

Read `SETUP.md`'s three-level route, the chapter `sec-trace-formula` and unit `sk-i-curve-zero`, and the main-20261015 ancestor proof `lem-trf-local-term-locality.proof.md`. Preserved the inherited supporting BBD-descent ancestry through `lem-trf-derived-basis-local-ext-sheaf` and the existing precise `blueprint.from.place`. This auxiliary lemma does not replace the unit's contracting-correspondence argument. `blueprint.same_as` remains empty: whole-DAG searches for tags 0D5X/0D5W, sheafification/cohomology, and ringed-space direct-image composition, and `blueprint_refs.py search` for `Leray`, `Leray unbounded`, `higher direct image`, `unbounded direct image`, `local hypercohomology`, `sheafification of`, and `K-injective` found no blueprint statement of the same scope. The ancestor command confirms `lem-trf-local-term-locality`.

Ran the prescribed msearch command for LeanFinder, LeanSearch, Loogle and grep, then repeated the concept using a second LeanFinder phrasing, Loogle `"cohomologyPresheaf"`, and a second grep directory. All services responded successfully. Read Mathlib `CategoryTheory/Sites/SheafCohomology/Basic.lean` lines 56–86: its `H`, `cohomologyPresheafFunctor` and `cohomologyPresheaf` concern nonnegative Ext of single abelian sheaves. Read `Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean` lines 39–49: `SheafOfModules.pushforward` is underived. The semantic hits on sheafification/pullback compatibility and derived homology factorization do not assert the item's local unbounded direct-image comparison. No exact or one-line generalized match was found. Existing Q43 search history is retained, with this run's actual records appended.

## Not duplicates

No new nodes. Reused the existing ringed-space sheafification theorem, exact restriction theorem, K-injective restriction theorem, and direct-image acyclicity theorem. The scheme-only global Leray and sections-pushforward statements were read and deliberately not used outside their hypotheses.

## Review by Q79

I read locally Stacks `cohomology.tex` Tag 0D5X (`lemma-unbounded-describe-higher-direct-images`), the complete proof and preceding Tag 0D5W (`lemma-Leray-unbounded`), Tag 0BKJ (`lemma-sheafification-cohomology`), Tag 08BS (`lemma-restrict-K-injective-to-open`), Tag 08FE (`lemma-restrict-direct-image-open`), and the unbounded construction and composition/adjunction discussion, Tags 0D5S/0D5T. I also read `derived.tex` Tag 070I (`lemma-K-injective`) and `injectives.tex` Tag 079P (`theorem-K-injective-embedding-grothendieck`). These give the item's unrestricted ringed-space statement, not only a qcqs scheme specialization. No new-node sources require review.

Step 1 uses the actual statement of `prop-pur-kinjective-resolutions-exist`: it gives functorial resolutions on small ringed sites. The sites of opens are sets in the stipulated universe, and the structure sheaves are commutative ring sheaves, as required. `def-pc-ringed-spaces-derived-direct-image` expressly says that direct image is evaluation on inverse-image opens and is represented by direct image of any K-injective resolution. These statements give I, B, J, and both cohomology computations. The degreewise identity of their sections complexes is simply that definition, including scalar actions.

Step 2 uses `lem-sc-derived-k-injective-restrict-open` for both I on X and J on Y; both are K-injective and U,V are opens. `lem-sc-derived-open-restriction-adjunction-exact` explicitly states exactness of module restriction on arbitrary ringed spaces, so restriction preserves the quasi-isomorphism r. `def-pc-ringed-spaces-derived-direct-image` supplies the section formula identifying B restricted to V with the direct image under f_V. No naturality or exactness is borrowed merely from a definition that lacks it.

Step 3 uses the statement of `lem-pc-ringed-space-direct-image-kinjective-acyclic`, with f=f_V, g=a_V and input I restricted to U. These are morphisms of ringed spaces; no local-ring, flatness, scheme, or K-injectivity-of-B hypothesis is introduced. Its conclusion is invertibility of the derived unit, exactly what the step needs. `def-sfb-right-derived-functor` supplies the natural unit and its invertibility on K-injectives. The written equation with r restricted to V proves invertibility of the actual evaluated comparison, rather than silently assuming it. Identifying sheaves on the one-point target with modules is direct from their values on its two opens; the scalar-forgetting argument is just the formula for module kernels and images. This verifies C4 for the critical acyclicity citation.

Step 4 uses functoriality from the resolution theorem, the K-injective Hom bijection and homotopy-equivalence consequence from `lem-weil-pbc-kinjective-hom-derived`, the localization universal property from `def-weil-abstract-derived-category`, and the additive termwise construction from `def-pc-ringed-spaces-derived-direct-image`. I checked that these statements actually include the homotopy-equivalence and morphism-comparison assertions, rather than merely full faithfulness on a smaller class of morphisms. The proof writes the commuting restriction square and explains why both presheaf functors invert quasi-isomorphisms. Independence follows from uniqueness of the comparison homotopy classes, with homotopies killed by evaluated cohomology. This is why the result is an isomorphism of presheaves natural in derived objects, not only objectwise group isomorphisms.

Step 5 uses `lem-pc-ringed-space-sheafification-cohomology`, whose statement explicitly concerns arbitrary ringed spaces, all integer q, the same K-injective section cohomology, its underlying abelian sheafification, and naturality in K. Applied to K=Rf_*E it gives exactly the second presheaf's sheafification. Applying sheafification to the already constructed presheaf isomorphism gives the first. No sheafification-exactness or forgetful-exactness theorem is being inferred from a definition. Every cited statement was opened, and `citations.json` copies it verbatim. The five off-unit generic tools are declared individually in `split_report.tool_uses`; the remaining cited objects are definitions or the existing Mathlib leaf.

I checked B–E point by point: no new-node schema, hidden proof in a new statement, unsearched leaf, duplicate, or restated clause; no citation relies on a dependency's proof rather than its statement; no new independent comparison lemma is hidden in a long step. All five steps are shorter than 2000 characters. Small cases checked were E=0, f=id, q negative (no boundedness truncation was used), the empty open V (both section complexes vanish, and its one-point target has the zero ring), arbitrary non-flat structure maps, and unbounded I. In particular the proof never says f_*I is K-injective. The zero-ring point is permitted for ringed spaces. No change to the chapter or unit records or route was required.

## What remains

Nothing in the requested split. The existing dependency nodes retain their own proof status. Final validation and direct delivery are performed with the prescribed delivery tool; its output determines the final response.
