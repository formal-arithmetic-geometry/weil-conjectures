# Q91 stage-1 report: lem-pur-site-comparison-edge-section

## Files written

- lem-pur-site-comparison-edge-section.json: the existing statement, now split into four proof steps; no new nodes and no Mathlib leaves.
- citations.json: verbatim statement excerpts for every node cited by each step.

## Attachments

None. Searches of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact item id, edge sections, Leray, and comparison cohomology found no declaration stating every clause. LowerStarAcyclic.lean has a global-cohomology vanishing comparison, and UpperLowerStar/EdgeMap.lean concerns the other Leray edge map H^n(V,u_*F) -> H^n(U,F); neither states this item. Master sorry declarations are not used as completed proofs.

## WANTED

None. The current blueprint and local Stacks sources supply the route.

## What I checked and corrected

Resumed the saved item, report and citations, compared the item against the current repository, and first ran the required delivery dry run. It exited successfully with OK (not pushed) at 0946d1c948. That mechanical success did not settle the mathematical reading: the saved proof attributed an unspecified chain map to the canonical-mate node and silently chose resolution replacements. I repaired those points before delivery.

The statement is unchanged. All inherited Mathlib searches and their actual results are retained: the search question has not changed, and those entries already occur in the repository item. There is no item-local searches.jsonl in this resumed sandbox, so I have not invented or reconstructed a search log. The reported hits concern sheaf cohomology functors, sheaf-section naturality, and site constructions; none gives this etale/pro-etale edge compatibility. The unavailable LeanSearch result remains unavailable. A fresh whole-blueprint search for “edge section” returned zero blueprint nodes. No new statement was created, so there is no new-node duplicate or Mathlib-leaf claim.

The historical source-place reference to “returned Step 13” is not a numbered step of the current three-step blueprint proof. I read the actual opening transport paragraph and the current parent node: its Step 15 invokes this item to identify the pro-etale Kummer edge section. The blueprint from.place and split_report now record that precise current use while retaining the historical ancestry.

## Review by Q91

I read literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/prop-pur-gm-relative-kummer.proof.md, especially the opening comparison paragraph. I also read Stacks Tag 099W (proetale.tex, lemma-compare-cohomology), Tag 072W (sites-cohomology.tex, lemma-higher-direct-images), and Tag 079P (injectives.tex, theorem-K-injective-embedding-grothendieck). The first two supply supporting comparison and cocycle-to-cohomology-sheaf conventions; neither is falsely described as verbatim stating the compatibility proved here. The proof is therefore marked agent-written. No SGA source is used.

Step 1 now cites prop-pur-kinjective-resolutions-exist for actual K-injective replacements I and A_U I -> J on the two ringed sites. It applies to module sheaves over a commutative constant ring; the sites are small in the project's chosen larger universe. Exactness from lem-sf-comparison-pullback-exact makes J a replacement of A_UF. The comparison adjunction definition supplies h:I -> nu_U,*J. The global-comparison node states precisely that c is the derived unit followed by the final-object comparison; the derived-sections node gives that final-object comparison. Thus evaluation of h gives the asserted global chain map. No inverse-image preservation of injectives is assumed.

Step 2 uses the etale module direct-image formula of def-weil-pbc-direct-image, the pro-etale formula in def-weil-pbc-proetale-operations, and restriction evaluation in def-weil-pbc-site-comparison-morphism. These statements really give the equality of right-adjoint composites: at W both are J(W times_V U), including the same restrictions and coefficient action. The definition of adjunction mate gives the unit-counit transposition formulas. The map d is constructed as the adjunct of u_*h; the equality on terminal sections is the defining adjunction calculation, written in the step. This is elementary relative to those definitions.

Step 3 uses the same direct-image definitions only for their explicitly stated K-injective models. On this resumption I expanded its cancellation claim into the actual Hom-bijection calculation, citing the existing def-weil-pbc-composite-adjunction and Mathlib leaf lem-weil-pbc-conjugate-iso-unit-equation. Their statements respectively give the composite Hom bijection and the unique unit-normalized conjugate of the right-adjoint identity. The successive adjuncts are d, k, r(h), h composed with the etale counit, and t composed with its comparison pullback; the final equality follows from the displayed counit naturality and triangle identity. This checks the normalization rather than assuming an arbitrary inverse-image isomorphism agrees with it. It applies the mate formula to d and the canonical inverse-image comparison of lem-weil-pbc-comparison-pullback. Expanding the transpositions gives t composed with A_U of the etale counit composed with a_u inverse; the triangle identity cancels the intervening unit and counit. The canonical-mate node states exactly that transpose and its counit normalization. It is used for that formula, not for an unmentioned resolution construction. Uniqueness under the adjunction identifies Q(d) with the specified b. This is one formal Hom-bijection calculation, with no auxiliary geometric lemma. I also read Stacks Tag 0B65, categories.tex, lemma-transformation-between-functors-and-adjoints, and Tag 0DV0, lemma-compose-counits, against the two added existing interfaces.

Step 4 uses def-weil-derived-cohomology-sheaves for kernel modulo image and functorial cohomology maps, and clause (3) of lem-sf-comparison-pullback-exact for the natural cohomology identification. The edge maps themselves are defined on cocycles in the item's statement. Applying the already constructed chain map sends [z] to [h(z)]; Step 1 gives its global class and Step 3 identifies its derived morphism. This proves the displayed equality. The step is elementary given those earlier calculations and the cited statements.

I checked the finite commutative coefficient ring throughout, F[0] in Dplus, and qcqs u where the canonical-mate isomorphism is invoked. The calculation itself requires no extra separatedness, smoothness, or injectivity-preservation hypothesis. For q=0 it reduces to pullback of sections and the ordinary direct-image comparison. For u=id it reduces to the natural cocycle-to-cohomology-sheaf map. For F=0 both sides vanish; for empty U the resolution complexes can be zero, again giving zero sections. All proof steps are under 2000 characters; Step 3 is the single formal adjunction calculation above and contains no independent subclaim with additional hypotheses. No new node hides a clause, elementary consequence, duplicate, or absent Mathlib search. All uses have verbatim statement quotes in citations.json. Generic tools from other units are declared in split_report.tool_uses; no maintainer-owned tool_uses field was changed.

## What remains

The initial required dry run on this resumption exited OK (not pushed) at 5355ac3520. After expanding Step 3, run the final revised dry run and push with the prescribed delivery tool. No Lean was written or compiled, and no live project file or launcher was changed.
