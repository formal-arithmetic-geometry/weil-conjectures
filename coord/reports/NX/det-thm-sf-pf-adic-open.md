# Worker report: det-thm-sf-pf-adic-open

## Files written

- `dag/nodes/sec-six-functors-basics/det-thm-sf-pf-adic-open.json`: statement node, status split; no Mathlib match for this integral completed-coefficient open-direct-image theorem. The existing statement, Lean audit, source, ancestry, import flags, search records and first four proof steps are retained. Former step 5 is replaced by six short steps; the conclusion is renumbered to step 11.
- `citations.json`: one verbatim statement excerpt for each of the 22 step/node citations.
- `report.md`: this report and review. Sandbox-local scripts in `work/` only generate these artifacts; they are not delivered as project files.

New nodes: **0**. New Mathlib leaves: **0**. The non-elementary hidden arguments are already statements of existing nodes; making new nodes would duplicate them.

## Attachments

None. Searched the whole `WeilConjectures/` source tree for the exact blueprint id and the open-direct-image/constructibility terms. No declaration states this entire completed-integral theorem without sorry. The related finite étale theorem `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion` at `WeilConjectures/SixFunctors/Etale/Derived/Finiteness/DirectImage.lean:86` has `sorry` at line 93 and supplies only finite étale coefficients, so it is not an attachment. `AlgebraicGeometry.ProEtale.lowerStarCompSheafComposeRestrictScalarsIso`, `SixFunctors/ProEtale/ScalarExtension.lean:59`, is an underived constant-coefficient comparison and does not prove the item's completed integral derived assertion.

## WANTED

No additional document is needed for this repair. General coefficient-change arguments are covered by existing nodes with available Stacks sources. The inherited DVR node notes that Serre, Local Fields, Ch. II, §2, Proposition 3 is not obtained; this repair uses its stated DVR theorem as a black box and creates no local-field node.

## What was wrong and what changed

This is the human-requested 2026-10-17 re-split recorded in `coord/repair-notes/det-thm-sf-pf-adic-open.json`: former step 5 (2125 characters) hid several arguments. The statement was specifically to remain unchanged, and it does. The current sandbox originally matched the repository exactly and had neither report nor new nodes. The required initial dry run exited with the diagnostic that `report.md` was absent or lacked `## Review by NX`.

The repaired former step 5 is now:

1. Step 5 checks quasi-separatedness of an open immersion from its diagonal and the definition of quasi-compactness.
2. Step 6 applies the existing qcqs étale/pro-étale derived comparison and the constructible derived equivalence at the residue coefficients.
3. Step 7 cites `sk-prop-sfb-cartesian-coefficients` for both inverse-image coefficient isomorphisms, `sk-def-sfb-coefficient-change` for the **stated commuting square**, and `lem-weil-pbc-ring-sheaf-change-adjunction` for the **stated derived direct-image scalar-restriction comparison**. The latter already contains the equal-ringed-topos-composites argument; it is no longer proved inside the item.
4. Step 8 cites `lem-weil-restriction-of-scalars-exact` and takes cohomology of the comparison in the ambient integral derived category.
5. Step 9 gives the elementary section calculation: lift a residue section locally along the coefficient epimorphism and compute `h(bm)=h(am)=a h(m)=b h(m)`. This is the whole argument for residue-linearity, including its inverse. It does not claim that scalar restriction is fully faithful on derived categories.
6. Step 10 applies the constructible derived equivalence to the actual reduction, giving its étale origin after its residue-coefficient cohomology has been checked.

The original completeness, all-level canonical reduction and finite-coefficient finiteness route are preserved. Original steps 1-4 are identical, and the conclusion changes only its reference from step 5 to step 10. Every step is under 2000 characters (largest 1514).

The inherited unit record is stale: `dag/units/sk-thm-sf-pf-adic.json` describes the old derived-complete projection-formula unit in `sec-six-functors`, whereas the current main-20261015 chapter and unit source describe open direct image and projection formula in `sec-six-functors-basics`. I read both and follow the current source. This is maintainer-owned metadata; the delivery does not edit it. All off-unit theorem uses are explicitly declared in `split_report.tool_uses` as generic tools serving the same source route.

There is no new STATEMENT-DISPUTED correction in this delivery. The previous split made the standing scheme and coefficient hypotheses explicit, and those exact words are preserved here. The inherited source tags are not all theorem tags: 099R and 09AI are section tags, and 09C1 defines the Stacks constant-coefficient category. I checked the actual source passages and the stronger, explicit existing node statements rather than treating these tags as complete theorem citations.

## Not duplicates

No new nodes. Before deciding this, searched all DAG statements for restriction of scalars with exactness/direct-image terms, ran `tools/blueprint_refs.py search 'restriction of scalars'`, `search 'quotient'`, and `search 'direct-image'`, and read the candidate statements. The search of the imported blueprint gives the item as its own nearest ancestor. It found no other blueprint node stating the item's entire completed-integral assertion, so its `same_as` remains empty.

Important candidates checked:

- `lem-weil-pbc-ring-sheaf-change-adjunction` covers arbitrary compatible ring sheaves and already states exactly the direct-image comparison used in step 7, including exact scalar restriction. It is reused.
- `lem-weil-restriction-of-scalars-exact` covers the exact completed-integral-to-finite reduction used in step 8. It is reused.
- `lem-weil-proetale-direct-image-restriction-of-scalars` assumes both coefficient rings are finite. It cannot be applied to the completed integral coefficient ring here.
- `def-sfb-derived-comap-lower-star-iso` and `lem-weil-pbc-flat-ringed-diagram-restriction` require flat scalar extension. The residue quotient is not flat over the integral DVR, so neither is substituted for the ring-sheaf-change lemma.

The sandbox's existing `searches.jsonl` was read and retained. Its six prior queries returned restriction-of-scalars definitions and underived pushforward identities, not the needed completed-coefficient derived comparison. No prior query is fabricated or reissued, no Mathlib search record is added, and all inherited item search records remain unchanged.

## What could not be finished

Nothing mathematical remains in this one-level split. The existing unsplit dependencies remain separate stage-1 items. The stale unit binding noted above remains for maintenance.

## Review by NX

I read the current main-20261015 item statement and all four paragraphs of `sk-thm-sf-pf-adic-open.proof.md`, the current unit `_section.md`, the chapter record and its current text, the old unit record, and the repair note. The statement retains the separated finite-type positive-characteristic setting with distinct residue coefficient prime, the completed coefficient sheaves, the canonical reduction arrow, derived completeness, bounded constructibility and finite Tor amplitude. The repaired steps implement the same completeness/reduction/finite-coefficient-finiteness/residue-criterion route. No SGA source is used.

I opened the statement of every cited node; `citations.json` records the exact parts used. In steps 1 and 11, `sk-lem-integral-models` explicitly gives both the if-and-only-if residue criterion for completed coefficients and the equality with the finite-Tor category. Step 1 also uses the **statement** of `lem-weil-l-adic-extension-integers-dvr`: PID, nonzero maximal ideal and finite residue field. Its characteristic calculation is elementary from the extending absolute value and the prime ell; since p differs from ell, ell is invertible in the field k.

For step 2, I checked that `det-pe-derived-nakayama-resolution` concerns completed coefficient sheaves, not the discrete constant integral sheaf, and gives the sheaf resolution and cone; `lem-pc-right-derived-functor-triangulated` gives preservation of triangles, and `sk-def-sfb-module-derived-pushpull` is genuinely the right derivation of the module direct-image composite. Importantly, these alone would give only a cone comparison. The canonical all-level projection-formula map and transition compatibility are instead explicitly asserted by `prop-weil-pbc-direct-image-limits`. Its hypotheses require finite perfect quotients, which `lem-weil-pbc-standard-quotients-perfect` states for every power of a uniformizer, and the tower conventions in `def-weil-pbc-adic-coefficient-datum` use completed coefficient modules. I read those statements and the Stacks `sites-cohomology.tex` lemma `lemma-Rf-commutes-with-Rlim` (Tag 0A07, lines 5150 ff.) to check the derived-limit route. In step 3 the direct-image-limits node states not merely an inverse-limit isomorphism but the completion-unit identification; thus the canonical map, not an arbitrary tower identification, is used. `sk-def-pe-derived-completion` defines precisely this canonical map.

In step 4, the field P_1 is finite and discrete, hence Noetherian, and the standing schemes U and X are qcqs. `sk-thm-pe-constructible-comparison` really states the bounded constructible **derived** equivalence, not merely a sheaf equivalence. `cor-fin-deligne-open-finite-coefficients` really states finiteness for an open immersion of finite-type schemes over an arbitrary field and a finite ring killed by an integer invertible in that field. I read its source file in the older blueprint and its finite-coefficient devissage. The integer is ell here; properness is not assumed or used.

Step 5 is now a complete elementary check: under the open-immersion definition, U times_X U is U, its diagonal is the identity, and the inverse image of each affine open is affine, giving quasi-compactness. The open-immersion and finite-type-morphism definition nodes say the facts being unpacked. Step 6 therefore meets the qcqs and bounded-below hypotheses of `prop-weil-pbc-comparison-direct-image`; the displayed comparison is its statement in the opposite direction. `sk-thm-pe-constructible-comparison` transports the finite étale finiteness conclusion back to the residue pro-étale category.

For step 7, I read the coefficient-change and Cartesian-coefficient source units under main-20261015 and checked their node statements. Cartesian coefficients supply the two **ring isomorphisms** required by `lem-weil-pbc-ring-sheaf-change-adjunction`; the coefficient-change node supplies their **compatibility square**, so no naturality argument is hidden. I read that general lemma's whole statement and the available source it cites: Stacks `sites-cohomology.tex`, Tag 0D6D (`lemma-derived-pullback-composition`, lines 3657 ff.), Tag 07A6 (`lemma-adjoint`, lines 3989 ff.), and Tag 0D6E (`lemma-derived-pushforward-composition`, lines 4010 ff.). In particular composition of derived direct image holds for morphisms of ringed topoi without a flatness hypothesis. The two equal ringed-topos composites and their canonical comparison are already in the reused lemma's statement; the item just applies it to the specified ring maps. I checked that this node does not depend on the item, directly or transitively in the delivery's graph check.

For step 8, I read the exactness node and its source `lem-weil-restriction-of-scalars-exact.md`: its target is modules over the completed coefficient sheaf. Exactness makes cohomology after restriction equal to restriction of cohomology. This avoids the incorrect inference that every derived integral-linear isomorphism automatically lifts to the residue derived category. Step 9 needs only the quotient epimorphism already given by the resolution in step 2. The local lifting computation in the proof proves residue-linearity on cohomology, including the inverse, so boundedness and constructibility follow with their actual residue actions. Step 10 uses the existing derived constructible equivalence again to supply étale origin for this actual reduction. Step 11 then has both residue-criterion hypotheses with no extra assumption.

I tested the repaired argument on the identity immersion, the empty source, zero complexes, and complexes with uniformizer torsion; nothing presumes flatness of the input K or of the residue field over the integral ring. For example over the DVR Z_ell, the residue quotient is nonflat, explaining why the flat coefficient-change candidate was rejected, while the equal-ringed-topos-composites comparison still applies. The local lifting argument is valid for sheaf epimorphisms, without assuming surjectivity on sections over every object. No smallness assumption is enlarged: all derived operations refer to the same small pro-étale sites and universe conventions of their cited nodes.

Against delivery-errors B-E: there are no new statement-only nodes or elementary-node duplicates; all notions and theorem dependencies remain named, TeX is singly escaped in decoded strings, all step citations were read in their own statements and quoted verbatim, no clause of the item is moved into a new node, no change of route or of coefficient categories is made, and the lengthy hidden comparison has been replaced with existing theorem applications. The only remaining uncited local calculation (step 9) is explicitly elementary and written out. The repair changes mathematical content in the proof, not merely its line breaks. No Lean files, compilers, Lake tools, live project files or launcher files were written or run.
