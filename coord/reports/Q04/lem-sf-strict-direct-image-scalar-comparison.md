# Q04 stage-1 delivery: lem-sf-strict-direct-image-scalar-comparison

## Files written

- dag/nodes/sec-smooth-purity/lem-sf-strict-direct-image-scalar-comparison.json: statement, split into eight proof steps; no exact Mathlib match.
- citations.json: 30 entries, one for every step/node citation, with verbatim excerpts of the live cited statements.
- searches.jsonl: six searches executed through the prescribed msearch.py command; their results were read and the new records added to the item's existing searches.
- report.md: this report. write_split.py is a sandbox-only generation aid, not a delivery file.

No new nodes; zero new Mathlib leaves. The statement and its statement dependencies are unchanged. No chapter or unit realization fields are changed: this item is a supporting node, not the unit's key statement.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for strict towers, scalar/direct-image comparisons and their possible declaration names. The hits in CoefficientChange and RestrictScalarsLowerStar concern finite constant coefficients and restriction of scalars. NormalizedTower and AdicSystem concern realization, rather than the whole normalized scalar comparison and cocycle of this item. No declaration found there states every clause. The existing Sheaf/Paper/SfScalarExtensionComposition normalization was read as supporting reference, not treated as an upstream attachment.

## WANTED

None. The blueprint and all Stacks sources used below are locally available. No SGA source is used. The old unit record mentions SGA, but that paragraph is not a source or proof citation in this delivery.

## Problems found and corrections

The item was statement-only, so there was no proof to preserve. Its existing source locates the rational and algebraically closed paragraphs of prop-sf-closed-unit-all-stages, whose assertion that direct image commutes with scalar extension does not by itself identify the chosen strict-tower maps. The split supplies the explicit conjugation formula and its cocycle calculation. No statement dispute or statement correction is needed.

The direct-image constructibility and scalar extension assertions are used on their actual full derived-complete integral categories. We do not replace these categories by finite-level categories or identify them with a different constant-coefficient category. We do not infer equality of derived maps just from their individual reduction projections.

I retained the imported Mathlib-search records and added only searches really performed in this sandbox. The two semantic phrasings returned cotangent-complex functoriality and ordinary algebraic adic-completion maps. LeanSearch returned scalar-tower instances and adic-completion scalar equations. Loogle returned general linear functors, including linear_of_iso. These are useful formal patterns, but none states the item, and no Mathlib leaf is asserted. The grep hits in ElladicCohomology and Proetale were read: they construct the site and coefficient sheaf/cohomology, without the specified completed direct-image comparison.

## Not duplicates

No new nodes are created. Whole-DAG and whole-blueprint searches for strict-tower, scalar comparison and scalar/direct-image compatibility found existing tools and no exact replacement for this item. In particular, prop-weil-pbc-scalar-extension concerns the ambient ringed direct image; lem-fix-scalar-completion-associator concerns the scalar functors; lem-pur-completed-line-tensor-coherence concerns line tensor functors; none alone states the direct-image comparison normalized by psi and chi.

## Review by Q04

I read the current main-20261015 prop-sf-closed-unit-all-stages proof, especially its rational-stage and algebraically closed-stage paragraphs, the current scalar-extension and scalar-composition proof files, and the operation-reduction paragraph specifying transport to field stages. I also read Stacks sites-cohomology.tex, Tag 0D6E (lemma-derived-pushforward-composition) and Tag 0A07 (lemma-Rf-commutes-with-Rlim), algebraization.tex Tags 099B and 0A0E (lemma-derived-completion and lemma-derived-completion-koszul), derived.tex Tag 070I (lemma-K-injective), and the K-injective shift observation. Bhatt--Scholze Proposition 6.8.14 and Remark 6.8.15 were read for the field-stage and ordinary-derived-operation context. The proof is marked agent-origin because the actual conjugation calculation is an explicit refinement of the blueprint, rather than a claim that the source wrote these eight steps.

Step 1 cites the finite-type algebra Noetherian theorem and finite-type dimension theorem, so the Noetherian and finite-dimensional hypotheses of the ambient scalar proposition are supplied. A finite affine cover exists by finite type; the field is Noetherian since its only ideals are zero and the unit ideal. Invertibility of ell passes through the structure maps. I checked the full statements of integral direct-image constructibility, strict functorial direct-image composition, completed-coefficient pushforward comparison, and integral scalar constructibility. They supply bounded constructible values, an actual natural reconstruction comparison on strict diagrams, and the required scalar functor domains. The completed pushforward node retains an auxiliary prime p distinct from ell; one may choose any such prime, independently of char(k). Its statement puts no condition on char(k), so it applies also in characteristic zero. No finite-field hypothesis is introduced here.

Step 2 uses precisely the ambient direct-image A-linearity stated by lem-sbc-completed-operations-linear-natural-exchange and the constant-section action stated by lem-weil-integral-constructible-linear. Naturality conjugates the map on Hom groups; bilinearity then gives both additivity and scalar compatibility. The displayed equation at a scalar identity checks the actual psi. No new linearity theorem is hidden in a definition citation.

Step 3 uses the ambient comparison in prop-weil-pbc-scalar-extension in the inverse direction, and the isomorphism/naturality clause of lem-weil-finite-free-completed-scalar-comparison. I checked each source and target of the formula: I_L S_Z goes through F_L S_Z, F_L C_Z, C_X F_E, S_X F_E, and S_X I_E. Every inverse is on a complete object. Step 1 guarantees all intermediate constructible restrictions. This is the actual chosen comparison, not an arbitrary isomorphism between endpoint objects.

Step 4 uses the explicit normalization equation in lem-fix-scalar-completion-associator and the explicit identification of its rationalization with the prescribed scalar associator in lem-pur-completed-line-tensor-coherence. The latter identification matters: the bare existence assertion of lem-weil-scalar-extension-composition would not identify chi-normalized associators. I read all three statements and the corresponding existing normalization equation in SfScalarExtensionComposition. After precomposition by F_M(h_Z), the ordinary ambient cocycle is exactly the equation written in the step. It is well typed from F_M C_b^Z C_a^Z to C_c^X F_E. Naturality moves the intermediate chi maps, their inverses cancel, and h_Z is invertible. The repeated-field calculation uses the completeness unit, not a false literal equality of the raw completed scalar functor with the identity.

Step 5 is elementary assembly of the maps already constructed: expand both d's, cancel S_b(psi_L inverse) with S_b(psi_L), apply Step 4 and then the written naturality equation of psi_M. It cites no further node. This calculation supplies the integral cocycle before any rationalization and checks the actual unit normalization.

Step 6 checks the native shifts by the full augmentation formula of lem-trf-completion-unit-strict-quotient-model and the zero-coordinate criterion of lem-weil-roos-comm-shift. I checked that both statements are for arbitrary schemes and impose no finite-field or boundedness hypothesis. The completed-coefficient and tower-limit nodes identify the comparison as derived composition, and the ringed-topos composition node supplies the representative g_*j. The K-injective shift node supplies the shifted resolutions. The equality g_*(j[r])=(g_*j)[r] is simply termwise reindexing of that same chain map; it is not an appeal to equality on evaluated tower arrows. Thus the entire normalized comparison commutes with shifts. This uses existing generic representative formulas and does not need a new comparison lemma.

Step 7 cites the exact ordinary-tensor/chi/native-cone shift equation in lem-weil-completed-scalar-chain-shift, the ambient shift clause of the scalar proposition, and the general composition/whiskering shift calculus. Inverting a shift square and composing the already supplied squares is a formal cancellation argument. No assertion about finite-Tor-amplitude objects or proper morphisms is used to cover arbitrary bounded constructible inputs.

Step 8 uses the full semilinear-localization statement, which explicitly preserves natural transformations, isomorphisms, compositions, whiskering and all well-typed equations. The integral DVR statement and the coefficient inclusion give t_E=u t_L^e, so the inverted-element condition is satisfied, including ramified extensions. The scalar functor's semilinearity is supplied by integral scalar constructibility, and direct-image linearity was proved in Step 2. The localization is raw, with the same objects and tensor-localized Hom groups as the rationalization definition says. Therefore it preserves the already proved unit and cocycle equations, and no Karoubi envelope or full-faithfulness assertion is introduced.

I checked B--E against the files and sources: there are no new nodes to duplicate, no new statement containing a proof sketch, no clause relabelled as a new lemma, and no extra hypotheses. Every cited step/node pair has a verbatim statement excerpt in citations.json, generated only after opening that statement. The proof dependencies are precisely the union of step uses; the statement dependencies remain those used in the unchanged statement. Off-unit generic tools are explicitly declared in split_report.tool_uses for maintainer review; I do not set the maintainer-owned tool_uses field. All steps are under 2000 characters; each is a single restriction, representative calculation, or conjugation argument. Small cases checked: the zero complex, empty schemes, identity f, E=L, repeated adjacent fields, ramified E inside L, and a negative shift. Zero and empty cases give zero maps as required; identity extensions use the specified completeness/multiplication units; ramification changes e but preserves localization; shifts retain the zero cocone coordinate. There is no claimed full faithfulness for a general f.

## Unfinished work

None in the authorized stage-1 split. No Lean files were written, no compiler or Lake command was run, and all writes were confined to this item's sandbox. Server dry-run results and delivery status are recorded below once available.
