# Worker report

1. Files written: the unchanged-statement item `dag/nodes/sec-proper-base-change/lem-weil-pbc-realization-adjoint-comparisons.json` (split; four assembly steps, 2003 text characters), and three new statement nodes in that directory:
   - `lem-weil-pbc-realization-restriction-normalizations`: statement, unsplit, no exact Mathlib match; actual coefficient square and the three restriction normalizations (old steps 2–4).
   - `lem-weil-pbc-scalar-normalized-adjunction-square`: statement, unsplit, no exact Mathlib match; the abstract scalar-transpose and unit-triangle argument (old steps 5–6).
   - `lem-weil-pbc-completed-localized-adjunction-square`: statement, unsplit, no exact Mathlib match; specified left-isomorphism and raw-localization transport of a compatible square (old steps 1 and 7).
   Also wrote the mandatory `citations.json`; auxiliary inspection/search files stay in the sandbox. No Lean was written.
2. Attachments: none. The project declaration `WeilConjectures.realization_adjoint_comparisons`, in `lean/Sheaf/Paper/RealizationAdjointComparisons.lean:152`, ends with `sorry`. Searches under `lean/WeilConjectures/` by the item's tag and scalar/adjunction terminology found no theorem stating the full item. The generic `ChangeOfScalarsSquare.lean` constructs comparisons by mates; it does not establish these separately specified derived comparison normalizations. Its constructions are possible implementation tools for later workers, not an attachment.
3. WANTED: none for this extraction. The new statements are agent abstractions of the supplied proof, not assertions that Bhatt–Scholze prints these equations. The inherited report below records its sources and earlier searches without treating its dry runs as validation of this repair.
4. The return asks to spread a 5484-character proof into at least two comparable independent arguments, rather than shorten its text. This delivery creates three unsplit nodes. Their argument allocations are respectively old steps 2–4 (2159 characters), 5–6 (1740), and 1,7 (1585). Every old step is preserved verbatim below, under its owning new node. The new nodes have complete statements but empty proof and proof_deps; their future workers can prove them independently, because none depends on another new node or on the parent item.
5. The item's one-level split is complete. Proofs of the three new nodes are intentionally left to future workers. Server validation follows below; no compiler, Lake, local DAG check, repository git command, or repository write was used.

## Repair of the return

The named sandbox initially contained only dispatcher brief markers, no delivered node, report, citations, or search log. I recovered the live seven-step item and retained the Q27 report from `coord/reports/Q27/`. The required initial dry run failed because the inherited report did not contain `## Review by Q108`. I then performed the substantive re-split requested by the return rather than re-pushing the old delivery. The live item supplies the returned proof with exactly the seven character counts quoted in the return. Its statement, statement dependencies, creation provenance, blueprint ancestry, and Lean record are retained. The new proof is short assembly, and each new node has its own actual Mathlib searches, source, ancestry, and statement-only status.

## Sources and search results

Read GOAL.md, SETUP.md including the three blueprint levels, the worker role, stage 1, brief-stage1, delivery-errors B–E in full, the chapter and proper-base-change unit records, the current item, and the actual Lean theorem/docstring. Read the current `main-20261015` finite-extension blueprint file. The parent remains the realization subargument below its finite-extension ancestor: no change to the projective-line, reduction, or torsion assembly unit route is made.

Read Bhatt–Scholze Remark 6.8.15 in the local PDF. It supplies the ordinary ambient adjunction setting and preservation under the stated finiteness conditions, not the explicit three normalization equations or general category-theoretic abstractions. Read Stacks `sites-cohomology.tex`, Tag 0D6D / `lemma-derived-pullback-composition` (3657–3680), Tag 07A6 / `lemma-adjoint` (3989–4007), and Tag 0D6E / `lemma-derived-pushforward-composition` (4010–4030), as the source of the already existing ring-sheaf-change input. These are the underlying composed derived adjunctions; they are not misquoted as verbatim sources for the extracted lemmas.

For each new node, searched the entire DAG by its prospective id, its notions, and (for the coefficient argument) the tags 07A6, 0D6D, 0D6E. Searched the whole imported blueprint with `blueprint_refs.py` for restriction scalars, realization adjoint, scalar adjunction, localization adjunction, restriction counit, adjunction scalar, adjunction localization, coefficient comparison normalization, scalar unit square, and completion localization comparison. Those blueprint queries returned no equivalent node. Read the strongest likely DAG candidates listed under Not duplicates below. The ancestry command gives `thm-weil-pbc-finite-extension`; each new node's via list includes the item, then its inherited realization and target intermediates.

Every search entry in the new nodes comes from an actual `msearch.py Q108 lem-weil-pbc-realization-adjoint-comparisons` invocation and matches `searches.jsonl`. All three nodes were searched with LeanSearch, Loogle, LeanFinder, and Mathlib grep. The two distinct semantic formulations per node are recorded and their hits were read. All services answered successfully. The inherited searches on the existing item are retained unchanged; they are historical evidence, not new searches claimed for Q108.

Read the candidates in Mathlib `CategoryTheory/Adjunction/Mates.lean:123–157`, `CategoryTheory/Adjunction/Basic.lean:497–520`, `CategoryTheory/Localization/Adjunction.lean:89–131`, and `Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:274–305`. The last is underived; it does not identify the actual continuous ring maps and derived comparison maps. The mate formulas require identifying the chosen transformation as a mate first; the second node establishes that identification from three independent normalization hypotheses. `ofNatIsoLeft` and `localization` supply separate parts of the third node, but do not in one specialization give its specified scalar-comparison square, completion normalization, fraction formulas into B-linear targets, and persistence of both equations. Thus none of the three complete new statements is a Mathlib leaf.

## Review by Q108

I read the item and all cited node statements alongside the source passages. I kept the parent's statement literally unchanged. I checked that the new coefficient node repeats the same finite field extension, characteristic restriction, separated finite-type schemes, Noetherian/finite-dimension/ell-invertibility assumptions, continuous coefficient rings, and actual coefficient isomorphisms. It does not assume properness or that an ambient restriction object is constructible. Its b and d are the derived isomorphisms of the existing ring-sheaf-change statement, not merely isomorphisms from that node's proof. The source c_h is the adjunct of precomposition; localizing that very map supplies the E map. This pins the square rather than choosing a more convenient comparison. The pull and push normalizations are exactly the assertions of the current completed-pull and localized-push statements. Applying the existing adjunct formula to the E counit gives the third equation at arbitrary ambient Z, which is why its quantifier is not restricted to constructible objects.

In new node 2, I checked types of the abstract argument before extracting it. C0 and D0 are full subcategories stable under the two horizontal functors; this is necessary because alpha and beta are available only on integral objects, whereas b, d and the counit at r_D Z must be ambient. The hypothesis on the restricted E counit is explicitly included. The two scalar-unit hypotheses do not already assert the desired horizontal mate property. The scalar transpose of each proposed counit map starts at P Q M and ends at r_D F_D M. Naturality of b moves r_C(beta) across b inverse; the two d factors then cancel, leaving epsilon at r_D F_D M followed by P Q of j_D,M. Naturality of the ambient epsilon makes this j_D,M epsilon_M. The scalar Hom bijection is injective without assuming faithfulness. For the unit, the primed counit transpose of Q'(alpha_N) beta_PN F_C(eta_N) becomes alpha_N F_D(epsilon_PN P eta_N) alpha_N inverse by counit naturality and alpha naturality. It is identity by the triangle identity. This proves the unit equation and checks the inverse convention in the final mate clause.

In new node 3, I checked the direction gamma:P to P-tilde. The transported Hom bijection applies the old transpose to f gamma, so its unit is Q gamma eta and its counit is epsilon gamma inverse. Correspondingly alpha-tilde is alpha F_D(gamma inverse), exactly the parent's completed comparison. The new node assumes linearity of P,Q and F_C,F_D and B-linearity of P',Q', so the naturality equations extend to u/t^n by multiplying the integral equation by t inverse to the n. Its target scalar localization B is a general ring localization, not an unjustified field assumption. Its units/counits and comparison components are specified, and it explicitly uses raw objects without an idempotent completion. The report's preserved old step 7 gives the triangle and naturality argument in full for the future worker.

For assembly step 1, the completed-pull statement says ordinary P K lies in I_T and its actual gamma is invertible. The localized-push statement says ordinary Q M lies in I_U and agrees with the specified direct image. The pro-etale-operations statement supplies the actual ambient derived adjunction. Restriction of its natural unit, counit and Hom bijection to these stable full subcategories is elementary; the step does not derive constructibility from a definition.

For assembly step 2, the new restriction-normalizations statement supplies exactly the three equations and b,d named by the step; its ambient quantifier includes Z=F_T M. I checked that its alpha^o is alpha-comp F_T(gamma), so the gamma direction matches step 1.

For assembly step 3, the scalar-functor statement supplies F_U and F_T left adjoint to exact restrictions on ambient categories. Its other hypotheses are precisely the full-subcategory stability of step 1 and the three formulas of step 2. The new normalized-square statement supplies both horizontal equations and the mate of alpha^o inverse. No right-adjoint mate is assumed in the application.

For assembly step 4, the new transport statement supplies the completed normalized adjunction and the unchanged comparison components on raw objects. The rational-category statement defines those categories with the same objects; rational-transport extends the supplied exact linear operations and their transformations. The scalar-functor statement gives J(u/varpi^n)=varpi inverse to the n times F(u). These identify its generic raw extensions with the actual specified ones. No lattice choice, faithfulness, idempotent completion, or cancellation in an integral Hom group is used. The new node is applied only after step 3 has supplied its two compatibility hypotheses.

Small cases: the coefficient square commutes for h=id by the actual precomposition formula; for an empty scheme every displayed morphism is the unique zero map. Integral objects killed by a power of varpi realize to zero, and both normalizations and comparison equations are still meaningful. In the abstract square, C0 or D0 may be empty, and only the quantified assertions for their objects are used; no essential surjectivity hypothesis is hidden. With all comparison maps identities the formulas reduce to the two original adjunction triangles. For transport gamma=id removes the completion change, and t already invertible makes raw localization trivial. If B is the zero localization the target Hom modules and equations are zero; no assumption t nonzero or regular is needed. None of these cases requires faithfulness of scalar extension.

The return's sole numbered demand is implemented by the three statement-only nodes and the 2003-character assembly. The retained argument below accounts for all seven old steps, including the actual coefficient-map verification, both explicit transpose calculations, ambient-versus-constructible distinction, completion conjugation, and all fraction/triangle calculations. None of the new nodes restates the parent: the first concludes restriction equations but no horizontal mate property; the second assumes those abstract equations without proving the actual coefficient comparison; the third assumes a compatible square and addresses only its two transports. Their separate proof workloads have comparable old-text sizes. Every assembly step is below 2000 characters; no long inline lemma remains. All new statuses are unsplit, with no proof sketch inside their statements and no proof/proof_deps. I checked JSON TeX escaping and every verbatim quotation in citations.json against the currently read statements.

## Not duplicates

lem-weil-pbc-realization-restriction-normalizations vs lem-weil-pbc-ring-sheaf-change-adjunction: the existing general coefficient theorem assumes a commuting square and supplies adjunct compatibility; the new node verifies the actual continuous coefficient square and pins the separately specified scalar comparisons by three simultaneous transposes.

lem-weil-pbc-realization-restriction-normalizations vs lem-weil-pbc-realization-completed-pull: the existing node provides alpha and its localization-unit normalization; the new node combines its actual coefficient map with the independent push normalization and ambient restricted-counit formula, without asserting the parent's horizontal adjunction compatibility.

lem-weil-pbc-realization-restriction-normalizations vs lem-weil-pbc-realization-localized-push: the existing node gives beta and its transpose, not the compatible pull restriction and ambient counit formulas.

lem-weil-pbc-realization-restriction-normalizations vs lem-pur-ringed-coefficient-restriction-counit: that node compares restriction to constant A sheaves with general R sheaves and a possibly noninvertible structural map; this node fixes the adic and continuous E coefficient systems and pins both separately specified scalar comparisons as well as the restricted counit.

lem-weil-pbc-scalar-normalized-adjunction-square vs def-weil-pbc-adjunction-mate: the definition describes a mate from a supplied map; the new theorem proves that a separately supplied beta has that mate property from scalar-unit and ambient counit normalizations.

lem-weil-pbc-scalar-normalized-adjunction-square vs lem-sfb-pasted-mates-counit-normalization: the latter assumes both squares already consist of mates; this node identifies a single supplied square as a mate using vertical scalar adjunction transposes and an ambient restricted-counit condition.

lem-weil-pbc-scalar-normalized-adjunction-square vs lem-sbc-unbounded-exact-adjunction-square: that node is specific to constant towers/evaluation and their K-injective comparisons; the new theorem concerns two arbitrary vertical adjunctions and normalization hypotheses on supplied maps.

lem-weil-pbc-completed-localized-adjunction-square vs lem-sfb-adjunction-localization: that existing Mathlib leaf supplies localized adjunction units and counits; the new statement additionally transports a specified compatible comparison square along a given left isomorphism and into B-linear targets, with exact comparison components and fraction formulas.

lem-weil-pbc-completed-localized-adjunction-square vs prop-weil-pbc-rational-transport: that node extends supplied exact linear functors and transformations, but does not state transported adjunctions, the specified left-isomorphism Hom bijection, or compatibility of both comparison equations.

lem-weil-pbc-completed-localized-adjunction-square vs lem-pbc-normalized-derived-adjunction-transport: the latter transports a universal left-derived pair through equivalences between abelian categories; the new lemma starts with arbitrary linear adjunctions and uses a specified left isomorphism plus raw scalar localization, without derived universal pairs or category equivalences.

lem-weil-pbc-completed-localized-adjunction-square vs lem-sc-localization-nested-adjunction-mate: the latter compares a degreewise complex map to a nested mate under derived presentations; the new lemma concerns raw scalar fractions and the given unit/counit comparison square, not a complex-level map or derived equivalence presentation.

## Current validation

Server check_dag found no introduced finding; review_split returned PASS. The first repaired dry run correctly rejected the too-short pro-etale-operations quote (fewer than 40 characters). I replaced it with the complete ambient derived-adjunction clause, including its Hom bijection, verbatim from the current node. The repaired server dry run exited successfully with `OK (not pushed)` at `c54845f9ad8`, including server preflight. In the final audit I removed two unused statement dependencies from the new coefficient node and expanded the verbatim excerpts to cover every assertion taken from the cited statements. These final text-only changes are revalidated before pushing. Earlier validation quoted in the archived report belongs to the prior delivery only.


## Preserved argument for the new-node workers

The following is the complete pre-repair proof, verbatim, grouped by future work item. These are report notes, not proofs inserted in the unsplit nodes.

### lem-weil-pbc-realization-restriction-normalizations

Old step 2:

Write $r_W$ for ambient restriction of scalars and $j_W:\mathrm{id}\to r_WF_W$ for the scalar-extension unit, for $W=T,U$. The coefficient description gives $E_W=A_W[1/\varpi]$. The current completed-pull statement specifies $c_h:h^{-1}A_U\xrightarrow{\sim}A_T$ as the adjunct of precomposition with $V\times_UT\to V$, and specifies the $E$-coefficient isomorphism as its localization at $\varpi$. These are the actual coefficient maps used by $P$ and $P^E$. The square with $A\to E$ commutes: under the inverse-image/direct-image adjunction its two composites are precomposition of continuous $A$-valued functions followed by the inclusion into $E$, or that inclusion followed by precomposition, which agree. The localization comparison sends $a/\varpi^n$ to the pulled numerator with the same denominator. The coefficient-change theorem therefore applies and supplies
$$b:r_TP^E\xrightarrow{\sim}Pr_U,\qquad d:r_UQ^E\xrightarrow{\sim}Qr_T,$$
with its stated compatibility of adjuncts. All functors here are ambient; in particular $r_WF_WM$ need not be integral constructible.

Old step 3:

In this notation the normalizations of the two specified comparisons say
$$r_T(\alpha_N)\,j_{T,PN}=b_{F_UN}^{-1}P(j_{U,N}),\qquad
r_U(\beta_M)\,j_{U,QM}=d_{F_TM}^{-1}Q(j_{T,M}).$$
The first equation is exactly preservation of the localization unit by the scalar-pull comparison, after removing $\gamma$ as in step 1. The second is exactly the extension/restriction transpose used to define the scalar-push comparison: the map out of $QM$ is $Q(j_{T,M})$, followed by $d^{-1}$. These are equations of derived morphisms, supplied by the cited normalizations; no computation with representatives of derived sections is being assumed.

Old step 4:

For any ambient $E_T$-complex $Z$, apply the coefficient-change adjunct equation to the counit $t=\epsilon^E_Z:P^EQ^EZ\to Z$, whose adjunct is $1_{Q^EZ}$. Its restricted adjunct is $d_Z$. Inverting the ordinary $P\dashv Q$ hom bijection therefore gives
$$r_T(\epsilon^E_Z)b_{Q^EZ}^{-1}=\epsilon_{r_TZ}P(d_Z).$$
This uses the counit of the ambient integral adjunction at $r_TZ$, not a counit whose domain is restricted to constructible integral objects.

### lem-weil-pbc-scalar-normalized-adjunction-square

Old step 5:

Fix integral $M$ and transpose both sides of the desired counit equation along $F_T\dashv r_T$. The transpose of $F_T(\epsilon_M)$ is $j_{T,M}\epsilon_M$ by naturality of $j_T$. Using step 3, naturality of $b$, step 3 again, and step 4 with $Z=F_TM$, the transpose of the other side is
$$\begin{aligned}
r_T(\epsilon^E_{F_TM})\,r_TP^E(\beta_M)\,r_T(\alpha_{QM})\,j_{T,PQM}
&=r_T(\epsilon^E_{F_TM})\,b_{Q^EF_TM}^{-1}P\bigl(r_U(\beta_M)j_{U,QM}\bigr)\\
&=r_T(\epsilon^E_{F_TM})\,b_{Q^EF_TM}^{-1}P(d_{F_TM}^{-1})PQ(j_{T,M})\\
&=\epsilon_{r_TF_TM}PQ(j_{T,M})=j_{T,M}\epsilon_M.
\end{aligned}$$
The final equality is naturality of the ambient counit. Injectivity of the scalar adjunction's hom bijection proves $F_T(\epsilon_M)=\epsilon^E_{F_TM}P^E(\beta_M)\alpha_{QM}$. By the definition of a square mate this identifies $\beta$ as the mate of $\alpha^{-1}$ (the inverse is required by the direction convention in that definition), equivalently the claimed compatibility with the displayed pull isomorphism.

Old step 6:

For integral $N$ put $D_N=Q^E(\alpha_N)\beta_{PN}F_U(\eta_N)$. Transpose it along $P^E\dashv Q^E$. Naturality of $\epsilon^E$, the counit equation of step 5 at $PN$, and naturality of $\alpha$ at $\eta_N$ give
$$\begin{aligned}
\epsilon^E_{P^EF_UN}P^E(D_N)
&=\alpha_N\epsilon^E_{F_TPN}P^E(\beta_{PN})P^EF_U(\eta_N)\\
&=\alpha_NF_T(\epsilon_{PN})\alpha_{QPN}^{-1}P^EF_U(\eta_N)\\
&=\alpha_NF_T\bigl(\epsilon_{PN}P(\eta_N)\bigr)\alpha_N^{-1}=1.
\end{aligned}$$
The last equality is the triangle identity of $P\dashv Q$. The transpose of $\eta^E_{F_UN}$ is also the identity by its triangle identity. Injectivity of the same hom bijection yields $D_N=\eta^E_{F_UN}$. Step 1 now restores the specified completed adjunction in both equations.

### lem-weil-pbc-completed-localized-adjunction-square

Old step 1:

First work with ordinary ambient $P=Lh_A^*$ and $Q=Rh_{*,A}$, and write $P^E=Lh_c^*$, $Q^E=Rh_{c,*}$. The completed-pull comparison gives the actual natural isomorphism $\gamma:P\xrightarrow{\sim}P_h$ on integral objects, and identifies the integral adjunction with $P\dashv Q$ by precisely $\gamma^{-1}$. Under this identification the specified $\alpha$ becomes the ordinary scalar-pull comparison. Thus an equation proved using ordinary $P$, its unit and its counit is the required completed equation after inserting $\gamma$ and $\gamma^{-1}$; adjacent inverse factors cancel. Both $P$ and $Q$ preserve the integral constructible categories by the pull and push statements, so their ambient units and counits restrict to these full subcategories.

Old step 7:

Finally raw rationalization has the same objects and morphisms $u/\varpi^n$. Extend the integral functors, unit and counit by rational transport. Naturality on a fraction is the integral naturality equation multiplied by $\varpi^{-n}$, and the two triangle identities hold because their components are the images of the integral components. Hence these are the localized adjunctions. The realization functors send $u/\varpi^n$ to $\varpi^{-n}F_W(u)$; the same scalar calculation extends naturality of $\alpha$ and $\beta$. Every object of the raw localization is already an integral object, and the components of the two equations are exactly those proved in steps 5 and 6. Consequently both equations hold for the localized adjunctions as well. No choice of rational lattice or passage to an idempotent completion enters this argument.


# Archived prior report (Q27; not validation of this repair)

# Worker report

1. Files written: `dag/nodes/sec-proper-base-change/lem-weil-pbc-realization-adjoint-comparisons.json` (statement, split; no exact Mathlib match), and the required `citations.json`. No new nodes, no Mathlib leaves, no Lean files. The pre-existing mathematical statement, creation provenance, and blueprint ancestry are retained.
2. Attachments: none. Searches of `lean/WeilConjectures/` for the blueprint tag and for scalar/adjunction comparisons found general category theory and finite/field coefficient infrastructure, not a declaration giving all clauses of this item. In particular `CategoryTheory.conjugateEquiv_paste` and the étale `upperStarRestrictScalars` results do not state this continuous-coefficient, completed-integral comparison theorem.
3. WANTED: none.
4. The source citation needs interpretation: Bhatt–Scholze Remark 6.8.15 (printed p. 62) supplies the ambient operations and adjunction but does not itself print these scalar-comparison equations. The proof is therefore explicitly marked agent-written, with the normalized existing DAG statements supplying the non-elementary input. The ordinary mate convention takes a map in the direction opposite to the displayed alpha: beta is the mate of alpha inverse. This is a clarification of the unchanged displayed equations, not a change in their meaning or hypotheses. The raw rational transport node extends supplied data; it does not assert preservation of constructibility. Preservation is taken from the existing pull/push comparison nodes before transport is used.
5. Nothing mathematical remains unfinished in the item's one-level split. Its existing dependencies remain available for their own work. Delivery validation is recorded below.

## Sources and searches

Read `SETUP.md`, `GOAL.md`, the worker role, the stage-1 document, the chapter and unit records, and both occurrences of delivery-errors B–E. Read the current `main-20261015` blueprint file for `thm-weil-pbc-finite-extension`; it states proper base change over finite E. This item's supplied ancestry is the realization/adjunction subargument used in rational transport, not a new replacement for the proper-base-change unit's projective-line/reduction/torsion route. No unit record is changed.

Read Bhatt–Scholze Remark 6.8.15 and the surrounding Proposition 6.8.14. Also read `sites-cohomology.tex`, labels `lemma-derived-pullback-composition` (0D6D), `lemma-adjoint` (07A6), and `lemma-derived-pushforward-composition` (0D6E), the source passages underlying the existing coefficient-change theorem. That theorem's *statement* explicitly gives the adjunct compatibility used here, beyond mere existence of composite isomorphisms.

Read every cited node's complete statement, including the continuous coefficient localization, inverse-image localization normalization, scalar extension, completed pull, localized push, ring-sheaf change adjunction, ambient operations, mate definition, raw rational category, and rational transport. Searched the whole DAG and `blueprint_refs.py` for adjoint/mate comparisons and coefficient-change statements. Reused the existing coefficient-change node and mate definition; no elementary calculation was promoted to a node.

Five searches were run through the required `msearch.py` command and recorded verbatim in the item's `mathlib_searches`, in addition to retaining its inherited searches: LeanFinder on the scalar-comparison formulation, Loogle on `CategoryTheory.Adjunction, "mate"`, grep on `mateEquiv_counit|unit_mateEquiv|localization_unit_app` in CategoryTheory, LeanSearch on extension of scalars and counits, and a second LeanFinder phrasing on ringed-topos change of rings. Read Mathlib `CategoryTheory/Adjunction/Mates.lean`, lines 123–157, and `CategoryTheory/Localization/Adjunction.lean`, lines 88–131. The generic mate identities assume the chosen transformation already is the mate; they do not identify the separately specified alpha and beta here. The module-sheaf hits concern underived adjunctions, and do not supply the completed/continuous coefficient comparison. Consequently the item is not a one-line Mathlib specialization.

## Review by Q27

For step 1 I checked the pull node's actual gamma direction: ordinary pull to completed pull. Its alpha uses gamma inverse, exactly as the item requires. The push node states ordinary direct-image constructibility without properness, so restriction of the ambient adjunction to the full integral categories is legitimate. No generic rational-transport statement is used for this preservation claim.

For step 2 I checked the coefficient hypotheses of the ring-sheaf-change theorem. The finite-extension coefficient node supplies both the adic/continuous A identification and E as sheaf localization of A. The completed-pull node supplies the actual A inverse-image isomorphism for h. The inverse-image/localization coherence node supplies the corresponding localized ring isomorphism and its normalization on sections, so the square with A to E really commutes. These are precisely the two coefficient isomorphisms and compatible maps required by the change-of-rings statement. Scalar extension supplies its ambient adjunction and unit. The b and d comparisons used in the proof are those of the *statement* of the ring-change node, not details borrowed from its proof.

For step 3 I checked each displayed equality against its normalization source. The pull node explicitly preserves localization units after removing gamma. The push node explicitly defines its comparison by applying Q to the scalar unit and taking the extension/restriction adjunct using the coefficient-restriction comparison. Thus the beta transpose is d inverse followed after Q of the scalar unit; reversing d would be ill-typed. No equality of chosen resolutions is needed.

For step 4 the ring-change node's adjunct equation applies to t equal to the E counit, with source object Q^E Z and target Z. Its E adjunct is the identity, so its ordinary adjunct is d_Z. Expanding the inverse Hom bijection gives exactly the displayed ambient counit formula. This formula is valid at r_T Z even if that object is not integral constructible. I explicitly kept this ambient distinction in the proof.

For step 5 I checked the domains of all maps: both sides start at F_T P Q M and end at F_T M, so their scalar adjunction transposes start at P Q M. Naturality of b moves the restricted beta across b inverse. The two d factors then cancel, and counit naturality at j_T,M gives the same transpose as F_T epsilon. This is an explicit elementary substitution from steps 3–4 and the defining Hom bijections; no new lemma about compatibility is hidden. The existing mate definition identifies the resulting counit equation with the mate of alpha inverse, as dictated by that definition's direction.

For step 6 I checked the E transpose of D_N. Counit naturality moves alpha_N outward; step 5 at P N substitutes the integral counit; alpha naturality at eta_N moves its inverse to the far right; the integral triangle identity gives the identity. The E triangle identity identifies the transpose of its unit with that same identity. This proves the unit equation rather than merely asserting that it transports. Restoring gamma uses the specified transported integral adjunction, so no replacement unit or counit is introduced.

For step 7 the rational category has literally the same objects, and morphisms are integral fractions. Rational transport supplies the extensions of functors and natural transformations. The proof checks naturality on fractions by multiplying the integral equation by the common inverse power of varpi; the triangle equations and both comparison equations have the same components on all objects. The scalar-functor node specifies the realization on fractions. This proves persistence without assuming a Karoubi envelope, full faithfulness of realization, or an integral lattice for an ambient restriction object.

Small cases checked: h the identity reduces the comparisons and both equations to the chosen adjunction's identities; zero objects and the empty scheme give identities of the unique zero maps; an integral object killed by a power of varpi has zero realization and both equations hold in the zero Hom groups. None of the calculations cancels a scalar in an integral Hom group, assumes nonzero realization, uses properness, or assumes a cartesian square. All seven steps have fewer than 2000 characters; the only substantive external comparisons are cited existing nodes. The argument was organized to avoid a new node restating the unit or counit clause. No new statements require a separate edge-case audit. No target statement or unit route was altered.

## Not duplicates

No new nodes. Existing coefficient-change and mate nodes are cited instead of duplicated.

## Previous validation

Server `review_split` returned PASS (0 new nodes). The required `deliver.py --no-push` completed successfully with `OK (not pushed)` at f2bf42da3ca: server preflight passed, including the DAG and split checks. The final report update is revalidated before pushing. No local DAG checker, compiler, Lake command, or repository git command was run.


## Repair of returned delivery (2026-10-21)

The return names one landing failure: `lem-weil-pbc-realization-completed-pull` changed after the reviewed delivery. I compared the retained delivered item and its saved verbatim citation with the current DAG. The current item is still unsplit there; the retained proof and logged searches remain applicable. The first required dry run exited with four stale-quote failures, exactly at steps 1, 2, 3, and 6. Every saved quote for every other cited node remains verbatim in its current statement; I re-read those statements as well.

Re-reading the changed pull statement shows that it retains ordinary-pull constructibility, the actual completion-unit isomorphism gamma, the alpha formula using gamma inverse, and preservation of localization units. It now specifies c_h by the profinite coefficient inverse-image theorem and, in continuous-function coordinates, as the adjunct of precomposition with the base-change projection. It also explicitly specifies the E coefficient map by localizing c_h and spells out identity/composition coherence. Thus none of the assertions used in steps 1, 3, and 6 was withdrawn. Those steps and both adjunction equations remain valid. Their citation excerpts now quote the retained assertions from the current statement.

For step 2 I changed the argument, rather than merely rebasing unchanged files: it now uses the current statement's explicit adjunct/precomposition definition and its specified localized E map. The coefficient square commutes because precomposition commutes with postcomposition by A into E. This verifies the exact hypothesis of the existing ring-sheaf-change adjunction statement. The separate localization-coherence citation still supplies the normalization on fractions. The schemes, finite coefficient extension, Noetherian and dimension hypotheses agree with those of the current pull statement; no properness or immersion hypothesis is introduced. All four completed-pull quotes were replaced with current verbatim excerpts. No new node or target change is required, and the saved Mathlib searches are retained because neither the item statement nor the search question changed.

I rechecked B--E against the retained proof: the counit and unit equations are still derived explicitly in steps 5--6, not delegated to a new node; the only changed step is the coefficient-square verification in step 2. It is below 2000 characters and contains no hidden comparison lemma: the comparison itself is supplied by the current completed-pull and localization statements, and the square is checked by its adjunct on continuous functions. The identity, empty-scheme, zero-object and varpi-power-torsion cases still require no cancellation in integral Hom groups. This paragraph supplements my signed Review by Q27 above with the check requested by the return.

## Current validation

The repaired delivery passed the required server dry run against the current DAG: `OK (not pushed)` at `fb89f67f3c2`, with preflight passed. The report update is revalidated before pushing. No compiler, Lake command, local DAG checker, repository git command, or repository write was used.
