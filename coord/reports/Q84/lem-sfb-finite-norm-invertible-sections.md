## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-norm-invertible-sections.json — repaired split, exact original statement retained; 1987 characters of current assembly.
- dag/nodes/sec-six-functors-basics/lem-sfb-norm-frame-tensor-section-gluing.json — statement-only unsplit lemma; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-function-norm-nonvanishing.json — statement-only unsplit lemma; no Mathlib match.
- citations.json — verbatim statement quotations for every proof-step citation.

Attachments: none. The project theorem AlgebraicGeometry.Scheme.Modules.exists_invertible_norm_sections in lean/Sheaf/AlgebraicGeometry/FiniteNormInvertibleSections.lean:78 ends with sorry. Searches of lean/WeilConjectures by the blueprint id and by norm/invertible/section concepts found no theorem proving the whole item. The finite-free determinant norm criteria in Morphisms/FiniteFlatNorm.lean:139 and BaseChangeNorm.lean:120 require affine opens and free algebras (or base change of a field extension) and use their determinant norm, whereas the new function lemma treats arbitrary multiplicative restriction-compatible maps and finite nonflat morphisms. They cannot attach to it. No Lean source was changed or compiler run.

WANTED: none. coord/dag-sync.md is absent in this read clone; the explicit current brief and current live nodes were followed.

The sandbox initially contained only dispatcher .brief files, with no node/report/search log to preserve. I copied the current item, whose seven steps and reviewed/Lean metadata agree with the returned description, and changed only its stage-1 split/report fields. There was no existing split/report for an initial retained-work dry run. No repository git command was run. Current main material was used rather than a stale reproduction. The item's statement, its chapter/unit, source, prior recorded searches, Lean record and maintainer fields are retained.

## Repair of the returned re-split

The sole return asks for at least two independent statement-only nodes of comparable work, not a shorter retelling. Two nodes now distribute the actual work. The frame lemma receives the old cocycle calculation (440 characters), gluing step (256), and tensor-power coefficient/sheaf gluing calculation (693): 1,389 characters of the old proof. The function lemma receives the zero implication (255) and neighborhood/inverse argument (972): 1,227 characters. The parent keeps the cover selection (209) and elementary final set argument (285), assembling the new results. Thus neither new node restates the item: one constructs compatible local-frame norms with no finiteness or vanishing assumptions and no locus equality; the other is about regular functions only and constructs no bundle. Their arguments can be worked independently, and neither depends on the parent or on the other. Both have proof [], proof_deps [], proof_origin null, status unsplit. No argument has been discarded.

## Preserved argument and allocation

The seven steps below are retained verbatim from the current returned proof. Steps 2-4 belong to the frame lemma, steps 5-6 to the function lemma, and steps 1,7 remain in the parent assembly. These are work instructions for later splitting of the new nodes, not proof fields in their statement-only records.

### Former step 1

Apply [lem-sfb-finite-trivialize-invertible-upstairs] at each point of $Z$ to obtain an open cover $(V_i)$ and free generators $e_i$ of $M$ on $p^{-1}V_i$. Fix these choices once, independently of $n$ and $s$.

Cited existing statements: lem-sfb-finite-trivialize-invertible-upstairs.

### Former step 2

On $p^{-1}(V_i\cap V_j)$ write $e_i=u_{ij}e_j$. Uniqueness of coefficients in a free rank-one module gives $u_{ii}=1$, $u_{ji}=u_{ij}^{-1}$, and $u_{ik}=u_{ij}u_{jk}$ on triple overlaps. Put $v_{ij}=\nu_{V_i\cap V_j}(u_{ij})$. Multiplicativity and preservation of $1$ give $v_{ij}\nu(u_{ij}^{-1})=1$, so $v_{ij}$ is a unit. Restriction compatibility then gives $v_{ii}=1$, $v_{ji}=v_{ij}^{-1}$, and $v_{ik}=v_{ij}v_{jk}$ on triple overlaps.

Cited existing statements: def-sc-invertible-module.

### Former step 3

Apply [lem-sc-glue-component-transition-cocycle] to the units $v_{ij}$ on the cover $(V_i)$. It supplies an invertible module $N$ on $Z$ with chosen generators $f_i$ satisfying $f_i=v_{ij}f_j$. This single $N$ will serve all tensor powers and all sections.

Cited existing statements: lem-sc-glue-component-transition-cocycle.

### Former step 4

Fix $n\geq1$ and $s\in\Gamma(Y,M^{\otimes n})$. Iterating the tensor-product assertion of [lem-weil-pbc-invertible-pullback-tensor](1) makes $M^{\otimes n}$ and $N^{\otimes n}$ invertible. Tensoring the chosen trivializations gives generators $e_i^{\otimes n}$ and $f_i^{\otimes n}$, with transitions $u_{ij}^{n}$ and $v_{ij}^{n}$. Write $s=b_i e_i^{\otimes n}$ over $p^{-1}V_i$; equality of its restrictions says $b_j=b_i u_{ij}^{n}$. Hence, on overlaps, $\nu(b_j)=\nu(b_i)v_{ij}^{n}$ by restriction compatibility and multiplicativity. The local sections $t_i=\nu(b_i)f_i^{\otimes n}$ therefore agree. The sheaf axiom for $N^{\otimes n}$ glues them to a section $t\in\Gamma(Z,N^{\otimes n})$.

Cited existing statements: lem-weil-pbc-invertible-pullback-tensor.

### Former step 5

If $y\notin Y_s$ and $p(y)=z$, choose $i$ with $z\in V_i$. In the chosen free generator, $s(y)=0$ means $b_i(y)=0$. The vanishing hypothesis on $\nu_{V_i}$ gives $\nu_{V_i}(b_i)(z)=0$, so $t(z)=0$. Consequently $Z_t\subseteq Z\setminus p(Y\setminus Y_s)$.

Cited existing statements: def-weil-pbc-ample-invertible-module.

### Former step 6

Conversely let $z\in Z$ have $p^{-1}(\{z\})\subseteq Y_s$. By [lem-weil-pbc-nonvanishing-section-trivializes] applied to the invertible module $M^{\otimes n}$, $Y_s$ is open. By [lem-weil-pbc-finite-closed-map-finite-fibres](1), $p(Y\setminus Y_s)$ is closed. Choose $i$ with $z\in V_i$ and put $W=V_i\setminus p(Y\setminus Y_s)$, an open neighborhood of $z$; then $p^{-1}W\subseteq Y_s$. The function $b_i$ is nonzero in every residue field on $p^{-1}W$. Apply [lem-weil-pbc-nonvanishing-section-trivializes] to the trivial invertible module on the open scheme $p^{-1}W$ with section $b_i|$: its entire nonvanishing locus is $p^{-1}W$, so multiplication by $b_i|$ is an isomorphism. Its inverse evaluated at $1$ yields a section $c$ with $b_i|\,c=1$. Multiplicativity gives $\nu_W(b_i|)\nu_W(c)=1$. Thus $\nu_W(b_i|)(z)\ne0$ in the residue field at $z$. Restriction compatibility identifies this with $\nu_{V_i}(b_i)(z)$, and the frame $f_i^{\otimes n}$ gives $t(z)\ne0$.

Cited existing statements: lem-weil-pbc-nonvanishing-section-trivializes, lem-weil-pbc-finite-closed-map-finite-fibres.

### Former step 7

The two inclusions give $Z_t=Z\setminus p(Y\setminus Y_s)$. For any set map $p$, membership in that complement means there is no point of $Y\setminus Y_s$ above $z$, equivalently $p^{-1}(\{z\})\subseteq Y_s$. This proves the displayed equality for every $n$ and $s$ with the fixed $N$.

Cited existing statements: none; set theory.

For the function lemma's more general local open V, closedness is relative to V: apply the finite closed-map theorem to p restricted over V, so the image of p⁻¹V minus D(b) is closed in V. This makes W open in V and hence in Z. It does not assert that that image is closed in all of Z. The nonvanishing-trivialization lemma is applied to the trivial invertible module on p⁻¹W, so it supplies the inverse c to multiplication by b. Restriction compatibility gives the required equality of norm evaluations after shrinking.

## Searches and source reading

Read literature/stacks-project/divisors.tex:3585-3770: Section norms (Tag 0BCX, divisors-section-norms), lemma-finite-trivialize-invertible-upstairs (0BUT), lemma-norm-invertible (0BCY), lemma-norm-map-invertible (0BCZ), and the opening of lemma-norm-ample (0BD0). Verified tag-label mapping in tags/tags. The frame lemma precisely exposes 0BCY's transition construction and 0BCZ's coefficient compatibility for tensor powers. The function lemma exposes the omitted reverse implication using the neighborhood-unit observation in 0BCX. No SGA route is used.

Read dag/chapters/sec-six-functors-basics.json and dag/units/sk-thm-sf-ctf-stability.json. This auxiliary algebraic-geometric norm argument stays on the recorded alteration/ample-descent route and changes no unit or chapter. blueprint_refs.py ancestor reports from.node None for this existing ancestor chain; the new nodes faithfully extend the item's via chain, and their from.place identifies the exact local norm argument. Whole-blueprint searches norm.*invertible, norm.*vanish, norm transition, norm.*function, norm.*fibre and norm.*line found no blueprint node stating either lemma. DAG searches by 0BCX/0BCY/0BCZ and norm/cocycle/transition/nonvanishing concepts identified the related nodes compared below. Source declaration searches by those concepts found only narrower determinant-norm criteria.

Each new node records all five actual logged searches for its question: LeanSearch, Loogle, grep and two LeanFinder phrasings. The function query's LeanSearch returned a rate-limit failure, accurately recorded unavailable. The other searches succeeded. Read hits included generic group cocycle identities and sheaf section maps for the frame question, and NumberField units/norms, Algebra.norm localization, structure-sheaf fraction normalization and residue-field/basic-open facts for the function question. None states the required scheme result or specializes to it in one line. The grep normalization hits at Normalization.lean:80,117,120 concern normalization diagrams, not multiplicative norms. Searches are in searches.jsonl and query text is copied exactly; no service outage is called absence.

## Not duplicates
lem-sfb-norm-frame-tensor-section-gluing vs lem-sfb-finite-norm-invertible-sections: the parent asserts existence with saturated loci; the frame lemma exposes the transition and coefficient construction without the locus theorem, and the function lemma has only functions and no bundle construction.

lem-sfb-norm-frame-tensor-section-gluing vs lem-sfb-finite-trivialize-invertible-upstairs: only supplies a cover trivializing a given line bundle, with no norm or norm-function criterion.

lem-sfb-norm-frame-tensor-section-gluing vs lem-sfb-normal-integral-finite-sheaf-norm: constructs the norm maps assuming a normal integral base; these new lemmas take arbitrary multiplicative maps as input and require neither normality nor integrality.

lem-sfb-norm-frame-tensor-section-gluing vs lem-sfb-finite-normal-ample-descent: concludes descent of existence of ample bundles under normality; neither new lemma assumes or concludes ampleness.

lem-sfb-norm-frame-tensor-section-gluing vs lem-sfb-affine-invertible-finite-set-section: constructs a section nonzero at finitely many points on an affine scheme; neither norm transition construction nor the finite-map local-unit criterion is its statement.

lem-sfb-norm-frame-tensor-section-gluing vs lem-sfb-finite-field-norm-minpoly: concerns field determinants and minimal polynomials, with no scheme sheaves or fibre neighborhoods.

lem-sfb-norm-frame-tensor-section-gluing vs lem-sfb-integral-minpoly-fraction-descent: concerns descent of minimal polynomial coefficients in integral domains, not line bundles or local-unit norm criteria.

lem-sfb-norm-frame-tensor-section-gluing vs lem-pur-finite-flat-kummer-norm-degree: assumes finite locally free Noetherian morphisms and constructs determinant norms with Kummer/degree compatibility; it has neither the arbitrary multiplicative-map tensor-section rule nor the local-function criterion under mere finiteness.

lem-sfb-finite-function-norm-nonvanishing vs lem-sfb-finite-norm-invertible-sections: the parent asserts existence with saturated loci; the frame lemma exposes the transition and coefficient construction without the locus theorem, and the function lemma has only functions and no bundle construction.

lem-sfb-finite-function-norm-nonvanishing vs lem-sfb-finite-trivialize-invertible-upstairs: only supplies a cover trivializing a given line bundle, with no norm or norm-function criterion.

lem-sfb-finite-function-norm-nonvanishing vs lem-sfb-normal-integral-finite-sheaf-norm: constructs the norm maps assuming a normal integral base; these new lemmas take arbitrary multiplicative maps as input and require neither normality nor integrality.

lem-sfb-finite-function-norm-nonvanishing vs lem-sfb-finite-normal-ample-descent: concludes descent of existence of ample bundles under normality; neither new lemma assumes or concludes ampleness.

lem-sfb-finite-function-norm-nonvanishing vs lem-sfb-affine-invertible-finite-set-section: constructs a section nonzero at finitely many points on an affine scheme; neither norm transition construction nor the finite-map local-unit criterion is its statement.

lem-sfb-finite-function-norm-nonvanishing vs lem-sfb-finite-field-norm-minpoly: concerns field determinants and minimal polynomials, with no scheme sheaves or fibre neighborhoods.

lem-sfb-finite-function-norm-nonvanishing vs lem-sfb-integral-minpoly-fraction-descent: concerns descent of minimal polynomial coefficients in integral domains, not line bundles or local-unit norm criteria.

lem-sfb-finite-function-norm-nonvanishing vs lem-pur-finite-flat-kummer-norm-degree: assumes finite locally free Noetherian morphisms and constructs determinant norms with Kummer/degree compatibility; it has neither the arbitrary multiplicative-map tensor-section rule nor the local-function criterion under mere finiteness.

lem-sfb-norm-frame-tensor-section-gluing vs lem-sfb-affine-invertible-section-fibre-correction: the existing node modifies one section on an affine scheme by adding a scalar multiple; it has no norm maps, transition cocycle, or tensor-section gluing.

lem-sfb-finite-function-norm-nonvanishing vs lem-sfb-affine-invertible-section-fibre-correction: the existing node corrects an affine section at one point while keeping prescribed values elsewhere; it has no finite morphism or fibrewise norm criterion.

lem-sfb-norm-frame-tensor-section-gluing vs lem-sfb-affine-finite-point-scalar-separation: the existing node separates an affine point from finitely many others by a regular function; it constructs neither normed frames nor tensor-power sections.

lem-sfb-finite-function-norm-nonvanishing vs lem-sfb-affine-finite-point-scalar-separation: the existing node constructs a separating regular function on one affine scheme; it does not assert a norm nonvanishing criterion under a finite map.

## Review by Q84

I read the Stacks source with the original seven steps and every cited existing statement open. The exact parent hypotheses and quantifier order remain unchanged: arbitrary schemes, p finite and surjective, d≥1, a multiplicative unital restriction-compatible ν satisfying the power and vanishing conditions, arbitrary invertible M, and one N chosen before n and s. The proof actually does not need the power identity beyond the stated hypotheses. No flatness, Noetherian hypothesis, reducedness, or ampleness has been introduced.

Parent step 1 cites lem-sfb-finite-trivialize-invertible-upstairs, whose statement really gives an open neighborhood trivializing M above each base point. Choosing those neighborhoods and generators gives the cover. Step 2 cites the new frame lemma: its statement expressly supplies the same N for all powers and the local expression t=ν(b_i)f_i^n, so this is a direct application, not an appeal to an unstated construction in a proof. All its weaker hypotheses follow from the parent's assumptions. Step 3 cites the frame lemma for tensor generators and local expressions, the function lemma for exactly ν(b_i)(z)≠0 iff every point of the fibre has b_i(y)≠0, and def-weil-pbc-ample-invertible-module for the residue-field meaning of Y_s and Z_t. A generator gives an isomorphism of each one-dimensional residue-field fibre, so multiplying its value vanishes exactly when the coefficient vanishes. This last identification is elementary. Step 4 is the written set-complement equivalence and uses no geometric fact. citations.json quotes the actual statements of every cited node, not their proofs.

For the new frame node I checked the orientation e_i=u_ij e_j gives b_j=b_i u_ij^n, hence ν(b_j)=ν(b_i)v_ij^n and therefore equality of local t_i. Unital multiplicativity takes units to units by ν(u)ν(u⁻¹)=1 and carries the cocycle identities. The old generic gluing lemma really states existence of an invertible module with the given transitions; the tensor lemma really includes tensor invertibility. The new statement records these outputs without a proof sketch, and its future proof work is preserved verbatim above.

For the new function node I checked both directions: a zero at any y forces a zero norm by the input condition, while the reverse uses openness of D(b), finite closedness over V, and the inverse of a nowhere-zero regular function on p⁻¹W. The existing nonvanishing lemma expressly supplies the needed isomorphism and division of sections; the finite-closed-map statement expressly supplies closedness. The refined W and c clauses keep the substantial neighborhood argument available rather than hiding it behind the final equivalence. The statement defines D(b) and residue-field evaluation and needs no implicit frame, no arbitrary existence construction, and no statement taken from a proof of another node.

Small cases: for p=id and ν(b)=b^d the construction gives N=M^d and the expected same nonvanishing locus; for two disjoint sheets with product norm, ν(b) is nonzero exactly when both factors are nonzero. A zero section vanishes everywhere and a unit section vanishes nowhere; nilpotent coefficients vanish in every residue field. The function node allows empty fibres: closedness produces W disjoint from the image, and unitality of ν_W then gives the required unit evaluation (if a vanishing condition precludes such a ν, the hypotheses simply have no instance). Empty schemes, empty cover members, repeated cover members and n=1 cause no exception. No claim about point values lifting to equality of sections is made.

I checked B-E individually: statement-only new nodes introduce all data, use single-escaped TeX, cite definition nodes for schemes/invertibility/tensor powers/finite morphisms/residue fields, have correct Stacks labels, and have real search records. They are not elementary fragments of a few lines: they isolate the two substantive old arguments of comparable size. All same-tag candidates are compared above; no new ids already exist. Parent proof citations are exactly its proof_deps, and no new node depends on the parent. The only return point is repaired by two independent unsplit nodes plus a 1,254-character parent assembly; all seven old arguments are retained in this report. No step exceeds 2,000 characters. No source error or statement dispute was found. No work is left unfinished other than the deliberately unsplit new nodes, which other workers will prove.


## Repair of the promotion return (2026-10-22)

Return L said that the reader-approved completion had not been promoted into the live DAG and requested a rebase onto the current DAG, with changed citations re-read. I retained the sandbox's two statement-only nodes, full preserved proof, report and actual searches.jsonl rather than restarting them. The previous dry-run receipt named de6a3c8778d. Before editing anything I ran the required retained-work dry run; it exited successfully at b4e78637dd1. The delivery command builds against current origin/sheaf-dag and overlays only worker-owned fields, so maintainer metadata comes from the current live base.

The current read clone still has the original seven-step proof, and old-proof.json is exactly that proof. Comparing its parent node with the retained sandbox found differences only in proof, proof_deps and split_report: statement, stmt_deps, source, blueprint, Lean record and reviewed metadata agree. Neither new node id exists in the current DAG. The current released stage-1 repair note explicitly reopens this reviewed item and requires two comparable independent nodes and an assembly of at most 3000 characters; the prior reviewed status therefore does not supersede this repair. The repair remains the same two arguments requested by that note, rather than an unchanged copy of the live proof.

I re-read every current parent citation: 0BUT gives the upstairs-trivializing cover; the retained frame node gives a fixed N and its tensor-section coefficient formula; the retained function node gives the exact all-points-in-the-fibre criterion; the ample-invertible definition gives the residue-field interpretation of the nonvanishing loci. I also re-read all current statement dependencies and the generic cocycle-gluing, tensor-invertibility, nonvanishing-trivialization and finite-closed-map statements used in the preserved argument. Their current statements support the old arguments without a replacement dependency. No reliance on a cited proof rather than its statement is needed. All five citations.json entries were refreshed from the actual current statements and verified as verbatim substrings.

To make this repair concrete beyond the rebase, parent step 3 now explicitly checks every hypothesis of the function lemma against the item and spells out the residue-field basis calculation: a generating frame evaluates to a basis, so its scalar multiple is zero precisely when the scalar is zero. This is the elementary identification that connects the two independent nodes; no third lemma or stronger geometric assumption is hidden. The statement is unchanged. The parent still has four short steps, each below 2000 characters, with the whole assembly below 3000 characters. I retained every old argument in the allocation above.

I re-read Stacks divisors.tex 3585-3770 and checked the 0BCX/0BUT/0BCY/0BCZ tag mapping. The identity and disjoint-two-sheet examples still give the expected loci; zero and nilpotent coefficients, unit coefficients, empty schemes and empty fibres introduce no missing hypothesis. The reverse direction uses closedness relative to V and the inverse of a nowhere-zero function; it never assumes flatness or Noetherianity. For the local-function statement, open restriction of a finite morphism is finite directly from its affine definition. The frame statement does not use the power identity or finiteness once the cover is given.

The retained search log was read in full. Its questions and new-node statements have not changed, so no historical search was repeated or fabricated. Current whole-blueprint search and ancestor lookup again found no equivalent imported node and returned the existing null ancestor. A fresh tag scan also found lem-sfb-affine-invertible-section-fibre-correction and lem-sfb-affine-finite-point-scalar-separation; I opened both. Their source is 0F20 (the norm tags occur elsewhere in their metadata), and their statements concern modifying an affine section and separating finitely many affine points, respectively. Neither states norm-frame gluing or the finite-map norm nonvanishing criterion, so neither replaces either new node. The earlier same-source comparisons remain valid. No source dispute, missing literature, Lean edit or compiler invocation arose in this repair.


## Review by Q84 — current-base repair retry (2026-10-22)

I continued the already repaired sandbox, including its preserved seven-step proof, both new node files, citations and all ten recorded search results. The required initial retained-work dry run finished successfully at 6d829f698dd. This retry addresses the same promotion return, not a new mathematical split. I compared the current read-clone item field by field: its only differences from the retained item were proof, proof_deps and split_report; old-proof.json still equals its complete seven-step proof. I rebuilt the sandbox item from that current node and restored only those three worker-owned split fields. In particular its exact statement, statement dependencies, source, blueprint ancestry, Lean and maintainer metadata come from the current DAG. The current released stage-1 repair record still requires two independent new nodes; neither retained new id exists in the current DAG. The delivery tool rebases these sandbox files onto its freshly fetched server base.

I opened every current proof citation and every statement dependency of the three delivered nodes. All five previously retained citation quotations are still verbatim parts of the actual current statements, so there is no changed cited statement to replace. I nevertheless refreshed citations.json against these current files. Step 1 uses the precise 0BUT neighborhood-and-isomorphism statement for a finite p and invertible M. I repaired its previously implicit frame choice: e_z is the image of 1 under the selected trivialization, multiplication by e_z is that isomorphism, and z in V_z proves the chosen family covers Z. These elementary identifications use no additional theorem. Step 2 applies the frame lemma with exactly this cover and its generators and obtains one N before any power or section is chosen. Step 3 now starts with an arbitrary z in Z and chooses a cover member explicitly. The function lemma applies to b_i because finiteness, restriction compatibility, unitality, multiplicativity and the vanishing condition are all hypotheses of the unchanged parent. Its stated equivalence plus the frame lemma's stated generator and local-coefficient clauses gives the residue-field equivalence for s and t. The cited ample-invertible definition supplies precisely the meaning of the nonvanishing loci. Step 4 is the elementary equivalence between absence of a point in the complement above z and inclusion of the whole fibre. No cited proof construction is used in place of a statement.

I re-read divisors.tex, Section norms 0BCX and Lemmas 0BUT, 0BCY and 0BCZ, including their proofs and the opening of 0BD0. I verified all four tag-to-label entries. For the frame node the source's u_ij convention gives b_j=b_i u_ij^n and hence the stated norm coefficients agree; the source's cocycle construction and its section calculation are the two preserved work instructions for that node. The generic cocycle-gluing statement, tensor-invertibility statement, nonvanishing-trivialization statement and finite closed-map statement were also re-opened; they still supply the precise inputs in the retained argument. For the function node I checked that W is open relative to V using finite closedness for the restricted finite map, and therefore open in Z. Inverting the nowhere-zero function on p^{-1}W and applying the multiplicative unital norm proves the reverse implication without flatness or normality. The forward implication is exactly the stated vanishing hypothesis. Both new records remain self-contained, statement-only and independent of the parent.

Fresh whole-blueprint search returned zero equivalent imported nodes and ancestor lookup returned the same null ancestor. I read every current node found by tags 0BCX, 0BCY, 0BCZ and 0BUT, not merely their file names; the two additional affine separation/correction statements are now explicitly compared for each new node in Not duplicates. Their claims do not concern multiplicative norms. A fresh search of lean/WeilConjectures by the exact item tag and norm/invertible/section terminology found no exact attachment; the existing Sheaf theorem still has sorry. I read the retained search log results rather than repeating unchanged search questions. No new Mathlib verdict was inferred from an unavailable service.

I checked B1-B9 and C1-C8 against the files: statements introduce their objects, name defining nodes, preserve TeX, and cite the correct source labels; all non-elementary parent inputs have statement citations; proof_deps is the union of uses. D1-D5 are addressed by the explicit re-split order: two independently usable arguments of comparable original size are isolated while the parent assembles them, with all old work retained in the report. E1-E7 were checked using identity/power norms and the two-sheet product norm, zero and unit sections, nilpotent coefficients, n=1, and empty schemes and fibres. These tests introduce no missing hypothesis and show no source error. The new-node statements and search questions are unchanged. No repository or launcher file was written, no git command was run in the repository, no Lean was written, and no compiler/build was run.

The current assembly contains 1987 characters, with step lengths 437, 445, 888, 217; every step is below 2000 characters and the total is below 3000. The fresh server dry run and push below are required before treating this retry as delivered.


## Review by Q84 — promotion repair on current DAG (2026-10-23)

I checked the previous tool result before continuing: the retained-work dry run exited 0 and printed OK (not pushed) at 8bba4eec712. No push or other delivery invocation remained active. The same promotion return still applies. I rebuilt the item from the current read-clone node, retaining only the sandbox proof, proof_deps and split_report. Before this edit those were its only differing fields. The current released stage-1 note still explicitly requires this re-split despite the old reviewed metadata, and neither new node exists in the current DAG. old-proof.json still equals the current original seven-step proof. The delivery tool performs the actual rebase onto its newly fetched server base.

I re-opened every current parent citation and all statement dependencies of all three delivered nodes. No cited statement changed in a way requiring replacement. Step 1's finite-trivialization statement gives exactly the neighborhood and isomorphism used to choose a generator. Step 2's frame lemma supplies a fixed N, generating tensor frames and the coefficient formula for its section. I made the local coefficient choice explicit here: the tensor generator gives the unique b_i before the lemma's section clause produces t. This clarifies the assembly's use of the lemma's stated output without taking an implicit construction from its proof. Step 3 applies the finite-function criterion with exactly the finite, multiplicative, unital, restriction-compatible and vanishing hypotheses already assumed; the frame lemma and the ample-invertible definition then identify the coefficient nonvanishing with the two residue-field nonvanishing loci. Step 4 is the elementary complement-of-image equivalence. All five citation entries were refreshed from the actual current statements and are verbatim substrings.

For both new nodes I re-read divisors.tex Section norms and the proofs of the upstairs trivialization, invertible norm and norm-map lemmas, checking the tag table entries 0BCX, 0BUT, 0BCY and 0BCZ. I also re-opened the generic transition-cocycle gluing, invertible tensor, nonvanishing-trivialization and finite closed-map statements used by the preserved arguments. The frame lemma keeps the transition convention e_i=u_ij e_j, so b_j=b_i u_ij^n and the norm coefficients glue in the claimed direction. The function lemma's W is open by closedness of the finite map restricted over V; the inverse c is supplied by trivializing the structure sheaf with its nowhere-zero section. Neither new node needs flatness, normality or the power identity. These are self-contained statements only, with the full original work allocation still preserved above.

I re-read the ten retained search-log results and their node records. Their statements and search questions are unchanged, so the actual searches are reused, including the accurately unavailable LeanSearch result. Fresh whole-blueprint search and ancestor lookup returned no equivalent imported statement and the same null ancestor. I opened all ten current same-tag DAG statements, including both affine correction/separation nodes: none supplies either new result; the Not duplicates comparisons above continue to apply. The project Lean search still finds no exact finished declaration in WeilConjectures; the existing Sheaf theorem visibly ends in sorry.

Against B-E I checked self-contained data and definition citations, correct source labels, unchanged statement hypotheses and quantifier order, actual search provenance, statement-level citations for all non-elementary inputs, no circular dependency, the prescribed two independent arguments of comparable size, and preservation of every old argument. Identity/power norms and two-sheet product norms verify the construction and both locus directions; zero, unit and nilpotent coefficients, empty schemes and fibres, repeated cover members and n=1 cause no additional assumption. The reverse direction uses a relative open neighborhood, never a closed-image assertion in the wrong ambient space. No statement dispute or source correction is needed. No Lean, repository or launcher file was written and no compiler/build was run.

The repaired assembly has 2109 characters, with step lengths [437, 567, 888, 217]; every step is below 2000 and the total is below 3000. The final server dry run and push will now validate and deliver this current-base repair.
