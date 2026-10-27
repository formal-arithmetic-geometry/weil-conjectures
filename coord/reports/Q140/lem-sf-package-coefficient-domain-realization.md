# Repair of D1/C5 return: lem-sf-package-coefficient-domain-realization

## Files written

- `dag/nodes/sec-six-functors/lem-sf-package-coefficient-domain-realization.json`: unchanged statement and stmt_deps; nine-step direct-citation assembly, 2433 characters.
- `dag/nodes/sec-six-functors/lem-sf-package-field-operation-realization.json`: new statement-only unsplit node, no Mathlib match; old step 7, including rationalized evaluation and common-stage representatives.
- `dag/nodes/sec-six-functors/lem-sf-package-common-stage-transport.json`: retained statement-only unsplit node, no Mathlib match; old steps 9–10, with J/j conjugation, functor/transformation descent and exact embeddings.
- `citations.json`: one literal statement quotation for each parent step citation.
- `report.md`: current review and all ten original arguments verbatim below. Previous report retained in sandbox-only `returned-report.md`; old searches and original-citations.json retained.

Two new nodes, zero Mathlib leaves. The two rejected never-landed bundle files have been removed from the sandbox delivery. No repository, launcher or Lean source was written; no compiler or git command was run.

## Attachments

None. Source searches for the item tag and coefficient-domain notions found no exact complete project declaration. Package.lean:224 has a finite-coefficient package, with a sorry at its smooth-base-change clause. The small-etale derived-Hom theorem at Stability/DerivedHom.lean:61 covers a finite-level bound only. Generic rationalization and site-perfect source declarations do not assert the entire item or either new obligation.

## WANTED

None.

## Problems found and repaired

The returned finite-domain and adic-field nodes only conjoined existing statements. They have been dropped. Old steps 1, 2, 3, 5, 6, 8 now cite those statements directly, with hypotheses and the actual compact-support tower retained. For old step 4, a whole-DAG and blueprint search found `prop-sf-dualizable-hom`, which already asserts precisely the site-perfect evaluation isomorphism, at every coefficient stage with the same local coefficient-unit interpretation. It would violate the duplicate rule to create a finite specialization of it. The sharper bound is still cited directly from stability (ii). This is the one adjustment to the return's suggested extraction; it reuses an exact existing result instead of inventing another node.

The real remaining constructions are old step 7 and old steps 9–10. The first is now a conditional field-realization lemma: it assumes the already-proved integral preservation rather than bundling its proofs again, and asserts the natural rationalized formulas and their independence on finite common-stage representatives. The second is retained unchanged from the returned head, as the return explicitly accepted its J/j transport as a genuine argument. The two obligations do different work: scalar localization/evaluation/finite-representative realization versus conjugation through distinct coefficient conventions and descent of arbitrary exact families. The old arguments of lengths 964 and 3175 characters are fully preserved below for their workers. No node restates the whole item. No source error or statement dispute was found, and the parent statement and stmt_deps agree exactly with current live.

## What remains unfinished

The two new nodes are intentionally unsplit with no proof steps, no proof dependencies and null proof_origin. Their complete old arguments and citations are retained below for later workers. The parent's one-level proof is complete.

## Not duplicates

lem-sf-package-field-operation-realization vs lem-coef-rational-operations: the existing result identifies rational Hom and exceptional inverse image, including evaluation; the new conditional realization also gives pullback, completed tensor and both direct-image values and proves their well-defined realization on the SF common-stage category for all representatives and localized arrows. It does not bundle integral preservation, integral reductions or scalar-extension exactness.
lem-sf-package-field-operation-realization vs lem-fix-operation-reduction: that existing coefficient-comparison theorem supplies compatibility of already-defined operations and comparisons; the new realization makes the object/morphism computation on raw rationalization and on finite common-stage representatives explicit under integral preservation, including the rational-Hom identification and evaluation. Its handoff is old step 7, using both existing interfaces and the two category constructions.
lem-sf-package-field-operation-realization vs lem-sf-adic-qbar-constructible-realization: the latter compares with a native module presentation and has a conditional Hom comparison; it does not identify pullback and both direct images with their rationalized integral values or perform the field-operation realization here.
lem-sf-package-field-operation-realization vs lem-sf-rational-thick-evaluation: that result proves closure of an evaluation-isomorphism locus under thick operations; it does not realize the five operation functors at field stages.
lem-sf-package-common-stage-transport vs prop-weil-pbc-descent-functors: that proposition descends on the PBC pair category only, whereas this lemma conjugates the SF family through J and j, cancels those comparisons to obtain the literal SF representative formula, and transports triangulation, retract closure and exact embeddings.
lem-sf-package-common-stage-transport vs lem-fd-rational-coefficient-category-comparison: that theorem supplies coherent comparison equivalences, but does not descend arbitrary compatible exact families or prove idempotent completeness of the SF category.
lem-sf-package-common-stage-transport vs thm-weil-pbc-idempotent-complete-triangulation: that theorem is on the PBC construction only and has no SF-family descent assertion.
lem-sf-package-common-stage-transport vs lem-weil-qbar-idempotent-complete: retract closure alone has neither J/j transport nor coherent family descent.
lem-sf-package-common-stage-transport vs lem-sf-adic-qbar-constructible-realization: module presentation and its conditional Hom comparison are different from arbitrary exact-family transport through SF/PBC J/j.

Whole-DAG searches for site-perfect/evaluation, rational/evaluation, coefficient passage and common-stage comparisons were checked against statements, not just names. Blueprint searches for site-perfect, rationalization, coefficient passage and field passage were read. The first found the exact existing evaluation node; the last found no imported field-passage lemma. The broader package and the parent cannot be used to prove their children. No Stacks source is introduced for a fact it does not state; no forbidden SGA source is used.

## Mathlib searches

The common-stage node retains its logged searches and results, which I read: generic exact functors, idempotent-completeness under equivalence and condensed AB results do not establish the coefficient-specific transport. For the changed field question, I ran two new semantic phrasings with LeanFinder, LeanSearch, Loogle (including a corrected pattern) and whole-Mathlib grep through the prescribed Q140/item command. Exact queries/results are in the node and searches.jsonl. The first Loogle pattern reports unknown identifier CategoryTheory.Rationalization; the valid IsTriangulated follow-up reports generic exact-functor interfaces. Grep returned zero hits. Semantic hits are ordinary sheaf Hom, light condensed internal Hom or Zariski tilde modules. Their signatures do not assert constructible derived field-operation realization. I read Mathlib/CategoryTheory/Triangulated/Functor.lean:186, Mathlib/CategoryTheory/Idempotents/Basic.lean:163 and the ihomPoints/ihom_map_val_app signatures in Mathlib/Condensed/Light/InternallyProjective.lean. The common-stage searches were not repeated because its statement/question is unchanged. Item searches and their already-read results are retained from the prior work.

## Review by Q140

I read GOAL, AGENTS, the worker brief, worker/stage rules, the three blueprint levels in SETUP, the chapter/unit records and both complete B–E checklists in delivery-errors. The main-20261015 prop-functor-package statement/proof remains the route: its opening names the coefficient-domain and Hom results, and clause (1) names exact scalar extension, descent and idempotent-complete triangulation. I read the current rational-operations and operation-reduction proofs for the field-realization node, and the descent/triangulation proofs for the common-stage node. I read Stacks 08JJ, sites-cohomology.tex label lemma-dual-perfect-complex, for the old step-4 argument; it proves the canonical evaluation comparison locally on strict perfect representatives. I then checked the existing prop-sf-dualizable-hom statement, which gives exactly the needed finite specialization. The old proof using 08JJ is retained verbatim as requested, although the parent now cites the exact project node directly.

For every parent step I opened the statements of its uses. Step 1 takes only finite restrictions (i)–(iv) from stability; all schemes/morphisms are separated finite type over k and ell is invertible. Step 2 takes the pro-etale general Hom preservation and precisely [c-b-2d,e-a+2d] from the finite Hom corollary. Step 3 takes the quotient isomorphism and its characterization as the unique evaluation transpose from thm-coef-finite-hom, with n >= m >= 1. Step 4 takes the canonical evaluation isomorphism from prop-sf-dualizable-hom at A_n and only the sharp interval from stability. Its local bounded finite-projective hypothesis is exactly site-perfectness, and is not inferred from finite Tor amplitude.

Step 5 uses the three separate integral-preservation statements for completed pullback/tensor, specified ordinary direct image, and the actual compact-support inverse system. The latter statement includes quotient and restriction-of-scalars transitions, completeness and a single cohomological interval for all reductions. Step 6 uses residue Tor control for uniform intervals and the integral Hom corollary for ambient membership and its canonical evaluation-defined reductions for arbitrary integral inputs. No completeness is deduced merely from boundedness. Step 7 uses the new conditional realization; steps 5–6 establish all its integral-preservation hypotheses for each E. Its statement gives the actual Q-images of operation values, naturality on localized arrows, finite-extension compatibility and common-stage independence, including evaluation. The old step-7 argument below still names its four existing interfaces, so no proof has been lost.

Step 8 uses the exact scalar-extension theorem on precisely the SF raw rationalized categories. Step 9 uses the retained common-stage node, whose statement supplies the exact representative formula, transformations and equations, plus ordinary triangulation, retract closure and exact embeddings. I rechecked its handoff against the comparison statement: j has direction J_F T_sf to T_pbc J_E; beta has direction T_S Phi_E to Phi_F T_T; the final representative has beta inverse at the target. T,S are noetherian finite-dimensional with ell invertible, so J applies. The J equivalence identifies finite-stage embeddings and distinguished triangles in both directions. No PBC category is silently substituted for the SF one and no Karoubi envelope is inserted.

Each parent uses-entry has a verbatim quotation in citations.json. All uses equal proof_deps. New nodes carry only statements with self-contained objects, the completed coefficient convention and explicit definition dependencies; no proof sketch is hidden in them. Both new nodes inherit the correct chapter/unit and nearest blueprint ancestor. Existing tool uses are retained, with the newly reused perfect-evaluation node separately explained in split_report.tool_uses. The longest parent step is below 600 characters; no long step hides another lemma. The longer common-stage argument is deliberately statement-only and its full argument is in the handoff below.

I checked n=m=1 and E=F (unit comparisons), identity morphisms and zero complexes. At a point d=0 the Hom bound is the difference interval; for the origin of A^1 the sharper bound is unavailable without site-perfectness, and it is not claimed. Empty schemes allow d=0. For raw rationalization every object has an integral representative by definition; two finite-stage representatives are compared after a common finite field, not by discrete infinite scalar extension. For common-stage arrows the order of beta, Phi(u), beta inverse has the correct endpoints. No hypothesis or conclusion of the parent has changed.

## Validation

The initial retained-head dry run exited OK (not pushed), commit 0d22b501e43. That result predates this repair and is not its certification. The repaired files will be checked with the required server deliver.py --no-push, then delivered only after that process exits OK.

## Complete original argument, retained verbatim

### Original step 1 → parent step 1 (direct citation)

At each $A_n$, apply clauses (i), (ii), (iii), and (iv) of [thm-sf-ctf-stability] to the given $f$ and the finite-Tor inputs. These respectively restrict $Lf^*$, $\otimes^L$, $Rf_*$, and $Rf_!$ to the displayed finite-stage categories. Its hypotheses are exactly separated finite-type morphisms between separated finite-type schemes over the fixed $k$, with $\ell\ne p$; they hold here for every $n\ge1$.

Cited statements: thm-sf-ctf-stability.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Opening sentence, proved constructible domains; stability clauses (i)–(iv).

### Original step 2 → parent step 2 (direct citation)

For $K,L\in\mathcal C_{X,A_n}$, [cor-weil-finite-constructible-hom] gives bounded constructibility and finite Tor amplitude of $R\mathcal Hom_{A_n}(K,L)$, on the small pro-etale site used by the operation datum. With input intervals $[a,b]$, $[c,e]$ and any integer $d\ge0$ satisfying $\dim X\le d$, its stated interval is precisely $[c-b-2d,e-a+2d]$. This proves the general finite-stage Hom restriction and the asserted dimension-dependent bound.

Cited statements: cor-weil-finite-constructible-hom.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Opening sentence: cor-weil-finite-constructible-hom.

### Original step 3 → parent step 3 (direct citation)

Apply [thm-coef-finite-hom] with $A=A_n$, $B=A_m$ and $M=L$. The hypotheses $n\ge m\ge1$ and $K,L\in D^b_{ctf}(X,A_n)$ are those of the item. The resulting isomorphism is exactly the displayed finite coefficient comparison. The theorem characterizes its arrow as the unique tensor–Hom transpose of scalar extension of evaluation; thus the comparison here is that specified arrow, not an arbitrarily chosen isomorphism.

Cited statements: thm-coef-finite-hom.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Opening sentence: coefficient comparison thm-coef-finite-hom.

### Original step 4 → parent step 4; reuse exact existing prop-sf-dualizable-hom

When the first input $K\in D^b_{ctf}(X,A_n)$ is site-perfect in the sense of [def-weil-site-perfect-complex], it is locally on the small pro-etale site a bounded complex of direct summands of finite free $(A_n)_X$-modules, i.e. perfect in the sense of [lem-sfb-ringed-site-perfect-duality] for the ringed site $(X_{\mathrm{proet}},(A_n)_X)$. That lemma gives the canonical evaluation isomorphism $K^\vee\otimes^L_{A_n}L\xrightarrow{\sim}R\mathcal Hom_{A_n}(K,L)$ with $K^\vee=R\mathcal Hom_{A_n}(K,(A_n)_X)$, for every $L$. Clause (ii) of [thm-sf-ctf-stability] gives, under exactly this extra hypothesis, the sharper Tor interval $[c-b,e-a]$. No application of either result to a merely constructible finite-Tor first input is made; that case was covered instead by step 2 (and the origin of $\mathbf A^1$ in clause (ii) shows the sharper bound fails without site-perfectness).

Cited statements: thm-sf-ctf-stability, lem-sfb-ringed-site-perfect-duality, def-weil-site-perfect-complex.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Opening domains and site-perfect qualification in prop-functor-package; stability clause (ii).

### Original step 5 → parent step 5 (direct citations)

At $R$, [lem-pur-integral-operations-preserve-constructible] restricts the completed pullback and completed tensor to the derived-complete integral constructible categories, with their stated finite reductions. Apply [lem-sf-integral-direct-image-constructible] to obtain the same restriction for the specified $Rf_*$. Apply [lem-sf-integral-compact-support-constructible] to the specified compactification reduction tower defining $Rf_!$. That theorem applies to its derived limit with exactly the quotient/restriction-of-scalars transitions, and proves completeness and one finite cohomological interval for all its reductions. All three results allow our finite-type $k$-schemes with $\ell$ invertible; the compact-support result requires the separated finite-type $f$ assumed here. These are preservation theorems for the actual completed operations, so the definition of the integral category alone is not being used to assert preservation.

Cited statements: lem-pur-integral-operations-preserve-constructible, lem-sf-integral-direct-image-constructible, lem-sf-integral-compact-support-constructible.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Opening integral preservation; completed pullback/tensor and the two direct images.

### Original step 6 → parent step 6 (direct citations)

For integral $K,L$, [lem-coef-integral-residue-tor] supplies uniform finite-level Tor intervals from the bounded residue reductions; it does not assert site-perfectness. Now [cor-coef-integral-internal-hom] applies to all $K,L\in D^b_c(X,R)$ and places their ambient internal Hom in that same category. Its canonical evaluation-defined reduction comparison gives the required formula from $R$ to every $A_n$. Consequently this step uses neither a site-perfect model for arbitrary constructible objects nor an inference of completeness from levelwise boundedness alone.

Cited statements: lem-coef-integral-residue-tor, cor-coef-integral-internal-hom.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Opening integral internal Hom: cor-coef-integral-internal-hom.

### Original step 7 → lem-sf-package-field-operation-realization

Use the raw rationalization of [def-weil-rationalization-karoubi] and the finite-representative common-stage construction of [def-weil-algebraically-closed-coefficients]. By [lem-fix-operation-reduction], the pullback, tensor, and two direct-image operations and their coefficient comparisons commute with rationalization and common-stage scalar extension. Thus their field values are the specified coefficient-passage values of the integral outputs established in step 5, and belong to the displayed field categories. The same result supplies scalar compatibility for internal Hom; [lem-coef-rational-operations] identifies the rationalized integral internal Hom with the field internal Hom and explicitly preserves evaluation, including under finite scalar extension. Applied to the integral outputs of step 6 and then to finite representatives, these identifications give internal-Hom restriction and the required evaluation identification at both field stages.

Cited statements: def-weil-rationalization-karoubi, def-weil-algebraically-closed-coefficients, lem-fix-operation-reduction, lem-coef-rational-operations.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Opening field passage: lem-coef-rational-operations; basic operation coefficient passage.

### Original step 8 → parent step 8 (direct citation)

For each finite inclusion $E\subset F$, apply [lem-weil-scalar-extension-exact-triangulated] with $L=F$ to $T$ (and to $S$ when needed). It states that this scalar-extension functor on the rationalized constructible categories preserves shifts and distinguished triangles. This is exactly the finite coefficient-field exactness asserted here.

Cited statements: lem-weil-scalar-extension-exact-triangulated.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Clause (1): lem-weil-scalar-extension-exact-triangulated.

### Original step 9 → lem-sf-package-common-stage-transport

The item's finite stages $D^b_c(-,E)$ and common-stage category $\mathcal C_T$ are those of [def-weil-rationalization-karoubi] and [def-weil-algebraically-closed-coefficients], while [prop-weil-pbc-descent-functors] is stated for the stages of [def-weil-pbc-rational-category] and the pair category $\mathcal P_T$ of [def-weil-pbc-qbar-category]. Our separated finite-type $k$-schemes $T,S$ are noetherian, finite-dimensional, with $\ell$ invertible, so [lem-fd-rational-coefficient-category-comparison] gives exact equivalences $J_{W,E}$ ($W=T,S$), the identity on the common integral objects and on localized Hom groups, with scalar comparisons $j_{W,F/E}:J_{W,F}T^{\mathrm{sf}}_{F/E}\simeq T^{\mathrm{pbc}}_{F/E}J_{W,E}$ respecting identities, shifts and the associators, and the induced exact equivalences $J_W:\mathcal C_W\simeq\mathcal P_W$ which identify finite-stage inclusions, shifts and distinguished triangles. Put $\Phi^{p}_E=J_{S,E}\Phi_EJ_{T,E}^{-1}$ and $\beta^p_{F/E}=(\Phi^p_F j_{T,F/E})\circ J_{S,F}(\beta_{F/E})\circ j_{S,F/E}^{-1}$, all at the transported object. Since the $j$ respect identities, associators and shifts, the identity, associator and shift equations assumed for $\beta$ give those of [prop-weil-pbc-scalar-extension] for $\beta^p$. Apply [prop-weil-pbc-descent-functors] to $(\Phi^p_E,\beta^p_{F/E})$: it gives an exact $\Phi^p:\mathcal P_T\to\mathcal P_S$, represented on $u$ by $\beta^{p,-1}_{M/F}\circ\Phi^p_M(u)\circ\beta^p_{M/E}$, and descent of compatible transformations and their equations by the same formula. Then $\Phi=J_S^{-1}\Phi^pJ_T$ is an exact functor $\mathcal C_T\to\mathcal C_S$, as a composite of exact functors. Since $J_T,J_S$ conjugate common-stage arrows by the same $j$, these cancel, and $\Phi$ has value $(E,\Phi_EK)$ on $(E,K)$ and is represented on $u:T^{\mathrm{sf}}_{M/E}K\to T^{\mathrm{sf}}_{M/F}L$ by $\beta_{M/F}^{-1}\circ\Phi_M(u)\circ\beta_{M/E}$. Transformations and their equations transport the same way. This supplies all of the requested functor and transformation descent, with the given comparisons.

Cited statements: lem-fd-rational-coefficient-category-comparison, prop-weil-pbc-descent-functors, prop-weil-pbc-scalar-extension, def-weil-rationalization-karoubi, def-weil-algebraically-closed-coefficients, def-weil-pbc-rational-category, def-weil-pbc-qbar-category.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Clause (1): prop-weil-pbc-descent-functors.

### Original step 10 → lem-sf-package-common-stage-transport

Apply [thm-weil-pbc-idempotent-complete-triangulation] to $\mathcal P_T$: it is an idempotent-complete ordinary triangulated category, and every finite-stage embedding $j^{\mathrm{pbc}}_E:D^b_c(T,E)^{\mathrm{pbc}}\to\mathcal P_T$ is exact. By [lem-fd-rational-coefficient-category-comparison] (hypotheses checked in step 9), $J_T:\mathcal C_T\to\mathcal P_T$ is an exact equivalence, exact also in the reverse direction, preserving shifts and common-stage distinguished triangles in both directions and identifying the finite-stage inclusions: $J_Tj^{\mathrm{sf}}_E\cong j^{\mathrm{pbc}}_EJ_{T,E}$. Hence the triangulated category $\mathcal C_T$ is idempotent complete (an idempotent $e$ of $\mathcal C_T$ splits because $J_T(e)$ splits in $\mathcal P_T$ and $J_T$ is an equivalence), and $j^{\mathrm{sf}}_E\cong J_T^{-1}j^{\mathrm{pbc}}_EJ_{T,E}$ is a composite of exact functors, hence exact. These are properties of the literal common-stage category $\mathcal C_T$; no Karoubi envelope is inserted. Together with steps 8–9 this proves the remaining exact common-stage realization assertions.

Cited statements: thm-weil-pbc-idempotent-complete-triangulation, lem-fd-rational-coefficient-category-comparison.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Clause (1): thm-weil-pbc-idempotent-complete-triangulation.

## Historical returned report (not current certification)

# Repair report: lem-sf-package-coefficient-domain-realization

## Files written

- `dag/nodes/sec-six-functors/lem-sf-package-coefficient-domain-realization.json`: unchanged statement, three-step assembly (1403 characters).
- `dag/nodes/sec-six-functors/lem-sf-package-finite-domain-comparisons.json`: statement-only, unsplit, no Mathlib match; old steps 1–4 (2148 characters).
- `dag/nodes/sec-six-functors/lem-sf-package-adic-field-domain-comparisons.json`: statement-only, unsplit, no Mathlib match; old steps 5–8 (2819 characters).
- `dag/nodes/sec-six-functors/lem-sf-package-common-stage-transport.json`: statement-only, unsplit, no Mathlib match; old steps 9–10 (3175 characters).
- `citations.json`: one verbatim statement quotation for each of the three assembly citations.
- `original-citations.json`: complete verbatim statement evidence for every citation of the retained ten-step argument; handoff material only, not new-node proof dependencies.
- `report.md`, `searches.jsonl`, sandbox-only `write_repair.py`.

Three new nodes; zero Mathlib leaves. No Lean files, compilers or build commands.

## Attachments

None. Exact tag and notion searches in `lean/WeilConjectures` found no declaration giving the entire item or any of these three compound obligations. The finite `AlgebraicGeometry.Etale.sixOperationsPackage` at SixFunctors/Etale/Derived/Package.lean:224 has only finite coefficients and still has a sorry in its package proof. DerivedHom.lean:61 gives only part of the finite obligation, on a different site, without its quotient comparison or the other operations. ScalarExtension.lean supplies only scalar-extension exactness. None is an attachment of these nodes.

## WANTED

None. All sources used are locally present.

## Problems found and repairs

The return requires spreading the 8142-character proof, keeping the statement, adding at least two comparable unsplit nodes, and leaving at most 3000 characters in the item's proof. This repair adds three independent obligations carrying 2148, 2819 and 3175 characters of the original argument, respectively. Every original argument is reproduced verbatim below with its destination, source and citations; no argument has been erased or blurred. The work is distributed rather than transferred wholesale to one child. The new nodes have complete statements, empty proof/proof_deps, null proof_origin, and status unsplit, so other workers can begin their proofs independently. This explicit work-spreading instruction governs the extraction of these assembly subarguments. The statement of the item is byte-for-byte unchanged.

The sandbox initially contained only dispatcher marker files. I recovered the item from the current shared repository, including the maintainer's corrected steps 4 and 9–10, and read its Q128 report. The retained report from that delivery is copied below as historical handoff, not as the present certification. The old review's site-perfect evaluation-isomorphism citation and distinction between SF and PBC coefficient constructions are preserved in the new obligations and their handoffs. No unit or chapter route changes, no statement dispute, and no unit realization edits were needed.

## What remains unfinished

The proofs of the three new statement-only nodes are deliberately left to later stage-1 workers, as the return requires. This one-level assembly is complete and awaits the required delivery checks and maintainer review.

## Not duplicates

lem-sf-package-finite-domain-comparisons vs thm-sf-ctf-stability: the stability theorem supplies the finite restrictions and sharp bound, but does not assert the canonical evaluation isomorphism of site-perfect duality; the new obligation also fixes the quotient comparison as its unique evaluation transpose. It carries old steps 1–4 together, not just the theorem's restriction clauses.
lem-sf-package-finite-domain-comparisons vs thm-coef-finite-hom: that result supplies quotient comparisons only; the new obligation also assembles preservation for pullback, tensor and both direct images, general Hom bounds and site-perfect evaluation duality.
lem-sf-package-finite-domain-comparisons vs lem-sfb-ringed-site-perfect-duality: that result is abstract perfect duality, without constructibility, geometric bounds, direct images or arbitrary finite-Tor quotient comparisons.
lem-sf-package-adic-field-domain-comparisons vs cor-coef-integral-internal-hom: that result covers integral Hom and reductions only; the new obligation includes completed pullback/tensor, both direct images on the actual tower, field passage and exact scalar extension.
lem-sf-package-adic-field-domain-comparisons vs lem-fix-operation-reduction: compatibility on stated bounded domains does not prove that those domains are preserved; the new obligation retains the three independent integral preservation theorems and general Hom preservation.
lem-sf-package-adic-field-domain-comparisons vs lem-coef-rational-operations: that result identifies rational Hom and exceptional inverse image, not integral preservation, uniform residue Tor control or exactness of field extension.
lem-sf-package-common-stage-transport vs prop-weil-pbc-descent-functors: that result descends only on the PBC category; the new obligation proves descent on the SF category via the coherent J comparisons and also transfers triangulation/retract closure and exact embeddings.
lem-sf-package-common-stage-transport vs lem-fd-rational-coefficient-category-comparison: the comparison supplies J and j, not descent of arbitrary compatible functor families or idempotent completeness.
lem-sf-package-common-stage-transport vs lem-weil-qbar-idempotent-complete: that node supplies retract closure only; the new obligation includes coherent functor/transformation descent with the literal representative formula and exact finite-stage embeddings. The old proof's comparison route is retained.
lem-sf-package-common-stage-transport vs lem-sf-adic-qbar-constructible-realization: that result compares the common-stage category with a native module presentation and conditional Hom evaluation; it does not descend arbitrary exact families through the SF/PBC comparison.

I searched the whole DAG by finite-Hom/quotient, completed-operation, rational-evaluation and common-stage/equivalence patterns, and the whole imported blueprint with blueprint_refs search for coefficient domain, finite Hom, integral preservation, rational operations, descent functors, site-perfect, coefficient passage, common-stage, and idempotent-complete. No existing node gives any entire new obligation. The broader parent prop-functor-package and the item itself cannot be used to prove their own extracted children. All new names were absent from DAG and project-source searches. New sources cite the specific blueprint passage; no unrelated Stacks tag or forbidden SGA source is introduced.

## Mathlib searches

All new-node queries ran with the required Q140/item msearch command, with two distinct semantic phrasings for each area, LeanSearch, Loogle, and whole-Mathlib grep. Exact query strings and actual top hits are recorded in each node and searches.jsonl. The integral/field node records both areas' searches. All services responded successfully. I read the returned signatures: underived sheaf evaluation and pullback, light condensed monoidal structures, ordinary module adic completion, constructible subsets and generic exact/idempotent categorical interfaces do not state these constructible derived assertions. I opened the relevant Mathlib pullback definitions at Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:53 and :60, the triangulated-functor interface at CategoryTheory/Triangulated/Functor.lean:186, the constructible-subset grep hits, and Idempotents/Basic.lean:163. The latter is a useful generic ingredient but does not supply the coefficient descent theorem; none of the new obligations is a one-line specialization of a hit.

## Review by Q140

I read GOAL, the worker brief, stage-1 contract, the three levels in SETUP, the complete B–E delivery-error sections (including the merged copy), and the chapter/unit records. For the item and each new node I read the main-20261015 prop-functor-package statement and proof: the opening names finite Hom, its coefficient comparison, integral Hom and rational operations; clause (1) names exact scalar extension, descent, and idempotent-complete triangulation. The extraction serves exactly these passages. I read every statement used by all ten retained steps, not just their proofs or metadata. The original-citations file records that evidence, while citations.json records the exact three statements the new assembly uses.

Assembly step 1 cites the finite node, whose statement explicitly gives all finite restrictions, the general bound, the unique evaluation-transpose quotient map, and the conditional sharper interval/evaluation isomorphism. Its hypotheses exactly match the item: same field, positive indices, separated finite-type f and schemes, and finite-Tor inputs. The site-perfect hypothesis is retained only for the extra formula/bound. Original steps 1–4 below retain the distinct stability, general Hom, quotient, and perfect-duality arguments. In particular, the perfect-duality statement really gives the evaluation isomorphism, whereas the stability statement's warning about the formula alone would not give it.

Assembly step 2 cites the adic/field node. Its statement specifies the completed coefficient sheaf, derived completeness and one interval for all reductions, the compactification tower with its actual quotient/restriction-of-scalars maps, general integral Hom, evaluation reductions, field operation values and exact scalar extension. Original steps 5–8 retain the separate completed pullback/tensor, ordinary direct image and compact-support preservation statements; residue Tor control supplies uniform Tor intervals but never site-perfectness. The integral Hom corollary states the evaluation-defined comparison for arbitrary integral inputs. The coefficient compatibility lemma expressly mentions rationalization and common-stage passage, and the rational-operations lemma identifies Hom while preserving evaluation. Scalar-extension exactness is a theorem for the item's own raw rationalized categories. Thus no assertion of completeness is inferred from boundedness alone, and no merely named operation is used as a preservation theorem.

Assembly step 3 cites the common-stage transport node. Its statement gives exactly the functor descent, transformation/equation descent, ordinary triangulation, retract closure and exact embeddings the item needs. All beta equations are hypotheses, not assumed conclusions. Original steps 9–10 retain the J/j construction between the two coefficient conventions, conjugation of the family, the beta formula, the PBC descent application, cancellation of j, and transport back. I checked the directions against the comparison statement: j goes from J_F T_sf to T_pbc J_E, beta goes from T_S Phi_E to Phi_F T_T, and the representative ends with beta inverse at its target. The comparison theorem identifies shifts/triangles in both directions and finite-stage embeddings; the PBC triangulation theorem actually gives idempotent completeness and exactness of its embeddings. The finite-type schemes here are noetherian and finite-dimensional with ell invertible, as required for J. The new node and its handoff keep these constructions distinct, with no inserted Karoubi completion.

I tested the new statements at n=m=1, identity maps, E=F, point schemes, empty schemes and zero complexes. The point case d=0 yields the usual difference interval. For the origin of the affine line, the sharp interval is unavailable for i_*A unless site-perfectness is supplied: the old stability counterexample remains in the handoff. Empty schemes admit the nonnegative bound zero. The descended representative formula has the correct source/target for different fields E,F; identity field extension uses the unit equations, and compatible transformations use the same coherence. The residue Tor assertion is for derived reductions over the completed integral sheaf, not naive quotient sheaves of arbitrary discrete modules.

Against B–E, each new statement introduces its objects and cites the definitions it uses, with readable single-escaped TeX. The new nodes are not proofs in disguise: all old argument is in this report and their proof arrays are empty. The three independent obligations are comparable in inherited work size and none restates the entire item. The parent has only three theorem applications; no parent step is over 2000 characters. All uses are in proof_deps, and every parent citation has its verbatim quotation. The original same-unit/off-unit tool uses are retained in the handoff for subsequent workers; the parent now cites only its three same-unit children. No proof dependency was inserted into a new unsplit node. No repository or launcher file was edited, and no git or local checker command was run.

## Complete retained argument and assignment

### Original step 1 → lem-sf-package-finite-domain-comparisons

At each $A_n$, apply clauses (i), (ii), (iii), and (iv) of [thm-sf-ctf-stability] to the given $f$ and the finite-Tor inputs. These respectively restrict $Lf^*$, $\otimes^L$, $Rf_*$, and $Rf_!$ to the displayed finite-stage categories. Its hypotheses are exactly separated finite-type morphisms between separated finite-type schemes over the fixed $k$, with $\ell\ne p$; they hold here for every $n\ge1$.

Cited statements: thm-sf-ctf-stability.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Opening sentence, proved constructible domains; stability clauses (i)–(iv).

### Original step 2 → lem-sf-package-finite-domain-comparisons

For $K,L\in\mathcal C_{X,A_n}$, [cor-weil-finite-constructible-hom] gives bounded constructibility and finite Tor amplitude of $R\mathcal Hom_{A_n}(K,L)$, on the small pro-etale site used by the operation datum. With input intervals $[a,b]$, $[c,e]$ and any integer $d\ge0$ satisfying $\dim X\le d$, its stated interval is precisely $[c-b-2d,e-a+2d]$. This proves the general finite-stage Hom restriction and the asserted dimension-dependent bound.

Cited statements: cor-weil-finite-constructible-hom.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Opening sentence: cor-weil-finite-constructible-hom.

### Original step 3 → lem-sf-package-finite-domain-comparisons

Apply [thm-coef-finite-hom] with $A=A_n$, $B=A_m$ and $M=L$. The hypotheses $n\ge m\ge1$ and $K,L\in D^b_{ctf}(X,A_n)$ are those of the item. The resulting isomorphism is exactly the displayed finite coefficient comparison. The theorem characterizes its arrow as the unique tensor–Hom transpose of scalar extension of evaluation; thus the comparison here is that specified arrow, not an arbitrarily chosen isomorphism.

Cited statements: thm-coef-finite-hom.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Opening sentence: coefficient comparison thm-coef-finite-hom.

### Original step 4 → lem-sf-package-finite-domain-comparisons

When the first input $K\in D^b_{ctf}(X,A_n)$ is site-perfect in the sense of [def-weil-site-perfect-complex], it is locally on the small pro-etale site a bounded complex of direct summands of finite free $(A_n)_X$-modules, i.e. perfect in the sense of [lem-sfb-ringed-site-perfect-duality] for the ringed site $(X_{\mathrm{proet}},(A_n)_X)$. That lemma gives the canonical evaluation isomorphism $K^\vee\otimes^L_{A_n}L\xrightarrow{\sim}R\mathcal Hom_{A_n}(K,L)$ with $K^\vee=R\mathcal Hom_{A_n}(K,(A_n)_X)$, for every $L$. Clause (ii) of [thm-sf-ctf-stability] gives, under exactly this extra hypothesis, the sharper Tor interval $[c-b,e-a]$. No application of either result to a merely constructible finite-Tor first input is made; that case was covered instead by step 2 (and the origin of $\mathbf A^1$ in clause (ii) shows the sharper bound fails without site-perfectness).

Cited statements: thm-sf-ctf-stability, lem-sfb-ringed-site-perfect-duality, def-weil-site-perfect-complex.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Opening domains and site-perfect qualification in prop-functor-package; stability clause (ii).

### Original step 5 → lem-sf-package-adic-field-domain-comparisons

At $R$, [lem-pur-integral-operations-preserve-constructible] restricts the completed pullback and completed tensor to the derived-complete integral constructible categories, with their stated finite reductions. Apply [lem-sf-integral-direct-image-constructible] to obtain the same restriction for the specified $Rf_*$. Apply [lem-sf-integral-compact-support-constructible] to the specified compactification reduction tower defining $Rf_!$. That theorem applies to its derived limit with exactly the quotient/restriction-of-scalars transitions, and proves completeness and one finite cohomological interval for all its reductions. All three results allow our finite-type $k$-schemes with $\ell$ invertible; the compact-support result requires the separated finite-type $f$ assumed here. These are preservation theorems for the actual completed operations, so the definition of the integral category alone is not being used to assert preservation.

Cited statements: lem-pur-integral-operations-preserve-constructible, lem-sf-integral-direct-image-constructible, lem-sf-integral-compact-support-constructible.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Opening integral preservation; completed pullback/tensor and the two direct images.

### Original step 6 → lem-sf-package-adic-field-domain-comparisons

For integral $K,L$, [lem-coef-integral-residue-tor] supplies uniform finite-level Tor intervals from the bounded residue reductions; it does not assert site-perfectness. Now [cor-coef-integral-internal-hom] applies to all $K,L\in D^b_c(X,R)$ and places their ambient internal Hom in that same category. Its canonical evaluation-defined reduction comparison gives the required formula from $R$ to every $A_n$. Consequently this step uses neither a site-perfect model for arbitrary constructible objects nor an inference of completeness from levelwise boundedness alone.

Cited statements: lem-coef-integral-residue-tor, cor-coef-integral-internal-hom.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Opening integral internal Hom: cor-coef-integral-internal-hom.

### Original step 7 → lem-sf-package-adic-field-domain-comparisons

Use the raw rationalization of [def-weil-rationalization-karoubi] and the finite-representative common-stage construction of [def-weil-algebraically-closed-coefficients]. By [lem-fix-operation-reduction], the pullback, tensor, and two direct-image operations and their coefficient comparisons commute with rationalization and common-stage scalar extension. Thus their field values are the specified coefficient-passage values of the integral outputs established in step 5, and belong to the displayed field categories. The same result supplies scalar compatibility for internal Hom; [lem-coef-rational-operations] identifies the rationalized integral internal Hom with the field internal Hom and explicitly preserves evaluation, including under finite scalar extension. Applied to the integral outputs of step 6 and then to finite representatives, these identifications give internal-Hom restriction and the required evaluation identification at both field stages.

Cited statements: def-weil-rationalization-karoubi, def-weil-algebraically-closed-coefficients, lem-fix-operation-reduction, lem-coef-rational-operations.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Opening field passage: lem-coef-rational-operations; basic operation coefficient passage.

### Original step 8 → lem-sf-package-adic-field-domain-comparisons

For each finite inclusion $E\subset F$, apply [lem-weil-scalar-extension-exact-triangulated] with $L=F$ to $T$ (and to $S$ when needed). It states that this scalar-extension functor on the rationalized constructible categories preserves shifts and distinguished triangles. This is exactly the finite coefficient-field exactness asserted here.

Cited statements: lem-weil-scalar-extension-exact-triangulated.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Clause (1): lem-weil-scalar-extension-exact-triangulated.

### Original step 9 → lem-sf-package-common-stage-transport

The item's finite stages $D^b_c(-,E)$ and common-stage category $\mathcal C_T$ are those of [def-weil-rationalization-karoubi] and [def-weil-algebraically-closed-coefficients], while [prop-weil-pbc-descent-functors] is stated for the stages of [def-weil-pbc-rational-category] and the pair category $\mathcal P_T$ of [def-weil-pbc-qbar-category]. Our separated finite-type $k$-schemes $T,S$ are noetherian, finite-dimensional, with $\ell$ invertible, so [lem-fd-rational-coefficient-category-comparison] gives exact equivalences $J_{W,E}$ ($W=T,S$), the identity on the common integral objects and on localized Hom groups, with scalar comparisons $j_{W,F/E}:J_{W,F}T^{\mathrm{sf}}_{F/E}\simeq T^{\mathrm{pbc}}_{F/E}J_{W,E}$ respecting identities, shifts and the associators, and the induced exact equivalences $J_W:\mathcal C_W\simeq\mathcal P_W$ which identify finite-stage inclusions, shifts and distinguished triangles. Put $\Phi^{p}_E=J_{S,E}\Phi_EJ_{T,E}^{-1}$ and $\beta^p_{F/E}=(\Phi^p_F j_{T,F/E})\circ J_{S,F}(\beta_{F/E})\circ j_{S,F/E}^{-1}$, all at the transported object. Since the $j$ respect identities, associators and shifts, the identity, associator and shift equations assumed for $\beta$ give those of [prop-weil-pbc-scalar-extension] for $\beta^p$. Apply [prop-weil-pbc-descent-functors] to $(\Phi^p_E,\beta^p_{F/E})$: it gives an exact $\Phi^p:\mathcal P_T\to\mathcal P_S$, represented on $u$ by $\beta^{p,-1}_{M/F}\circ\Phi^p_M(u)\circ\beta^p_{M/E}$, and descent of compatible transformations and their equations by the same formula. Then $\Phi=J_S^{-1}\Phi^pJ_T$ is an exact functor $\mathcal C_T\to\mathcal C_S$, as a composite of exact functors. Since $J_T,J_S$ conjugate common-stage arrows by the same $j$, these cancel, and $\Phi$ has value $(E,\Phi_EK)$ on $(E,K)$ and is represented on $u:T^{\mathrm{sf}}_{M/E}K\to T^{\mathrm{sf}}_{M/F}L$ by $\beta_{M/F}^{-1}\circ\Phi_M(u)\circ\beta_{M/E}$. Transformations and their equations transport the same way. This supplies all of the requested functor and transformation descent, with the given comparisons.

Cited statements: lem-fd-rational-coefficient-category-comparison, prop-weil-pbc-descent-functors, prop-weil-pbc-scalar-extension, def-weil-rationalization-karoubi, def-weil-algebraically-closed-coefficients, def-weil-pbc-rational-category, def-weil-pbc-qbar-category.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Clause (1): prop-weil-pbc-descent-functors.

### Original step 10 → lem-sf-package-common-stage-transport

Apply [thm-weil-pbc-idempotent-complete-triangulation] to $\mathcal P_T$: it is an idempotent-complete ordinary triangulated category, and every finite-stage embedding $j^{\mathrm{pbc}}_E:D^b_c(T,E)^{\mathrm{pbc}}\to\mathcal P_T$ is exact. By [lem-fd-rational-coefficient-category-comparison] (hypotheses checked in step 9), $J_T:\mathcal C_T\to\mathcal P_T$ is an exact equivalence, exact also in the reverse direction, preserving shifts and common-stage distinguished triangles in both directions and identifying the finite-stage inclusions: $J_Tj^{\mathrm{sf}}_E\cong j^{\mathrm{pbc}}_EJ_{T,E}$. Hence the triangulated category $\mathcal C_T$ is idempotent complete (an idempotent $e$ of $\mathcal C_T$ splits because $J_T(e)$ splits in $\mathcal P_T$ and $J_T$ is an equivalence), and $j^{\mathrm{sf}}_E\cong J_T^{-1}j^{\mathrm{pbc}}_EJ_{T,E}$ is a composite of exact functors, hence exact. These are properties of the literal common-stage category $\mathcal C_T$; no Karoubi envelope is inserted. Together with steps 8–9 this proves the remaining exact common-stage realization assertions.

Cited statements: thm-weil-pbc-idempotent-complete-triangulation, lem-fd-rational-coefficient-category-comparison.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md; Clause (1): thm-weil-pbc-idempotent-complete-triangulation.

## Historical Q128 report (retained without alteration)

# Stage-1 report: lem-sf-package-coefficient-domain-realization

## Files written

- `dag/nodes/sec-six-functors/lem-sf-package-coefficient-domain-realization.json`: statement, now split into ten short proof steps. Statement unchanged. Mathlib verdict: no match for the complete coefficient-domain and common-stage package.
- `citations.json`: sixteen step/node entries with verbatim quotations from the current cited statements.
- `report.md`: this report. `searches.jsonl` records the five real search-command invocations. `write_split.py` is a sandbox-only authoring helper, not a DAG delivery file.

There are zero new nodes and zero new Mathlib leaves. The sandbox had no previous item, report, split, or searches to recover. Existing non-worker fields, including the source, blueprint ancestry, and creation record, were retained. The statement dependencies now explicitly name completion, rationalization, common-stage coefficients, Tor amplitude, and dimension in addition to the operation datum and site-perfectness. Proof dependencies are exactly the union of step uses.

## Attachments

None. I searched the project `lean/WeilConjectures/` for the exact blueprint tag, coefficient-domain terminology, six-operation package names, and common-stage/exactness terminology. The finite-coefficient `AlgebraicGeometry.Etale.sixOperationsPackage` is only part of this item's assertion; its finite-coefficient statement does not supply this integral/rational/common-stage package. The pro-etale bounded-constructible module-object source explicitly lists sorried preservation inputs, and the common-stage triangulation instances alone do not prove the other clauses. None is an exact attachment of the whole item. No compiler, Lake command, or Lean-writing operation was run.

## WANTED

None. The sources used are present locally.

## Problems found and corrections

The unsplit item itself has a correct statement against the current blueprint. Its proof and proof dependencies were empty. I supplied the assembly, using existing nodes rather than making a new node for each clause. In particular, the finite comparison for arbitrary constructible finite-Tor first arguments comes from `thm-coef-finite-hom`, not from the site-perfect-only elementary comparison in `lem-fix-operation-reduction`.

The latter's coefficient-passage clauses are sufficient for field identification, but its mere mention of operations is not integral preservation. Step 5 therefore separately cites the three existing completed-operation preservation results. Its compact-support citation applies to the actual inverse system, including its quotient and restriction-of-scalars transitions. The proof never claims that an arbitrary bounded tower is effective just because its terms are constructible.

No statement dispute or change of the unit/chapter route was needed. The item is not the unit key theorem; no unit realization fields were changed.

## What remains unfinished

Nothing in this one-level split. The existing dependencies retain their own proof obligations. This delivery is stage 1 only.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs to distinguish. I searched the entire DAG by the source-named ids and coefficient/Hom/common-stage concepts, and used the existing results. `tools/blueprint_refs.py ancestor` gives `prop-functor-package`. Blueprint searches for `coefficient-domain` and `common-stage realization` found no imported node stating the entire item; the `descent-functors` search located the existing descent proposition and its applications. The parent `prop-functor-package` is strictly broader, with seven clauses; it cannot be cited to prove its own realization child. The existing stability theorem supplies finite preservation and the site-perfect qualification, but does not subsume the general exact-functor descent assertion of this item.

## Mathlib searches

All searches were run through the required `batch2/msearch.py Q128 lem-sf-package-coefficient-domain-realization` command; exact query strings and actual results are in the node and `searches.jsonl`. I ran LeanFinder with two distinct phrasings, Loogle for `CategoryTheory.Functor.IsTriangulated`, grep for constructible/rational/Tor and adic scalar terminology, and LeanSearch for the whole coefficient-passage package. All five services/commands returned successfully; none is described as unavailable or recorded without an invocation.

I read every returned hit's signature/output. LeanSearch found underived sheaf pullback/pushforward adjunctions and condensed locally constant functors. Loogle found the triangulated-functor interface and transport lemmas, which assume the categories and exactness data. LeanFinder found condensed categorical structures, internal projectivity, ordinary finite-dimensional internal Hom, and unrelated exact sequences. The grep hits concern adic algebra, constructible subsets, and faithfully-flat module descent. I opened the Mathlib triangulated-functor source, condensed AB source, and ModuleCat descent source; none supplies constructible derived preservation, these evaluation-defined coefficient comparisons, or the full common-stage package. Thus the item is not a Mathlib leaf, although its generic categorical ingredients may have their own leaves lower in the existing DAG.

## Review by Q128

I read the standing stage-1 brief, the complete B–E delivery-error checklists (including the merged checklist), the worker and stage documents, GOAL, the three blueprint levels in SETUP, and the item's chapter/unit records. I read the current `main-20261015` parent statement and proof, not only the historical master source path in the node. The parent proof expressly names the finite Hom, coefficient-change, integral Hom, rational operation, exact scalar-extension, descent, and idempotent-complete triangulation results used here. I also read their current blueprint statement files, the current stability proof, and the rational-operations proof. For the integral operation background I read Bhatt–Scholze, local PDF pp. 49–57: 6.5.5, 6.5.9, 6.5.11, 6.7.2, 6.7.6–6.7.7, and 6.7.13. These supply background; every non-elementary assertion in the item is still cited as a DAG statement. No prohibited SGA source is used. There are no new-node sources to certify.

I opened and read the statement of every cited node. In detail:

1. `thm-sf-ctf-stability` (i)–(iv) really states the four finite-stage restrictions, including nonproper ordinary direct image. The field is the fixed algebraic closure of the finite field, the coefficient exponent is prime to its characteristic, and both scheme and morphism separated/finite-type hypotheses are supplied by the item.
2. `cor-weil-finite-constructible-hom` says preservation for both general finite-Tor inputs and gives exactly `[c-b-2d,e-a+2d]`. It is a theorem on either finite site, so its pro-etale version is available without a change of category. The nonnegative integer bound also permits the empty scheme.
3. `thm-coef-finite-hom` says the comparison is an isomorphism and identifies it as the unique transpose of changed evaluation. Its quotient ring map and inequalities match `n >= m >= 1`. This is stronger than merely knowing the two Hom objects are isomorphic.
4. The stability theorem's clause (ii) separately says the sharper bound and tensor-dual formula for a site-perfect first input. It does not identify arbitrary constructible finite-Tor inputs with site-perfect ones. The item retains exactly this extra hypothesis.
5. `lem-pur-integral-operations-preserve-constructible` gives completed pullback/tensor membership and their reductions. `lem-sf-integral-direct-image-constructible` gives ordinary pushforward membership with a reduction interval independent of n. `lem-sf-integral-compact-support-constructible` gives membership of the actual compact-support tower's derived limit, including completeness and uniformly bounded constructible reductions. The latter requires a compactification of a separated finite-type morphism, already used by the operation datum. These statements allow our field and all the stated morphisms. I do not take their proofs as extra interfaces or infer a preservation theorem from a definition node.
6. `lem-coef-integral-residue-tor` gives uniform Tor intervals from residue cohomology and explicitly warns that this does not mean site-perfectness. `cor-coef-integral-internal-hom` states membership of the ambient integral Hom for arbitrary integral constructible inputs and the canonical evaluation-defined reduction isomorphism for every n. This covers the item's specified integral category with its single cohomological interval.
7. The two coefficient definition nodes identify rational objects and common-stage representatives with exactly the item's categories. `lem-fix-operation-reduction` expressly says the same operations/comparisons commute with rationalization and common-stage scalar extension and preserve evaluation. `lem-coef-rational-operations` expressly identifies rational internal Hom and preserves evaluation, also under finite scalar extension. Therefore the already-preserved integral outputs yield field outputs with the specified operation, including the Hom identification. This step does not appeal to its source proof's completion-adjunction argument as if that argument were another theorem statement.
8. `lem-weil-scalar-extension-exact-triangulated` has precisely the finite field-extension functor in question, including shift and distinguished-triangle preservation. The scheme may be arbitrary, so our finite-type schemes meet its hypotheses.
9. `prop-weil-pbc-descent-functors` has exactly the supplied coherent scalar comparisons and exact-functor hypotheses. I wrote out its representative formula, with beta inverse at the target, and used its explicit final assertion for compatible transformations and their equations. This does not claim descent for incoherent or merely objectwise functors.
10. `thm-weil-pbc-idempotent-complete-triangulation` states the required ordinary triangulation, idempotent completeness, and exactness of every finite-stage embedding on the common-stage category itself. No new Karoubi completion is inserted.

I checked the zero objects, identity morphisms, n=m, and identity field extension E=F: the cited comparisons specialize with their stated unit equations and do not need strict inequalities. At a point (d=0) the general Hom bound reduces to the expected difference interval. On a positive-dimensional scheme the closed point in the affine line is the stability statement's example showing why the dimension-free bound needs site-perfectness; the split does not accidentally assert that stronger bound for it. Empty schemes and zero complexes do not require a negative dimension bound. I checked the order of the three factors in the descended morphism formula against the proposition's displayed arrow. Equations of transformations are taken from the proposition's statement, not deduced by an unproved faithfulness assertion about stage embeddings.

Against B–E: no new nodes, hollow data, relabelled clauses, or hidden statement-only proof sketches were introduced; the item is a complete assembly of independently existing results. Each of the sixteen step citations has its verbatim evidence in `citations.json`. Every step is marked non-elementary because it invokes a theorem, and every substantive claim is in one of the cited statements. The longest step is 964 characters, so none exceeds the long-step threshold or conceals an extracted lemma. Generic uses from other units are declared with individual reasons in `split_report.tool_uses`; they follow the existing package route. I traversed dependencies before writing to ensure none of the major cited results reaches the item or its package parent. The required server dry run below is the authoritative global cycle and preflight check. I did not edit the repository or any launcher script.

## Validation and delivery

The required server preflight is run with `deliver.py --no-push`; its result and the subsequent delivery commit are reported by the command output. No local DAG/preflight checker, Lean compiler, or build tool is used.


## Validation and delivery for this repair

The final server dry run and push are performed with the prescribed deliver.py commands; their output is the authority for the current repair. Historical validation above is not claimed as validation of this repair.

## Repaired server-check wording

The first repaired-head preflight rejected the context phrase in step 8. Replaced it by the explicit categories $D^b_c(T,E)\to D^b_c(T,F)$. No statement, dependency or argument changed.

## Current repair validation

Server preflight passed for the repaired split: `OK (not pushed)` at `6bd50ab478f`. This included the DAG and split checks. Parent assembly has 2433 characters; statement and stmt_deps remain unchanged. Final report-only bookkeeping is followed by a final dry run and direct delivery.
