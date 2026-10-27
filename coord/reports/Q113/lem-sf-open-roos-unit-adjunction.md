# Q113: repair of lem-sf-open-roos-unit-adjunction

## Files written

- dag/nodes/sec-six-functors/lem-sf-open-roos-unit-adjunction.json: same live statement and statement dependencies; six-step assembly, 2272 characters.
- dag/nodes/sec-six-functors/lem-sf-quotient-completion-actual-reflector.json: statement-only lemma, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors/lem-sf-open-quotient-completion-unit-comparison.json: statement-only lemma, unsplit; no Mathlib match.
- citations.json: a verbatim statement quotation for every citation in every parent step.

## Attachments

None. The read-only WeilConjectures source has no exact finished declaration found by the blueprint id or by Roos/unit/reflector terminology. In lean/Sheaf/SixFunctors/OpenRoosUnitAdjunction.lean the project theorem WeilConjectures.OpenRoos.openRoosUnitAdjunction starts at line 183 and ends in sorry at line 261. It is not an attachment. No Lean was written or compiled.

## WANTED

None.

## Return repaired

D1/D2/C5: I removed the two rejected, unlanded sandbox package drafts from dag/nodes and retained their exact JSON as *.rejected.json outside that tree. Their proof, report, citations and logged search outputs are preserved in report-before-second-return.md, repair.py, search-*.txt and searches.jsonl. The returned report is historical, not the current split's justification. It incorrectly treated the four unrelated coefficient/geometry/reflection assertions as one argument, and it missed the existing immersion comparison. The current report supersedes those claims.

The current live eight-step proof and current live metadata were reread. Its statement and stmt_deps are retained exactly, including the additional statement metadata that landed after the earlier draft. Old coefficient Steps 1–3 stay in the parent as direct citations, with the stronger existing profinite coefficient inverse-image statement replacing the elementary projection calculation. The two new nodes isolate only old Step 4 and old Steps 5–6, respectively, precisely the arguments requested by the return. The second no longer includes extension, a second completion functor, or a completeness-preservation theorem. Extension preservation is now cited from lem-sf-integral-open-reduction-comparison, and complete-input restriction/completed comparison is cited from lem-sf-immersion-completed-pullback-comparison. The strict extension tensor and normalized lambda arguments in old Step 7 are retained below as the explanation of these existing citations, not rebranded as new work. The final full-subcategory adjunction proof remains elementary. Its cross-reference now names Step 5; no reference to obsolete Steps 6 and 7 remains.

The item has no statement dispute. The new statements do not assert the constant-coefficient results over the actual completed sheaf by substitution. They explicitly distinguish the actual quotient unit, intrinsic Koszul unit, and pulled augmented tower, and they state derived isomorphisms, not only cohomology identifications. The human count of two is met by two independent arguments; no waiver is requested.

## Sources and searches

I read stages/1-dag.md, the worker brief, the three blueprint levels in SETUP.md, GOAL.md, the chapter and unit of prop-sf-pf-coherence, and delivery-errors B–E in both copies of the consolidated file. The fixed unit route remains its open-factor base-change argument: full faithfulness and the section-normalized open unit. This item does not realize the entire unit and does not edit its record.

For the item, I read Stacks proetale.tex, Tag 099M (lemma-naive-completion), Tag 099N (lemma-pushforward-Noetherian-case, including proof of (5)), and Tag 09BN (lemma-open-immersion). I read algebraization.tex, Tags 099B (lemma-derived-completion) and 0A0E (lemma-derived-completion-koszul), including their proofs, for the first new node. Those ringed-site results give the Koszul reflector; its comparison to the completed-ring strict quotient unit is supplied by the existing completed-koszul-quotient-comparison, not by assuming a completed sheaf is a constant Noetherian ring. For the second new node I read 099N's tensor comparison and the existing ringed-topoi-derived-tensor-pullback statement (Stacks 0G7E/07A4 input), the exact-product strict-limit statement, and the definition of actual completed pullback. The additional normalization on arbitrary completed-ring inputs is agent-formulated, not claimed verbatim from 099N. Bhatt–Scholze, The pro-etale topology for schemes, printed pp.24–25, Proposition 3.5.1 and Definition 3.5.2, was reread with its constant-Noetherian-coefficient qualification and the following completed-coefficient discussion. No SGA source is used.

Before the narrower drafts, I searched the whole DAG for reflector, actual unit, open restriction, strict quotient, and the relevant tags, and used tools/blueprint_refs.py search for completion reflector, Roos, quotient completion, open Roos, actual quotient reflector and strict open augmentation. The ancestor is prop-sf-pf-coherence through lem-sf-pf-open-factor-coherence. No blueprint statement states either narrower completed-coefficient argument. I opened the closest matches, including the general Koszul reflector, unit-compatible completed Koszul comparison, Roos/intrinsic equivalence, open Roos restriction/extension comparisons, canonical open restriction model, pulled-reduction comparison, exact-pullback-counit normalization, and the separated-finite-type integral pullback normalizations. The Not duplicates section gives the precise distinctions.

The original searches were retained and read, then fresh searches were run because both new questions changed. Each new node has LeanFinder, LeanSearch, Loogle, and grep through the required unmodified msearch.py, plus a second LeanFinder phrasing. Exact queries and complete outputs are in repair2-*.txt and the append-only searches.jsonl; mathlib_searches contains those exact queries. All answered. AdicCompletion and its finite-module tensor formulas are ordinary ring-module completion results, not unbounded derived sheaf reflection; restrictFunctorIsoPullback concerns structure sheaves on the scheme's Zariski space, not the augmented quotient/Roos comparison; the sheafification and condensed adjunction hits do not contain either claim. No Mathlib leaf is asserted. The two new ids were searched in the DAG and the read-only source and did not already exist.

## Review by Q113

I checked the return against each changed statement and the cited statements themselves. The first new node is one reflector-transport argument: a unit-preserving isomorphism from Koszul completion to actual quotient completion carries complete output and its universal Hom bijection to the actual quotient augmentation. It does not package coefficient finiteness, geometry, or open operations. The second is one augmented restriction argument: the balanced tensor tower map, its natural descent, normalized product comparison, and ordinary-to-completed identification are all one comparison construction on arbitrary H. It does not package extension and it does not delegate the entire item to a clause block.

Parent Step 1 uses the DVR statement for domain/PID/nonzero uniformizer and finite residue field, and the finite-quotients statement for finiteness of every A_n. Finitely generated ideals in the PID prove Noetherianity. The nonzero t^n proves injectivity of multiplication and its cokernel is the stated quotient, so the finite-free resolution has exactly degrees [-1,0]. These facts verify every hypothesis in the cited adic datum, including perfectness and additive torsion.

Parent Step 2 uses finite-type-over-Noetherian for Noetherian V,W, locally-Noetherian-quasi-separated for the quasi-separated clause, and Noetherian-open-subscheme-Noetherian for quasi-compactness of each affine inverse image. The field is Noetherian and Spec(k) is quasi-compact. No intersection of two affines is assumed affine, and no separatedness of V,W is added.

Parent Step 3 uses profinite-coefficient-inverse-image for both ring isomorphisms and its two explicit projection/transition equations. Its hypothesis of finite rings is Step 1. The immersion-limit-preservation statement says exactly that module inverse image along the coefficient isomorphism is exact and preserves small limits, including products; an open immersion is a locally closed immersion. Countable-products-exact is stated for any ring sheaf, hence applies to B_V and B_W. These are direct uses, not a new coefficient lemma.

Parent Step 4 invokes the first new node on W and V. Its hypotheses are Step 1 and the fixed small-site/module universe convention. Its statement explicitly supplies complete output and the Hom bijection by precomposition with the actual eta, not an arbitrary isomorphism to a limit, and supplies exactly the Roos, intrinsic and unit criteria. The source argument retained below explains the nontrivial unit transport its future worker must prove.

Parent Step 5 invokes the second new node for the actual open restriction. The coefficient and exact-product identifications are those fixed in Step 3. Its statement supplies the strict tau and b, the formula rho=b lambda, both unit equations, and the comparison for arbitrary H; no completeness assumption has been slipped into that assertion. Complete-input restriction preservation and invertibility are then cited directly from immersion-completed-pullback-comparison, which states those facts for a locally closed immersion with exactly these coefficient identifications. Extension preservation is cited directly from integral-open-reduction-comparison, whose hypotheses are quasi-compactness (Step 2), invertibility of ell over k, and the same strict quotient completeness convention (Step 4). Its statement says j_!K is derived complete. No proof of either preservation claim is borrowed from inside a different node.

Parent Step 6 uses the exact-derived-adjunction definition for the localized original unit/counit and the open-tensor-normalization statement for the section identity under e^*e_!M=M. Because both complete categories are full and Step 5 verifies preservation, the same Hom bijections restrict. The written map calculation proves full faithfulness without an additional non-elementary fact. citations.json records a literal statement substring for all 15 citations, using full statements to keep qualifications visible.

For the new restriction statement I checked types: b has source Rlim(e^*Q_W(H)) and rho has source e^*C_W(H); alpha has source e^*H, so b alpha and rho e^*eta both land in C_V(e^*H). The quotient-unit map on each tensor is x tensor 1 and the transition takes its coefficient to the same 1. The signed Roos differential is (dx,(1-s)x-dy), and the product comparison is used on both summands. The unit's shifted component is zero. The arbitrary-input augmented formula is distinguished from the original completed functor, which its definition initially restricts to complete inputs. No comparison between unrelated triangulated cones is chosen.

Small cases: V empty gives the zero restriction and unique comparison; e=id gives identity tau and product comparisons; H=0 gives zero units and the unique Hom bijection; the first exponent n=1 has the same [R --t--> R] resolution and quotient unit. Shifts of unbounded representatives cause no new convergence or amplitude assumption, since both arguments use actual strict total limits and exact products. On already complete H both unit formulas give invertible ordinary-to-completed comparison; on arbitrary H only the natural rho is invertible, not eta. For the reflector, L=0 gives the unique-map bijection and an already complete H makes its actual unit invertible. These tests did not expose a false statement.

Every non-elementary fact in the parent is named in uses, and each is exactly present in the opened node's statement. Both new nodes are unsplit with no proof steps or proof dependencies. Parent proof length is 2272 characters; no step approaches the long-step threshold. Every notion in each new statement is introduced inline or names its node in stmt_deps; all blueprint fields have precise places. B1–B10, C1–C8, D1–D5 and E1–E7 were checked with these files open. The corrected sources, hypotheses, exact-unit typing and comparisons above are my mathematical review, not just a mechanical checklist.

## Retained argument for later workers

The old eight steps are retained verbatim below, with allocation updated to the repaired proof. Their content was not dropped to reduce the parent length.

### Old Step 1: parent Step 1, existing coefficient tools

The valuation ring $R$ is a PID and a domain, with finite residue field, by [lem-weil-l-adic-extension-integers-dvr]. Thus each ideal is finitely generated, so $R$ is Noetherian. By [lem-weil-valued-dvr-finite-quotients] every $A_n$ is finite. The additive group of $A_1$ is torsion because it is finite. Since $t\ne0$, multiplication by $t^n$ on $R$ is injective, its image is $(t^n)$, and its cokernel is $A_n$. Hence $0\to R\xrightarrow{t^n}R\to A_n\to0$ is a finite free resolution. This verifies every coefficient hypothesis of [def-weil-pbc-adic-coefficient-datum], including perfectness, for $(R,(t))$.

Source: literature/blueprint/master/blueprint/sec-nagata-compactification/sk-prop-nagata-sketch-comp-category/def-weil-finite-field-fiber.md, Coefficient datum, using the two cited DVR results; the Noetherian and two-term resolution deductions are elementary.

### Old Step 2: parent Step 2, existing geometry tools

The field $k$ is Noetherian (its only ideals are $0$ and $k$), and $\operatorname{Spec}k$ is quasi-compact. Applying [lem-weil-pbc-finite-type-over-noetherian] gives that $V,W$ are Noetherian; [lem-weil-pbc-locally-noetherian-quasi-separated] gives quasi-separatedness, so both are qcqs. For each affine open $T\subset W$, the open subscheme $T\cap V$ is Noetherian, hence quasi-compact, by [lem-weil-pbc-noetherian-open-subscheme-noetherian]. This is the affine-local definition that $e$ is quasi-compact.

Source: literature/stacks-project/morphisms.tex, Tag 01T6, lemma-finite-type-noetherian; properties.tex Tags 01OY, 01OW and 01OZ.

### Old Step 3: parent Step 3, existing coefficient tools

Use [lem-weil-proetale-weakly-etale-localization] to identify the site of $V$ with the slice over the open. Its constant-coefficient identification takes $a\in A_n$ to the same constant section. For the quotient $A_{n+1}\to A_n$, the two possible composites therefore agree on constant sections, hence agree as maps of constant sheaves. The inverse-image functor preserves limits and is exact by [lem-weil-pbc-proetale-immersion-limit-preservation]. Apply it to $B_W=\lim_n(A_n)_W$ to obtain $e^{-1}B_W=B_V$; the induced comparison is characterized by the equalities of all quotient projections. These are the coefficient identifications claimed. Countable products are exact for both completed ring sheaves by [lem-weil-proetale-countable-products-exact].

Source: literature/stacks-project/proetale.tex, Open localization and immersion limit preservation; coefficient identifications by the universal property of the limit. Countable-product exactness is the cited pro-etale product result.

### Old Step 4: new actual quotient reflector

For $T=W$ or $V$, let $\Lambda_T(H)$ be the Koszul completion on $B_T$ for the global section $t$. The ringed Koszul reflector [lem-weil-pbc-ringed-koszul-completion-reflector] says that $\Lambda_T(H)$ is locally derived $(t)$-complete and that its unit induces $\operatorname{Hom}(\Lambda_T(H),L)\simeq\operatorname{Hom}(H,L)$ for every locally complete $L$. The intrinsic product-fibre construction and this strict derived-limit Koszul construction agree, including their units: [lem-weil-strict-roos-comparison] identifies the product-fibre unit $(u_H,0)$ with the strict augmentation unit. By [lem-pur-roos-intrinsic-completeness-equivalence], intrinsic completeness is precisely the local completeness condition in the reflector theorem. Finally [lem-weil-pbc-completed-koszul-quotient-comparison] supplies a natural isomorphism $a_H:\Lambda_T(H)\xrightarrow{\sim}C_T(H)$ satisfying $a_H\kappa_H=\eta_H$. Therefore $C_T(H)$ is intrinsically complete. The bijection for $C_T(H)$ is explicitly $f\mapsto f\eta_H$: composing first with $a_H$ and then with $\kappa_H$ gives exactly this map. The same equivalence lemma identifies the Roos predicate, intrinsic completeness and invertibility of this specified $\eta_H$. This proves all reflector and predicate assertions on both sites.

Source: literature/stacks-project/algebraization.tex, Tags 099B, lemma-derived-completion, and 0A0E, lemma-derived-completion-koszul; proetale.tex Tag 099M. Completed-ring and actual-unit bridges are the cited nodes.

### Old Step 5: new augmented restriction comparison

Choose a flat-term K-flat representative $P\to H$ by [lem-pc-kflat-resolution]. By [lem-weil-pbc-ringed-topoi-derived-tensor-pullback], $e^*P$ is flat-term K-flat. On a slice object $T\to V$, restriction of $P\otimes_{B_W}(A_n)_W$ is canonically $(e^*P)\otimes_{B_V}(A_n)_V$: the tensor map sends $x\otimes a$ to the same tensor with its restricted coefficient, and its inverse is the same balanced tensor formula under the slice identifications. It commutes with $1\otimes(A_{n+1}\to A_n)$ and sends $x\mapsto x\otimes1$ to $x\mapsto x\otimes1$. Thus these maps give a comparison $\tau_H:e^*Q_W(H)_\bullet\xrightarrow{\sim}Q_V(e^*H)_\bullet$ of strict tower complexes, including the augmentations. Naturality is already an equality on tensors. The derived pullback theorem and the functorial reduction tower of [def-weil-pbc-adic-coefficient-datum] make the resulting comparison independent of representatives.

Source: literature/stacks-project/sites-cohomology.tex, Tags 0G7E, lemma-pullback-K-flat, and 07A4, lemma-pullback-tensor-product; strict slice tensor calculation.

### Old Step 6: new augmented restriction comparison; existing immersion result for complete inputs

Apply [lem-cbc-exact-product-functor-strict-limit] to the exact product-preserving functor $e^*$ from Step 3 and its termwise action on strict towers. Define $\rho_H=R\lim(\tau_H)\circ\lambda_{Q_W(H)}$. This is a natural isomorphism $e^*C_W(H)\to C_V(e^*H)$. In normalized Roos coordinates $H_M^q=(\prod M_n)^q\oplus(\prod M_n)^{q-1}$, $\lambda=\theta^{-1}\kappa e^*\theta$ with $\kappa$ the canonical product comparison on both summands. In particular, the augmentation clause of the cited lemma and the strict augmentation equality of Step 5 give the equality $\rho_H\,e^*\eta_H=\eta_{e^*H}$. If $H$ is complete, $e^*\eta_H$ is invertible and hence so is $\eta_{e^*H}$; Step 4 proves completeness of $e^*H$. By [def-weil-pbc-completed-pullback], the comparison from ordinary to completed open pullback is induced by applying the tower pullback to the strict quotient augmentation. Step 5 identifies that augmented tower with the quotient tower of $e^*H$, so the comparison becomes exactly $\eta_{e^*H}$. It is therefore invertible on complete objects.

Source: literature/stacks-project/proetale.tex, Tag 099N, lemma-pushforward-Noetherian-case (2),(5); normalized strict-limit augmentation comparison in the cited exact-product lemma.

### Old Step 7: existing integral open reduction comparison (no new extension node)

Exact extension by zero is [lem-pur-site-restriction-module-adjunction-exact]; it preserves countable products by [lem-cbc-ringed-open-extension-products], since Step 2 proves $e$ quasi-compact. For a flat-term K-flat $P\to M$ on $V$, [lem-sf-open-semilinear-tensor-model] says that $e_!P$ is flat-term K-flat and gives the simultaneous tensor isomorphisms $r_n:(e_!P)\otimes_{B_W}(A_n)_W\to e_!(P\otimes_{B_V}(A_n)_V)$ with formula $[x]\otimes a\mapsto[x\otimes a|_V]$. Forgetting the finite-ring actions yields an isomorphism $r:Q_W(e_!M)_\bullet\to e_!Q_V(M)_\bullet$ in strict $B_W$-module towers: extension by zero has the same underlying module sections before and after this scalar restriction. Its transitions and augmentations commute by the cited model. The strict-limit lemma now gives the natural isomorphism $\sigma_M=(R\lim r)^{-1}\lambda:e_!C_V(M)\to C_W(e_!M)$. Its augmentation clause gives $\sigma_M e_!\eta_M=\eta_{e_!M}$. Thus completeness of $M$ makes $\eta_{e_!M}$ invertible, and Step 4 proves completeness of $e_!M$.

Source: literature/stacks-project/proetale.tex, Tag 09BN, lemma-open-immersion; normalized strict-tower proof using open product preservation and the simultaneous open tensor model. Agent-written assembly.

### Old Step 8: parent Step 6 (its stale step reference is repaired there)

The specified exact open adjunction localizes termwise as in [def-weil-exact-derived-adjunction]. By Steps 6 and 7 both functors preserve complete objects, and the complete subcategories are full, so its Hom bijections restrict unchanged to an adjunction between them. The open unit in [lem-sf-open-tensor-normalization] is the identity on sections under the slice identification $e^*e_!M=M$. This remains the unit after restricting the Hom bijections. Explicitly, a map $e_!M\to e_!N$ corresponds under that bijection to a unique map $M\to e^*e_!N=N$; naturality of the unit says that the map corresponding to $e_!f$ is $f$. Hence $e_!$ induces a bijection on these Hom sets and is fully faithful on the complete subcategories.

Source: literature/stacks-project/proetale.tex, Tag 09BN, lemma-open-immersion; sites-modules.tex lemma-restrict-back; restriction of the specified exact derived adjunction.

### How the extracted arguments use the current statements

For the reflector, ringed-koszul-completion-reflector is applied to the ring sheaf B_T and the actual global section t. Strict-roos-comparison identifies its strict augmentation with the intrinsic (u,0) unit. Completed-koszul-quotient-comparison is natural for arbitrary input and carries precisely that unit to the strict quotient augmentation. Conjugate the Koszul Hom bijection by this unit-compatible isomorphism: for f:C_T(H)→L the composite is f a_H kappa_H=f eta_H. The output completeness and the equivalence of the local/intrinsic/Roos criteria then use roos-intrinsic-completeness-equivalence, whose statement explicitly compares the specified units. This is the actual-unit bridge isolated by the first node, not the coefficient facts of old Steps 1–3.

For restriction, choose a flat-term K-flat P; ringed-topoi-derived-tensor-pullback preserves this property. On a slice over V, restriction of P tensor (A_n)_W and e^*P tensor (A_n)_V have mutually inverse balanced tensor maps, identity on restricted tensors. Applying the quotient A_(n+1)→A_n on either side gives the same x tensor reduced(a), and the augmentation x tensor 1 agrees. Thus there is one strict augmented tower isomorphism before localization, natural on chain maps; the K-flat reduction functor's computation comparisons give its descent. Apply exact-product-functor-strict-limit using exactness and products from the immersion result and exact products from the pro-etale result. Its augmentation clause gives alpha=lambda e^*eta. Applying Rlim(tau) gives b alpha=eta on e^*H, and hence rho e^*eta=eta. The completed-pullback definition uses exactly this pulled strict augmentation; the canonical exact-localization model of derived open pullback identifies that construction with alpha. Exact-pullback-counit-normalization is an existing general tool for this last identification if needed by the future worker. No assertion about arbitrary e_! limits or any choice of a cone map occurs.

Old Step 7 is already existing work: open-semilinear-tensor-model gives r_Q and its strict augmentation and transition equations with K-flatness. On forgetting finite scalar actions it gives the same B_W-tower map because the underlying extension sheaf is unchanged. With qc from parent Step 2, open extension preserves products; exact-product-functor-strict-limit gives sigma=(Rlim r)^(-1) lambda and its augmentation clause gives sigma e_!eta=eta. Integral-open-reduction-comparison already states the resulting completeness preservation, and the parent now cites it. This retains the argument without creating a duplicate node. The final adjunction uses only these preservation facts and the section-normalized existing unit.

## Not duplicates

lem-sf-quotient-completion-actual-reflector vs lem-sf-regular-roos-koszul-unit: gives a regular quotient/Koszul comparison and four criteria; it does not assert complete output or the universal Hom bijection for the actual quotient unit.

lem-sf-quotient-completion-actual-reflector vs lem-sfb-ringed-complete-triangulated: asserts exactness of the Koszul functor and closure of the complete locus, not reflection by the quotient augmentation.

lem-sf-quotient-completion-actual-reflector vs lem-weil-pbc-ringed-cech-completion-unit-idempotence: gives idempotence for two Cech-unit maps, not the actual completed quotient unit or its Hom bijection.

lem-sf-quotient-completion-actual-reflector vs lem-weil-pbc-ringed-cech-completion-restriction: compares Cech completion with slice restrictions, not Koszul-to-quotient transport or a quotient-unit reflector.

lem-sf-quotient-completion-actual-reflector vs lem-weil-pbc-ringed-localization-rhom-calculus: supplies restriction and tensor-Hom identities for bounded localization complexes, not the completion reflection.

lem-sf-quotient-completion-actual-reflector vs lem-weil-pbc-extended-cech-reflector-core: gives a reflector for an augmented locally Cech complex; the new node identifies the actual completed quotient tower/unit with that reflector.

lem-sf-quotient-completion-actual-reflector vs lem-weil-pbc-ringed-koszul-completion-reflector: is the reflector for strict Koszul towers over an arbitrary ringed site; the new argument carries it to completed-coefficient quotient towers and their actual unit.

lem-sf-quotient-completion-actual-reflector vs lem-weil-pbc-ringed-cech-completion-hom-injective: gives only injectivity into another Cech-completed object, not the quotient-unit universal bijection and complete output.

lem-sf-quotient-completion-actual-reflector vs lem-pur-integral-principal-cone-quotient-comparison: identifies two Roos complexes and their units, but has no Hom reflection assertion or Roos/local completeness equivalence.

lem-sf-quotient-completion-actual-reflector vs lem-pur-integral-principal-cone-local-criterion: gives complete output and a local criterion for a cone unit, but no quotient-tower Hom reflector or identification of its actual quotient unit.

lem-sf-quotient-completion-actual-reflector vs lem-sf-completion-finite-reduction: inverts a completion unit after finite reduction, not the universal property for the whole quotient completion.

lem-sf-quotient-completion-actual-reflector vs lem-pur-integral-principal-cone-quotient-augmentation: gives strict levelwise cone-to-quotient quasi-isomorphisms; it neither states the completed quotient reflector nor its Hom universal property.

lem-sf-quotient-completion-actual-reflector vs lem-weil-pbc-completed-koszul-quotient-comparison: gives the unit-preserving isomorphism used in the argument; it does not state complete output or the universal Hom bijection for the actual quotient unit.

lem-sf-quotient-completion-actual-reflector vs lem-pur-roos-intrinsic-completeness-equivalence: identifies five completeness criteria for the input, not the quotient-completion output and Hom reflection.

lem-sf-quotient-completion-actual-reflector vs lem-sf-open-quotient-koszul-completeness: gives adic coefficients, unit identifications and extension completeness, but no universal Hom bijection for arbitrary input quotient completion.

lem-sf-quotient-completion-actual-reflector vs lem-pur-principal-koszul-roos-reflector: gives reflection for a principal Koszul Roos model, not its unit-normalized transfer to the actual finite coefficient quotient tower.

lem-sf-quotient-completion-actual-reflector vs lem-a1-principal-augmented-roos-descent: gives the actual strict Koszul/quotient comparison and descent, not reflection by its quotient augmentation.

lem-sf-quotient-completion-actual-reflector vs lem-sf-automorphism-completion-unit-comparison: assumes an intrinsic reflector and compares an automorphism with it; it does not prove the actual quotient augmentation is the reflector.

lem-sf-quotient-completion-actual-reflector vs lem-sf-constructible-canonical-completeness: starts with a completeness witness and proves unit invertibility; the new lemma treats arbitrary inputs and proves the quotient Hom reflection.

lem-sf-quotient-completion-actual-reflector vs lem-sf-open-roos-unit-adjunction: the new node has one scheme and no open operation, no coefficient/geometry verification and no adjunction; it isolates the actual-unit reflector argument old Step 4, as expressly requested in the return.

lem-sf-open-quotient-completion-unit-comparison vs lem-sf-open-roos-unit-adjunction: the new node proves only the strict augmented restriction comparison, for arbitrary schemes/inputs; it contains neither the coefficient/reflection clauses nor extension preservation or the restricted adjunction, and provides the strict tau and b identifying the actual comparison rather than merely repeating the parent rho clause.

lem-sf-open-quotient-completion-unit-comparison vs lem-pe-constructible-comparison-tensor-test-reflection: reflects vanishing of a tensor homology group for etale comparison; it has no quotient completion, strict augmentation or open Roos comparison.

lem-sf-open-quotient-completion-unit-comparison vs def-sf-point-fibre-tensor-common-stage: defines field-stage canonicality for point tensorators, not the open restriction quotient-completion map.

lem-sf-open-quotient-completion-unit-comparison vs lem-weil-pbc-ringed-slice-normalized-comparisons: provides slice tensor/Hom/Koszul comparison data, not the augmented quotient tower or completed-pullback identification.

lem-sf-open-quotient-completion-unit-comparison vs lem-sf-clopen-comparison-tensor-square: proves tensor and proper/open support squares; its diagrams do not assert the arbitrary-input quotient completion comparison.

lem-sf-open-quotient-completion-unit-comparison vs def-sf-finite-open-tensor-operations: defines fixed finite coefficient tensor/pullback/extension maps, not an assertion over the actual completed coefficient sheaf or its strict derived limit.

lem-sf-open-quotient-completion-unit-comparison vs lem-derived-right-exact-tensor-comparison: constructs the normalized tensorator of a derived strong monoidal functor; it has no strict quotient tower or Roos unit assertion.

lem-sf-open-quotient-completion-unit-comparison vs def-coef-semilinear-derived-calculus: defines system-calculus interfaces and localized adjunctions; it is not a theorem constructing this completed pullback comparison.

lem-sf-open-quotient-completion-unit-comparison vs lem-sf-point-integral-completed-tensor-comparisons: gives integral geometric-point tensor witnesses; it does not give restriction along an arbitrary open or the pulled quotient augmentation.

lem-sf-open-quotient-completion-unit-comparison vs lem-sf-completed-tensor-rational-naturality: proves a scalar-localized tensor naturality theorem assuming reflector comparisons; it does not construct an open quotient comparison.

lem-sf-open-quotient-completion-unit-comparison vs def-coef-semilinear-geometry-derived: defines a normalized system geometry interface; it does not assert the quotient/Roos identification for arbitrary unbounded open input.

lem-sf-open-quotient-completion-unit-comparison vs lem-sf-ringed-finite-free-tensor-complex: gives chain tensor comparison and K-flat preservation for scalar extension, not geometric open restriction and its actual completed-pullback unit.

lem-sf-open-quotient-completion-unit-comparison vs lem-sf-open-roos-restriction-unit: gives exact-product restriction comparison on any tower and its adjunction compatibility; it does not identify e^*Q_W(H) with Q_V(e^*H), nor the resulting map with the specified completed pullback of H.

lem-sf-open-quotient-completion-unit-comparison vs lem-sf-open-roos-extension-comparison: concerns extension applied to arbitrary tower limits; the new node concerns the pulled quotient tower and unit on W under restriction.

lem-sf-open-quotient-completion-unit-comparison vs lem-sf-canonical-open-restriction-model: gives a finite-adjunction mate on semilinear reduction systems given model data; the new argument descends that kind of strict tensor map, applies the normalized Roos limit and identifies the actual completion unit.

lem-sf-open-quotient-completion-unit-comparison vs lem-sf-open-square-quotient-augmentation: assumes a complete H and a Cartesian open square and compares two completed pullbacks; the new node has arbitrary H, no square, and compares open restriction of completion with completion of open restriction.

lem-sf-open-quotient-completion-unit-comparison vs lem-sfb-integral-pullback-strict-roos-normalization: uses separated finite-type schemes and compares scalar-restricted completed and constant towers; it does not state the normalized e^*C(H) comparison for all possibly nonseparated open schemes.

lem-sf-open-quotient-completion-unit-comparison vs lem-sfb-integral-roos-derived-pullback-unit: also assumes separated finite-type schemes and includes constant scalar restriction; the new node has no separatedness or finite-type hypothesis and specifies rho from exact-product open restriction.

lem-sf-open-quotient-completion-unit-comparison vs lem-weil-pbc-pulled-reduction-strict-tower-comparison: is after restriction from actual completed to constant coefficients; the new node lives throughout in B_V-modules and fixes both open Roos product coordinates and the actual completed coefficient unit.

lem-sf-open-quotient-completion-unit-comparison vs lem-sf-immersion-completed-pullback-comparison: supplies the complete-input preservation and comparison, which the parent now cites directly; the new node constructs the augmented strict quotient comparison and normalized rho for arbitrary inputs.

lem-sf-open-quotient-completion-unit-comparison vs lem-sf-integral-open-reduction-comparison: concerns open extension and realized semilinear comparisons on complete inputs; it supplies parent extension preservation and is absent from the new restriction lemma.

lem-sf-open-quotient-completion-unit-comparison vs lem-cbc-exact-product-functor-strict-limit: gives lambda on arbitrary towers for a given exact product-preserving functor; it does not identify pulled quotient reductions, their coefficient tensors, or completed open pullback.

lem-sf-open-quotient-completion-unit-comparison vs lem-sf-exact-pullback-counit-normalization: identifies the K-flat-derived and exact-localized pullback models and their augmented maps; it does not compare the pulled reductions with the reduction tower of e^*H or construct rho to C_V(e^*H).

lem-sf-open-quotient-completion-unit-comparison vs def-pd-section-derived-realization: defines tensor and derived operation comparisons under internal/section equivalences; it has no assertion about the augmented finite quotient completion tower.

lem-sf-open-quotient-completion-unit-comparison vs def-pd-section-derived-tensor-data: defines conjugate K-flat tensor and its localization on section modules; it neither constructs quotient completion nor its open unit normalization.

lem-sf-open-quotient-completion-unit-comparison vs lem-pd-module-ringed-topos-derived-comparison: compares internal and ringed tensor/adjunction operations for condensed coefficients on separated finite-type schemes; no normalized strict quotient limit is identified.

lem-sf-open-quotient-completion-unit-comparison vs lem-pd-section-derived-representative-square: gives the representative square of an internal oplax tensorator, not an augmented strict reduction-tower or Roos-limit comparison.

lem-sf-open-quotient-completion-unit-comparison vs lem-pd-section-derived-tensor-normalization: identifies internal and ringed derived tensor transformations, not pullback of actual quotient completion or its augmentation.

lem-sf-open-quotient-completion-unit-comparison vs lem-pd-section-oplax-total-comparison: identifies the ordinary signed total tensorator under section equivalences; it contains neither the strict quotient tower nor total derived inverse limit.

lem-sf-open-quotient-completion-unit-comparison vs def-weil-pbc-normalized-origin-scalar-comparisons: defines normalized identity and quotient scalar-extension comparators; it is not a geometric open quotient-completion theorem.

lem-sf-open-quotient-completion-unit-comparison vs def-weil-pbc-ringed-projection-restriction-data: defines tensor/adjunction presentation data and projection compatibility, not a proof of an open quotient/Roos unit comparison.

lem-sf-open-quotient-completion-unit-comparison vs def-weil-pbc-ringed-tensor-square-presentation: defines the ordinary geometric coefficient and tensor square data; it states no derived strict quotient completion assertion.

lem-sf-open-quotient-completion-unit-comparison vs lem-weil-pbc-augmented-cech-tensor-pullback: concerns augmented tensor actions of locally Cech complexes under pullback; its statement expressly has no completion-reflector conclusion and does not construct the strict finite quotient limit.

lem-sf-quotient-completion-actual-reflector vs def-pur-principal-cone-tower: Defines the chain cone tower and its augmentation only; the new node proves the actual completed quotient unit is a reflector with its Hom bijection.

lem-sf-quotient-completion-actual-reflector vs lem-fix-scalar-completion-associator: Gives associativity of completed scalar extension for nested fields on complete inputs; the new node is a one-ring reflector on arbitrary input and has no scalar associator.

## Validation

The required initial dry run of the retained earlier split exited 1 at the duplicate gate (a new same-tag node had landed); it pushed nothing. The repair was made in the sandbox only. The final dry run and push results are recorded after they finish.
