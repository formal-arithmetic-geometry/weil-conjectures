# Stage-1 delivery: det-def-sfb-sheaf-tensor-structure

## Files written

- dag/nodes/sec-proetale-coefficients/det-def-sfb-sheaf-tensor-structure.json: existing definition with assertions, now split into eight proof steps; Mathlib candidates require an explicit construction comparison.
- dag/nodes/sec-proetale-coefficients/lem-sfb-sheaf-tensor-unit-comparison.json: new statement-only lemma, unsplit; no exact or one-line Mathlib match.
- citations.json: verbatim statement passages for every citation of the item.

## Attachments

None. Searched all WeilConjectures/ by blueprint tag and the tensor-structure names, and read CategoryTheory/GrothendieckAbelian/Monoidal/Defs.lean:91-147. Its generic monoidal and braided instances and pro-etale specializations do not state all the explicit symmetric-structure, comparison, functor, and Ab clauses of the item. The local Sheaf wrapper listed in the node is stage-2 material, not a completed proof in the allowed project source.

## Wanted sources

None. Both current blueprint files, the unit and chapter records, and the Stacks source were available. No forbidden SGA source was used.

## Corrections and retained work

The shared item already contained an earlier six-step proof and its searches, despite its current unsplit status. I copied that version into the empty sandbox and retained its statement and mathematical construction. Its 2688-character step 3 contains an independently quantified four-case comparison calculation. Under the 2026-10-17 long-step instruction I extracted precisely that lemma, without moving coherence or strong symmetric monoidality out of the item's proof. The 2076-character functor step combined construction with a short recursion calculation; these are now separate steps, with the calculation written out. The earlier calculations are preserved below for the next worker. No statement dispute, altered hypothesis, or change to chapter/unit route is needed. The previous searches are preserved verbatim; fresh searches made here are appended with their actual logged output.

## Unfinished work

The new comparison lemma is intentionally statement-only and unsplit, as required for a one-level split. Its four cases are recorded in the appendix as a handoff argument. No Lean was written or compiled.

## Not duplicates

lem-sfb-sheaf-tensor-unit-comparison vs det-def-sfb-sheaf-tensor-structure: the new lemma asserts four comparison identities for arbitrary presheaf-to-sheaf maps, before any coherence is assumed. It asserts neither the pentagon/triangle/hexagons nor involutivity nor strong symmetric monoidality nor the Ab identification; these remain proved in the item.

lem-sfb-sheaf-tensor-unit-comparison vs det-def-sfb-sheaf-tensor-local-iso: the latter asserts tensor stability of W and invertibility after sheafification, not compatibility of structure maps with comparisons.

lem-sfb-sheaf-tensor-unit-comparison vs det-def-sfb-sheaf-tensor-presheaf: the latter constructs the objectwise monoidal structure and internal Hom, and contains no reflected structure-map identities. Whole-DAG statement searches for sheafification together with associator/unitors/hexagon/pentagon/brackets found only the item. Whole-blueprint searches for sheafification associator, bracketing, canonical isomorphisms and conjugate found no existing node stating this comparison. Lean searches by the id, canonical comparison and unit-comparison concepts found no exact project declaration. There is no Stacks-tag collision for this new blueprint-source lemma.

## Review by Q104

I read the main-20261015 structure statement and its entire proof, the complete sheaf-tensor unit and proetale-coefficients chapter records, and the statements of every cited node. I also read Stacks sites.tex Proposition sites-proposition-sheafification-adjoint (00WH), lines 2053 onward, and Example sites-example-constant-sheaf (0H7J), lines 2099 onward. These latter passages concern sets; they are used for terminology only. The general coefficient-category adjunction is explicitly provided by the cited sheafification and local-iso statements, so no set-valued theorem is silently applied to arbitrary coefficients. The new node serves the blueprint proof's second paragraph, first sentence, whose claim about conjugates requires exactly these four checks.

Step 1 uses def-weil-pbc-sheafification for factorization and uniqueness and det-def-sfb-sheaf-tensor-local-iso for the Hom characterization of W. The inverse of the unit on a sheaf follows by the two displayed uniqueness arguments. All targets of extensions are sheaves; no arbitrary unit is inverted as a presheaf map.

Step 2 uses det-def-sfb-sheaf-tensor-presheaf for the objectwise bifunctor, unit and constraints, local-iso clause 2 for tensoring the comparison maps in W, and sheafification for the unit and its functoriality. Its induction has variable and unit bases. This includes zero variables and repeated inserted units. The essential smallness and Grothendieck coefficient hypotheses are exactly those inherited from the statement; no new colimits or large ends are formed here.

Step 3 uses the same three interfaces: local-iso clause 1 makes the reflected maps involving eta invertible; presheaf gives the natural objectwise constraints; sheafification provides the natural unit and counit. The left-hand factor of the associator is explicitly inverted in the correct direction. Unit maps have domain I, not the sheafified unit.

Step 4 uses only lem-sfb-sheaf-tensor-unit-comparison, whose four verbatim formulas give exactly equation (*). The formula d(d(f,g),h) has target i((F star G) star H), so compound comparisons type-check without assuming monoidal coherence. The lemma allows arbitrary f,g,h, which includes all maps from step 2; its validity does not depend on a hidden local-equivalence hypothesis for those maps.

Step 5 uses presheaf for the actual pentagon, triangle, hexagon and symmetry identities, and local-iso for injectivity of precomposition by q_B into the target sheaf. Propagation through tensor contexts is written as an explicit naturality calculation. Inverse propagation inverts the structure isomorphisms only, never q_B. Thus this is an argument for coherence, not an appeal to a general coherence theorem.

Step 6 uses sheafification for extension and its uniqueness, local-iso clause 3 for the invertible tensor comparison, and presheaf for the tensor functor. The tensorator direction is the inverse of c_{F,G}; the unit comparison is the identity of aI, including at the empty expression.

Step 7 uses sheafification uniqueness to establish the displayed recursion in two lines and to equate the two maps after precomposition by eta. Earlier steps 4-5 supply the already-proved comparison identities for structure maps in compound expressions. Substitution gives all four displayed associativity/unit/symmetry compatibility equations, not merely invertibility of the tensorator. This calculation uses no new non-elementary black box.

Step 8 uses clause 1 of presheaf for the objectwise tensor/unit and def-weil-pbc-constant-sheaf for the definition of the constant sheaf. It is a direct specialization to Ab. No cartesian tensor is substituted for the additive tensor.

I checked the new lemma against its blueprint source sentence and all four earlier calculations reproduced below. For associativity, unit naturality cancels a(s) against its inverse after precomposition with eta_X s; objectwise naturality then introduces arbitrary f,g,h. The two unit cases use i epsilon eta = identity with the correct target sheaf. Symmetry uses unit naturality then objectwise braiding naturality. These checks work for zero maps, the zero coefficient object, identity units on a trivial topology, and non-flat abelian sheaves: no tensor exactness, stalk criterion or flatness is used. The unit-only and inverse-constraint cases are covered by the item's induction and propagation. No definition depends on a sorry-existence construction, and the new statement does not cite the item, so it introduces no dependency cycle.

Mathlib search hits were read, including Sites/Monoidal.lean:168-201, Localization/Monoidal/Basic.lean:124-126,214-247 and Braided.lean:57-64. They use the lifted tensorBifunctor and its abstract mu; their agreement with the present explicit reflected tensor and eta composites is a substantive comparison. CartesianMonoidal hits assume a cartesian tensor and do not cover Ab tensor. Neither item nor new lemma is an exact/one-line Mathlib leaf. All new recorded queries are in searches.jsonl, including a second semantic phrasing. The new node has no proof or proof dependencies, and no unperformed query was recorded.

The original two long steps were specifically reviewed for hidden lemmas. The arbitrary-leaf comparison was extracted as the sole new node. The functor comparison recursion is an elementary unique-extension computation, retained explicitly rather than made a duplicate node. Every resulting non-elementary step is shorter than 2000 characters. No off-unit theorem is used, and the item is not the key node of sk-def-sfb-sheaf-tensor, so its unit realization record is not edited.

## Preserved comparison calculation for the new node

Define the associator by the composite in the statement, using the inverse of $a(\eta_{iF\otimes_p iG}\otimes_p iH)$ on its left and $a(iF\otimes_p\eta_{iG\otimes_p iH})$ on its right. Both maps are invertible by clause 1 of [det-def-sfb-sheaf-tensor-local-iso] and step 1. Explicitly define the left unitor as
$$\epsilon_F\circ a(\lambda^p_{iF})\circ a(\eta_I\otimes_p iF)^{-1}:a(iaI\otimes_p iF)\longrightarrow F,$$
and the right unitor by $\epsilon_F\circ a(\rho^p_{iF})\circ a(iF\otimes_p\eta_I)^{-1}$. Define symmetry as $a(\beta^p_{iF,iG})$. These are natural isomorphisms: functoriality gives naturality before taking inverses, and naturality of an invertible family also gives naturality of its inverse. We verify compatibility for arbitrary leaf maps $f:P\to iF$, $g:Q\to iG$, $h:R\to iH$ chosen in step 2, not only identity leaf maps. Thus for every basic structure map $t$ we prove
$$i(t^{\mathrm{Sh}})q_B=q_{B'}t^p.\tag{*}$$
For associativity put $L=(iF\otimes_piG)\otimes_piH$, $X=ia(iF\otimes_piG)\otimes_piH$, $M=iF\otimes_p(iG\otimes_piH)$, $Y=iF\otimes_pia(iG\otimes_piH)$, $s=\eta_{iF\otimes_piG}\otimes_p\mathrm{id}_{iH}:L\to X$, and $r=\mathrm{id}_{iF}\otimes_p\eta_{iG\otimes_piH}:M\to Y$. Unit naturality and the specified associator give
$$i(\alpha^{\mathrm{Sh}})\eta_Xs=\eta_Yr\alpha^p_{iF,iG,iH}.$$
Indeed $i(a(s)^{-1})\eta_Xs=\eta_L$, $i(a\alpha^p)\eta_L=\eta_M\alpha^p$, and $i(ar)\eta_M=\eta_Yr$. Precomposing by $(f\otimes_pg)\otimes_ph$ and using
$$\alpha^p_{iF,iG,iH}((f\otimes_pg)\otimes_ph)=(f\otimes_p(g\otimes_ph))\alpha^p_{P,Q,R}$$
gives (*) because the two recursive comparisons are $\eta_Xs((f\otimes_pg)\otimes_ph)$ and $\eta_Yr(f\otimes_p(g\otimes_ph))$.
For the left unitor put $X_\ell=iaI\otimes_piF$ and $s_\ell=\eta_I\otimes_p\mathrm{id}_{iF}$. Its defining formula gives
$$i(\lambda^{\mathrm{Sh}}_F)\eta_{X_\ell}s_\ell=i\epsilon_F\eta_{iF}\lambda^p_{iF}=\lambda^p_{iF}.$$
Precomposing by $\mathrm{id}_I\otimes_pf$ gives $i(\lambda^{\mathrm{Sh}}_F)q_{(IP)}=f\lambda^p_P$ by naturality of $\lambda^p$. For the right unitor put $X_r=iF\otimes_piaI$ and $s_r=\mathrm{id}_{iF}\otimes_p\eta_I$. Its defining formula gives
$$i(\rho^{\mathrm{Sh}}_F)\eta_{X_r}s_r=i\epsilon_F\eta_{iF}\rho^p_{iF}=\rho^p_{iF}.$$
Precomposing by $f\otimes_p\mathrm{id}_I$ gives $i(\rho^{\mathrm{Sh}}_F)q_{(PI)}=f\rho^p_P$ by naturality of $\rho^p$. Finally symmetry satisfies
$$i(a\beta^p_{iF,iG})\eta_{iF\otimes_piG}(f\otimes_pg)=\eta_{iG\otimes_piF}(g\otimes_pf)\beta^p_{P,Q}$$
by unit naturality followed by naturality of $\beta^p$. These equations prove (*) for all four kinds of maps and all chosen leaf comparisons, including comparisons of compound subexpressions.

## Preserved earlier functor-comparison calculation

For sheafification itself use step 2 with $S_j=aP_j$ and $q_j=\eta_{P_j}$. The unique extension of $q_B$ to a map $c_B:aP_B\to S_B$ is $\epsilon_{S_B}\circ a(q_B)$, and is invertible by step 2. At a variable this map is the identity. At a unit it is also the identity; at a binary expression in two variables it is
$$c_{F,G}=a(\eta_F\otimes_p\eta_G):a(F\otimes_pG)\xrightarrow{\sim}a(iaF\otimes_piaG)=aF\otimes aG,$$
by unit naturality and $\epsilon_{aQ}a(\eta_Q)=\mathrm{id}$, the latter following from the uniqueness of extension across $\eta_Q$. Clause 3 of [det-def-sfb-sheaf-tensor-local-iso] also states this invertibility directly. The tensorator in the question is $c_{F,G}^{-1}$ and the unit comparison is the identity of $aI$. Naturality of these comparisons follows from unit naturality. To identify the comparisons for compound expressions, first note that $i(c_D)\eta_{P_D}=q_D$ and $i(c_E)\eta_{P_E}=q_E$. Hence
$$i\bigl((c_D\otimes c_E)c_{P_D,P_E}\bigr)\eta_{P_D\otimes_pP_E}
=\eta_{iS_D\otimes_piS_E}(q_D\otimes_pq_E)=q_{(DE)},$$
by bifunctoriality and unit naturality. Uniqueness of extension therefore gives the recursion
$$c_{(DE)}=(c_D\otimes c_E)c_{P_D,P_E}.$$
Equation (*) was proved in step 3 for arbitrary leaf comparisons and extends inside contexts by step 4. For a basic presheaf structure map $t^p:P_B\to P_{B'}$, it yields
$$i(t^{\mathrm{Sh}}c_B)\eta_{P_B}=q_{B'}t^p=i(c_{B'}a(t^p))\eta_{P_B}.$$
Uniqueness of extension gives $t^{\mathrm{Sh}}c_B=c_{B'}a(t^p)$. Substituting the recursion for $c_B,c_{B'}$ gives the four equations
$$\alpha^{\mathrm{Sh}}(c_{F,G}\otimes\mathrm{id})c_{F\otimes_pG,H}
=(\mathrm{id}\otimes c_{G,H})c_{F,G\otimes_pH}a(\alpha^p),$$
$$\lambda^{\mathrm{Sh}}_{aF}c_{I,F}=a(\lambda^p_F),\qquad
\rho^{\mathrm{Sh}}_{aF}c_{F,I}=a(\rho^p_F),\qquad
\beta^{\mathrm{Sh}}_{aF,aG}c_{F,G}=c_{G,F}a(\beta^p_{F,G}).$$
These are precisely the associativity, unit and symmetry compatibilities of a strong symmetric monoidal functor (written in the direction $c$). Thus $a$ has the asserted structure, with the specified inverse tensorator.

## Dry-run repair

The first server dry run rejected the new node because its inherited chapter and unit were not explicit fields. Added chapter sec-proetale-coefficients and unit sk-def-sfb-sheaf-tensor; no mathematical content changed.
