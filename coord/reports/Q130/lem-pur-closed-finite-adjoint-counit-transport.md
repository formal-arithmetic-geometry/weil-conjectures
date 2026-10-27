# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-closed-finite-adjoint-counit-transport.json`: same statement and statement dependencies; repaired stage-1 proof assembly, 1864 characters in three steps.
- `dag/nodes/sec-smooth-purity/lem-pur-closed-unbounded-compact-support-normalization.json`: new statement, unsplit; no Mathlib match. Covers returned Step 1 (1255 characters of argument).
- `dag/nodes/sec-smooth-purity/lem-pur-closed-transported-hom-counit-formula.json`: new statement, unsplit; no Mathlib match. Covers returned Step 5 (1629 characters of argument).
- `dag/nodes/sec-smooth-purity/lem-pur-exact-adjoint-classical-counit-comparison.json`: new general categorical statement, unsplit; no Mathlib match. Covers returned Steps 3, 4, 6 (2245 characters of argument).
- `citations.json`: a verbatim quotation for each node used by each assembly step.

The three new statements have empty proof/proof_deps and null proof_origin. Their proofs are deliberately left for separate workers. The complete arguments they inherit are recorded below, rather than being smuggled into their statements.

## Attachments

None. I searched `lean/WeilConjectures/` for the item tag and closed/counit/identity-compactification terms, and read `lean/Sheaf/Paper/ClosedFiniteAdjointCounitTransport.lean`. Its main theorem is still sorry; its canonical auxiliary definitions do not prove all clauses. The upstream exact-derived comparison and identity-open-extension declarations are useful ingredients, not an exact attachment for either complete new statement. No Lean was changed or compiled.

## WANTED

None. All sources used here are present locally.

## Return repaired

The supplied return has one substantive request: spread the six-step 5729-character proof into at least two comparable independently assignable arguments, with statement-only children and an assembly of at most 3000 characters. There was no node, report or search log in this sandbox at startup (only dispatcher marker files). I copied the current shared item; its six proof lengths match the returned entry, and its existing Lean and review metadata were retained. Thus there was no earlier sandbox proof or search history to overwrite. No repository git command was run.

Returned Step 1 is assigned in full to `lem-pur-closed-unbounded-compact-support-normalization`: field/Noetherian check, exact closed direct image, localization identification on unbounded categories, identity extension by zero, and the cohomology formula used later. Returned Step 5 is assigned in full to `lem-pur-closed-transported-hom-counit-formula`: exact pro-etale pushforward, canonical comparison normalization, the entire Hom chain, and its explicit inverse image of the identity. Returned Steps 3, 4, 6 are assigned to `lem-pur-exact-adjoint-classical-counit-comparison`: the standard-truncation lower bound, the isomorphisms beta and alpha constructed from the actual inverse unit, and the full triangle-identity/naturality calculation. These are comparable 1255-, 1629-, and 2245-character arguments. Returned Step 2 is exactly the existing `det-sp-unique-right-adjoint` applied to the two adjunctions; that node already states the unique normalized isomorphism and its equation, so no duplicate child was created. The item now has only three application/assembly steps (1864 characters). Every returned argument is preserved verbatim in the appendix with its assigned node.

The first dry run exited with citation-check errors: the original quotes for t-structure orthogonality and the finite exceptional formula were shorter than its 40-character minimum. I replaced all assembly citations with whole relevant statement excerpts and completed the three-node extraction before the next dry run. That first run pushed nothing.

## Blueprint and literature read

I read the chapter `sec-smooth-purity`, unit `sk-prop-a1`, the current `main-20261015` first-localization-triangle proof, and the finite Hom-chain proof of `thm-sf-ambient-adjoint-class`. The nearest blueprint ancestor remains `prop-pur-affine-line-orientation-uniqueness`, proof Steps 1 and 3 via `lem-pur-retracted-support-localization-comparison`; each of the three children records the parent item as the additional nearest `via`. This repair implements the same closed localization term before pushing through the retraction. It changes neither a unit nor the purity route, and uses no SGA source.

For the normalization child I read Stacks `sites-modules.tex`, Tag 08M3, label `lemma-i-star-equivalence` (exact, fully faithful module direct image); `etale-cohomology.tex`, Tag 04CA, `proposition-closed-immersion-pushforward` (identification of the closed etale subtopos); and `derived.tex`, Tag 015F, `lemma-right-derived-exact-functor` (explicitly includes the whole unbounded category and every complex computing RF). Identity extension is evaluated from `def-weil-pbc-extension-by-zero`; Stacks Tag 03S3 is the extension-by-zero construction cited by the returned argument. The new child's source identifies the localization-triangle extraction and Tag 08M3; these additional places supply the rest of that extracted argument.

For the Hom/counit child I read Stacks `proetale.tex`, Tag 09A6, `lemma-morphism-comparison`, and Tag 09BM, `lemma-closed-immersion-complement-retrocompact-exact`. I read the displayed finite Hom chain in the current blueprint, including the warning that its last arrow is full faithfulness rather than a second Rnu adjunction. I also read Bhatt--Scholze, Proposition 5.2.6(1)-(2), printed page 37, in the local PDF: full faithfulness and invertibility of the actual comparison unit on D+. The new source is the explicit Hom-chain extraction, not a claim that either Stacks tag by itself gives the counit calculation. These are agent-written extractions, as was the returned proof.

For the categorical comparison child I read the standard truncation triangle in Stacks `derived.tex`, Tag 08J5, label `remark-truncation-distinguished-triangle`, together with the explicit standard-t-structure definition and the actual counit equation in `det-sp-unique-right-adjoint`. I also read `lean/WeilConjectures/CategoryTheory/Triangulated/TStructure/Adjunction.lean`: its generic amplitude/right-adjoint lower-bound lemma supplies only the bound part, not the whole new counit comparison statement. This child is the agent's categorical extraction of the returned Steps 3,4,6, with no geometry in its hypotheses. It assumes the left normalization, comparison lambda and invertible comparison unit; it does not assert the geometric existence or normalization of those data.

## Searches

DAG statement/title searches used the whole `dag/nodes` tree for closed compact support, identity compactification, termwise/unbounded closed pushforward, transported counit, and the relevant tags. Blueprint searches were `closed compact support`, `transported counit`, `identity compactification`, `closed direct image`, `counit formula`, `unbounded closed`, and `exceptional counit`. The identity-compactification search finds the proper projection-formula node, whose statement concerns projection maps, not unbounded closed pushforward or the Hom-chain counit. The closed-direct-image hits give exactness or essential-image statements, not both derived normalizations. None states any entire child.

Every new node's Mathlib searches are copied from actual `msearch.py` calls in `searches.jsonl`, with precisely the same tool/query. Each has Loogle, grep and two semantic phrasings; the normalization child also has a successful LeanSearch. The counit child's LeanSearch was rate-limited and is recorded unavailable. I read the actual hits: structure-sheaf open restriction, continuous sheaf pushforward, generic adjunction constructors/counit fields, condensed counits and the definition of pro-etale topology. They do not give the specified constant-module derived closed compactification comparison or the finite transported Hom normalization. No Mathlib leaves are asserted. Existing parent search records are preserved. For the third child I additionally searched the whole blueprint with `comparison unit counit`, `adjoint lower bound`, and `exact derived adjoint`, and the whole DAG for exact/truncation right adjoints, lower bounds, and classical-unit/counit comparisons. Its two semantic searches returned generic derived-adjunction constructors, the same derived counit normalization lemmas, and limit-preservation results. Reading `Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean` confirms that these construct derived adjunctions under localization hypotheses; they do not assert this t-structure bound and classical-image equation from the hypotheses stated in the child. A guessed upstream Mathlib Adjunction.lean location was absent; successful registered searches and the actual source read above are the evidence, not that absent path.

## Not duplicates

lem-pur-closed-unbounded-compact-support-normalization vs lem-trf-oriented-closed-base-localization: the latter supplies exact module direct image and the etale closed-subtopos identification, but states neither unbounded total-derived normalization nor the identity-open compact-support identification or cohomology formula. It is an ingredient of the assigned argument, not its entire statement.

lem-pur-closed-unbounded-compact-support-normalization vs lem-sf-etale-immersion-shriek-normalization: the latter asserts compact-support normalization only on bounded-below inputs and for arbitrary chosen compactifications using refinements. The child fixes the identity-open compactification and asserts the canonical comparison on every unbounded input. No unbounded compactification-refinement comparison is required.

lem-pur-closed-unbounded-compact-support-normalization vs lemma-weil-pbc-projection-formula-identity-compactification: the latter identifies the compactified projection-formula morphism and its inverse for a proper map; it does not state exactness, total-derived comparison or cohomology on unbounded closed inputs.

lem-pur-closed-unbounded-compact-support-normalization vs lem-sfb-exact-open-closed-unbounded-calculus: that statement localizes a specified abstract recollement of exact abelian functors and their units/counits. It does not identify a total right derived direct image or an identity-open compact-support functor.

lem-pur-closed-unbounded-compact-support-normalization vs lem-weil-pbc-exact-functor-derived-factorization: the latter descends an already exact functor and specifies its shift structure. It does not supply closed etale exactness, total-right-derived identification or identity compact-support normalization.

lem-pur-closed-transported-hom-counit-formula vs lem-coef-closed-identity-open-hom-normalization: the latter treats only classical targets S_PH. The child gives the explicit counit at all bounded-below pro-etale targets L for which GU_XL is bounded below, without requiring L classical; it also records exact pro-etale descent and the explicit inverse-identity formula.

lem-pur-closed-transported-hom-counit-formula vs lem-coef-site-closed-counit-transport: the latter identifies the final counit on classical inputs after a prescribed comparison alpha. The child computes the pre-specialization counit from the Hom chain for general L; the parent still performs the classical triangle-identity and naturality calculation.

lem-pur-closed-transported-hom-counit-formula vs lem-coef-proper-identity-open-site-comparison: that node identifies the compact-support comparison with the inverse named mate for proper maps. It supplies one normalization used in the child but does not compute the exceptional Hom bijection or the inverse image of its identity.

lem-pur-closed-transported-hom-counit-formula vs lem-sf-etale-proetale-exceptional-transport: that statement assumes constructible finite-Tor preservation and addresses constructible finite-Tor target K. The child imposes no constructibility or Tor condition and explicitly identifies the formula for the counit on its bounded-below domain.

lem-pur-closed-transported-hom-counit-formula vs lem-pur-closed-support-exceptional-comparison: that node compares the pro-etale kernel-support right adjoint with the transported exceptional value under bounded constructibility of the former. The child compares no such pro-etale support adjoint and computes the relative transported counit directly.

The first two children vs lem-pur-closed-finite-adjoint-counit-transport: the normalization child has no right-adjoint comparison or classical-input counit conclusion; the Hom-formula child assumes the left normalization and contains no lower-bound proof for JB or the final classical-input compatibility. The third child supplies the general boundedness/classical-equation calculation from specified data; the parent still assembles the geometric normalization and actual transported-Hom counit with that conditional categorical result.

lem-pur-exact-adjoint-classical-counit-comparison vs lem-etale-upper-shriek-bounded-below-from-amplitude: that node gives bounded-below preservation from a geometric compact-support amplitude bound, without a fixed bound a preserved by an arbitrary derived F, or the classical counit comparison with two specified right adjoints and lambda. The new statement is about arbitrary abelian derived categories and a specified adjunction/comparison square, not a replacement for the existence theorem.

lem-pur-exact-adjoint-classical-counit-comparison vs lem-weil-boundary-comparison-composition-transport: the existing node assumes the geometric exceptional adjoints preserve D+ and compares composition mates of three morphisms. The new node proves the lower-bound input and a single classical-image counit equation for arbitrary derived categories, with no geometric composition data.

lem-pur-exact-adjoint-classical-counit-comparison vs lem-pbc-normalized-derived-adjunction-transport: that node transports universal left derived pairs across additive equivalences with exact right adjoints. The new node assumes already given derived adjunctions, allows a non-equivalence comparison S_X with a unit invertible only on D+, and proves a lower bound and the displayed classical counit equation. Neither is a one-line specialization of the other.

lem-pur-exact-adjoint-classical-counit-comparison vs lem-coef-site-closed-counit-transport: that node is geometric, assumes IH bounded below, and identifies the actual exceptional counit. The new node proves the bound for any bound-preserving left derived F and treats t_N as the displayed composite, without asserting a geometric relative-adjunction normalization. The second child independently supplies exactly that normalization when the parent uses this result.

lem-pur-closed-transported-hom-counit-formula vs lem-pur-bounded-site-adjunction-transpose: that general geometric statement fixes the bounded Hom transpose and the final classical-target equation under a dimension bound, but does not assert exact unbounded pro-etale closed direct image or the explicit e S(epsilon) lambda^{-1} formula on general nonclassical targets. It provides a useful normalization ingredient, not the complete extracted child.

## Review by Q130

I read the parent statement, current localization triangle, all six returned proof steps and the finite exceptional definition. The statement is unchanged, including ordinary constant-A module categories, c=(id_Z,i), unbounded etale adjunctions, the D+ domain for full faithfulness, quasi-compact complementary open, and no constructibility hypothesis. I checked the three-level route and used no SGA source. The change is a re-split, not a statement repair.

Assembly Step 1 uses the complete new unbounded-normalization statement for both left-functor isomorphisms and the cohomological bound preservation. I opened `lem-exc-closed-support-triangle`: it really uses termwise i_* and identifies the first arrow with its right-adjoint counit, without constructibility assumptions. I opened `det-sp-unique-right-adjoint`: it really supplies a unique natural isomorphism gamma with exactly epsilon^J F(gamma)=epsilon^G, on all objects. Thus the first clause is proved from statements, not from construction details hidden in a proof.

Assembly Step 2 applies the third child's statement. Its four abelian categories are the ordinary etale/pro-etale module categories in the parent. The F of Step 1 preserves both bounds, exactly the categorical hypothesis. `def-sf-comparison-derived-pullback` explicitly supplies exact termwise S_T and preservation of lower bounds. `thm-weil-pbc-site-comparison` explicitly gives invertibility of the actual comparison unit on D+, with no finiteness requirement on individual module sheaves. The second child explicitly supplies the natural lambda on every bounded-below etale H before its later E_L hypothesis. Gamma and its counit equation are Step 1. These match every hypothesis of the third child: in particular lambda is not used before E_B and JB are known bounded below. Its lower-bound conclusion bounds both G and J, its comparison then bounds E_B and constructs alpha using the inverse actual unit. `def-weil-exceptional-inverse-image` literally defines the finite value as S_Z G U_X, so the derived isomorphism has precisely the parent's source and target.

Assembly Step 3 uses the second child's counit formula, now legitimately at K=S_XB because the previous step proved E_K bounded below. The third child's displayed t_B is exactly the second child's actual transported exceptional counit: same G counit, same comparison counit e_K, same canonical lambda_E^{-1}. Its final equation therefore gives the claimed counit compatibility after alpha_B and lambda_D. This last step just substitutes two statement equations; it asserts no ambient unbounded pro-etale adjunction.

For the first new node I verified Noetherianity from finite type over a field using the existing finite-type-over-Noetherian statement. Tag 04CA identifies the closed etale subtopos. In Tag 08M3 the ring-map surjectivity hypothesis holds because the coefficient sheaf pulls back to the same constant coefficient sheaf. Thus exactness is for the module category actually used, not just sets or structure-sheaf modules. Exactness preserves kernels/images and cohomology on arbitrary complexes. Tag 015F explicitly gives unbounded total derivation and every complex computing it; localization uniqueness fixes the comparison. At id_Z the extension presheaf is the original sheaf, so the identity-open factor contributes no map. This is the whole assigned returned Step 1; its extra H^m clause is exactly the observation used by the lower-bound argument, not a new uncited geometric assertion.

For the second new node I verified closed i is qcqs for Tag 09A6, and quasi-compactness of its open complement is the retrocompactness needed for Tag 09BM. Exact pro-etale i_* gives total derived equal to termwise by the same exact-functor/localization argument. The identity-open compact-support comparison is lambda^{-1}, with identity extension contributing identity. The last Hom arrow is comparison full faithfulness at Z, and requires H and GU_XL in D+; both are explicit hypotheses of the statement. Reading the finite source Hom chain confirms this arrow is not a second Rnu adjunction. Inverting the chain on the identity yields first lambda_E^{-1}, then S_X(epsilon^G), then e_L, exactly as displayed. No condition that L itself be classical is needed, and none is inserted. This node contains the whole returned Step 5, not merely an abstract existence of a bijection.

For the third new node I checked the general categorical hypotheses and the detailed argument preserved below. If N lies in D^{>=a}, set T=tau_{<=a-1}(JN). F preserves the upper bound, so orthogonality gives Hom(FT,N)=0. Adjunction forces the truncation map T->JN to be zero; its cohomology is an isomorphism below a, giving the bound. Gamma transfers it to GN. For classical K=S_XN, eta_N is invertible, so beta=gamma_N G(eta_N^{-1}) gives E_N bounded below and alpha=S_Z beta. The triangle identity makes e_K=S_X(eta_N^{-1}); counit naturality and gamma's equation give r epsilon^G=epsilon^J F(beta); naturality of lambda at beta gives the final equation. Every one of returned Steps 3,4,6 has been assigned here. The node assumes F/lambda/unit data; proving their geometric existence is left to the other nodes, so it does not move the entire parent's problem into a categorical restatement. No proof step in this unsplit child was filled in.

Small cases: i=id reduces the left normalization to the identity and the transported formula to comparison counit. Empty Z makes the closed terms/counits zero; empty X forces empty Z. N=0 and a shifted sheaf test the categorical bound and the a-1 truncation endpoint. The formal comparison statement also works with S_X=S_Z=id and lambda=id, where its equation is precisely the given normalized counit equation; it does not wrongly force e_K to be an isomorphism off the classical image. Finite disjoint unions give the same formulas componentwise. No nonemptiness, connectedness, constructibility, finite cohomological dimension, or unbounded full faithfulness was used.

I checked B1-B7 on all three new files: objects and hypotheses are introduced, definition/construction dependencies are named, isomorphisms are in derived categories, sources are explicit, TeX is single-escaped, and proof/proof_deps are empty. I checked C1-C4 against complete node statements for every assembly use and used whole relevant statement excerpts in citations.json. The duplicate comparisons above distinguish bounded inputs, exact normalization, general targets, and the assumptions supplied versus proved; none relies merely on a different node name. D1/D2 are addressed by three comparable subarguments and a short assembly; no child states the entire item. All assembly steps are shorter than 2000 characters. I kept the detailed old arguments below so later workers need not reconstruct them.

## Tool uses

The parent's already accepted maintainer `tool_uses` data is untouched. The worker split report retains the previously declared generic construction roles. The three new nodes have the same chapter/unit as the parent. The third node abstracts ordinary derived categories and adjunctions; the geometric hypotheses and normalized relative counit remain supplied by the first two nodes. No unit route is replaced, and no new maintainer field is set.

## Validation

The server-only review_split check passed on the initial extraction. The first deliver.py dry run failed only its two too-short citation excerpts and pushed nothing. Those excerpts have been replaced with whole relevant statements, and the final three-node extraction is checked by another complete dry run below. No local DAG/preflight checker, compiler, Lake or build tool was run.

## Preserved returned arguments and assignment

These are the complete six returned arguments verbatim, retained for independently assigned workers. They are not proof steps in any of the new statement-only nodes.

### Returned Step 1 -> lem-pur-closed-unbounded-compact-support-normalization

The field $k$ is Noetherian (its ideals are $0$ and $k$), and [lem-weil-pbc-finite-type-over-noetherian] makes $X,Z$ Noetherian. On ordinary constant-$A$ module sheaves, [lem-trf-oriented-closed-base-localization] gives exact closed direct image $F=i_{\mathrm{et},*}$. By [lem-sf-exact-functor-derived-triangulated], its total unbounded right derived functor is canonically its termwise descent: an exact functor preserves kernels, images and hence cohomology and quasi-isomorphisms. The localization universal property [lem-weil-pbc-localization-universal-property] identifies this descent with the total right derived functor: its comparison is already invertible before any resolution, and natural transformations out of either functor are the same transformations after localization. For $c=(\operatorname{id}_Z,i)$, [def-amb-etale-compact-support] gives $Ri_!^c=Ri_{\mathrm{et},*}D(\operatorname{id}_!)$. The presheaf formula in [def-weil-pbc-extension-by-zero] at the identity is already the given sheaf, so its sheafification and derived descent are identities. This gives the asserted canonical isomorphisms on the entire unbounded etale category. In the rest of the proof read the compact-support adjunction through this left-functor isomorphism.

Cited nodes: lem-weil-pbc-finite-type-over-noetherian, lem-trf-oriented-closed-base-localization, lem-sf-exact-functor-derived-triangulated, def-amb-etale-compact-support, def-weil-pbc-extension-by-zero, lem-weil-pbc-localization-universal-property.

Source: literature/stacks-project/derived.tex; Tag 015F (lemma-right-derived-exact-functor); etale-cohomology.tex Tag 04CA (proposition-closed-immersion-pushforward); sites-modules.tex Tag 08M3 (lemma-i-star-equivalence); identity extension by zero: Tag 03S3.

### Returned Step 2 -> existing det-sp-unique-right-adjoint; assembly Step 1

Write $G=i_c^\times$, $J=i_{\mathrm{supp}}^\times$, and write $\epsilon^G:FG\to1$ for the compact-support counit after Step 1. The support adjunction $F\dashv J$ and its counit $\epsilon^J$ are those of [lem-exc-closed-support-triangle]. Apply [det-sp-unique-right-adjoint] to these two adjunctions of the same unbounded etale functor $F$. It gives a unique natural isomorphism $\gamma:G\xrightarrow{\sim}J$ characterized, for every $M$, by $\epsilon^J_M\circ F(\gamma_M)=\epsilon^G_M$. This proves the first right-adjoint and counit assertion without restricting to constructible or bounded objects.

Cited nodes: lem-exc-closed-support-triangle, det-sp-unique-right-adjoint.

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-unique-adjoint/sk-prop-sp-unique-adjoint-categorical.md; The two transpose maps and their counit equation; application to the first localization triangle of sk-prop-a1.

### Returned Step 3 -> lem-pur-exact-adjoint-classical-counit-comparison

Choose $a$ with $B\in D^{\ge a}$. Exactness of $F$ in Step 1 makes $F$ t-exact, since $H^m(FV)=F(H^mV)$ termwise. Put $T=\tau_{\le a-1}(JB)$ using the standard truncation of [def-sbc-standard-tstructure-derived-category]. Then $FT\in D^{\le a-1}$, so the orthogonality axiom of [def-weil-t-structure] gives $\operatorname{Hom}(FT,B)=0$. Under $F\dashv J$, this is $\operatorname{Hom}(T,JB)=0$. In particular the truncation map $T\to JB$ is zero. In degrees $m<a$ it induces an isomorphism on cohomology, by the explicit kernel truncation, so $H^m(JB)=0$. Thus $D=JB\in D^{\ge a}$; this is a direct truncation argument on the unbounded category, without a cohomological-dimension assumption.

Cited nodes: def-sbc-standard-tstructure-derived-category, def-weil-t-structure.

Source: literature/stacks-project/derived.tex; Tag 08J5 (remark-truncation-distinguished-triangle), standard truncation; agent application of adjunction and standard t-structure orthogonality.

### Returned Step 4 -> lem-pur-exact-adjoint-classical-counit-comparison

Let $\eta_B:B\to R\nu_{X,*}\nu_X^*B$ be the comparison unit. It is a natural isomorphism on $D^+$ by [thm-weil-pbc-site-comparison]; set $r_B=\eta_B^{-1}$. Define $E=G R\nu_{X,*}\nu_X^*B$ and $\beta_B=\gamma_B\circ G(r_B):E\xrightarrow{\sim}JB=D$. Step 3 therefore also makes $E$ bounded below. The definition [def-weil-exceptional-inverse-image] is literally $Ri^!K=\nu_Z^*E$ for $K=\nu_X^*B$, so $\alpha_B=\nu_Z^*(\beta_B)$ is the required isomorphism $Ri^!K\xrightarrow{\sim}\nu_Z^*D$. Exact termwise pullback [def-sf-comparison-derived-pullback] preserves the lower bounds. All components are natural in $B$.

Cited nodes: thm-weil-pbc-site-comparison, def-weil-exceptional-inverse-image, def-sf-comparison-derived-pullback.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 5.2.6(1)-(2), p. 37; application to the finite transported definition in def-weil-exceptional-inverse-image.

### Returned Step 5 -> lem-pur-closed-transported-hom-counit-formula

Closed $i$ is quasi-compact and quasi-separated. For every $H\in D^+(Z_{\mathrm{et}},A)$, apply [sk-thm-pe-direct-image-comparison] to get the canonical comparison $\lambda_H:\nu_X^*FH\xrightarrow{\sim}Ri_{\mathrm{proet},*}\nu_Z^*H$. By [lem-exc-proetale-closed-exact] pro-etale $i_*$ is exact on module sheaves; here the quasi-compact open complement is exactly the required hypothesis. Hence, by the argument of Step 1 with [lem-sf-exact-functor-derived-triangulated] and [lem-weil-pbc-localization-universal-property], the latter is termwise $i_*\nu_Z^*H$. At $c=(\operatorname{id},i)$ this is also the inverse of the compact-support comparison of [lem-sf-class-compact-support-comparison], since the identity extension contributes no map. For a bounded-below etale $H$ and bounded-below pro-etale $L$, the transported adjunction is the chain
$$\operatorname{Hom}(i_*\nu_Z^*H,L)\cong\operatorname{Hom}(\nu_X^*FH,L)\cong\operatorname{Hom}(FH,R\nu_{X,*}L)\cong\operatorname{Hom}(H,GR\nu_{X,*}L)\cong\operatorname{Hom}(\nu_Z^*H,\nu_Z^*GR\nu_{X,*}L).$$
The last bijection is comparison full faithfulness in [thm-weil-pbc-site-comparison]; the value is bounded below by the finite definition [def-weil-exceptional-inverse-image]. Expanding these adjunction bijections, the inverse image of the identity of $\nu_Z^*GR\nu_{X,*}L$ is
$$\epsilon^{\mathrm{tr}}_L=\epsilon^\nu_L\circ\nu_X^*(\epsilon^G_{R\nu_{X,*}L})\circ\lambda_{GR\nu_{X,*}L}^{-1},$$
where $\epsilon^\nu$ is the comparison counit. This is precisely the counit of the finite transported exceptional functor, rather than a claim about adjunction on all pro-etale objects.

Cited nodes: sk-thm-pe-direct-image-comparison, lem-exc-proetale-closed-exact, lem-sf-class-compact-support-comparison, thm-weil-pbc-site-comparison, def-weil-exceptional-inverse-image, lem-sf-exact-functor-derived-triangulated, lem-weil-pbc-localization-universal-property.

Source: literature/stacks-project/proetale.tex; Tag 09A6 (lemma-morphism-comparison) and Tag 09BM (lemma-closed-immersion-complement-retrocompact-exact); expanded transported Hom bijections of def-weil-exceptional-inverse-image.

### Returned Step 6 -> lem-pur-exact-adjoint-classical-counit-comparison

Now take $L=K=\nu_X^*B$. The comparison triangle identity gives $\epsilon^\nu_K\circ\nu_X^*(\eta_B)=1_K$, hence $\epsilon^\nu_K=\nu_X^*(r_B)$. Counit naturality for $F\dashv G$, followed by the equation of Step 2, gives
$$r_B\circ\epsilon^G_{R\nu_{X,*}K}=\epsilon^G_B\circ FG(r_B)=\epsilon^J_B\circ F(\gamma_B)\circ FG(r_B)=\epsilon^J_B\circ F(\beta_B).$$
Substitute in Step 5 and use naturality of $\lambda$ at $\beta_B:E\to D$:
$$\epsilon^{\mathrm{tr}}_K=\nu_X^*(\epsilon^J_B)\circ\nu_X^*F(\beta_B)\circ\lambda_E^{-1}=\nu_X^*(\epsilon^J_B)\circ\lambda_D^{-1}\circ i_*(\alpha_B).$$
Thus after identifying $Ri^!K$ with $\nu_Z^*D$ by $\alpha_B$ and identifying $\nu_X^*i_*D$ with $i_*\nu_Z^*D$ by $\lambda_D$, its counit is exactly the image of the etale support counit. The equation uses the actual comparison unit and counit and is natural in $B$; every object to which comparison full faithfulness was applied is bounded below by Steps 3--4.

Cited nodes: .

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1/sk-prop-a1.proof.md; First localization triangle: agent expansion of its closed counit identification by adjunction triangle identity and counit naturality.
