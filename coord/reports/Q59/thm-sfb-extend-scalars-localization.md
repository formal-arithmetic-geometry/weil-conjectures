# Worker report — Q59

Stage-1 repair of `thm-sfb-extend-scalars-localization`, 2026-10-21. The human returned the 5043-character proof as too coarse. The item's statement is unchanged, including the actual continuous coefficients, the finite-extension hypothesis and topological Noetherianity. No Lean, compiler, repository git command, repository edit, or launcher edit was used.

## Files written

All node files are under `dag/nodes/sec-proetale-coefficients/` in this sandbox.

- `thm-sfb-extend-scalars-localization.json`: statement; repaired five-step assembly, 2478 proof characters.
- `lem-sfb-integral-localization-hom-colimit.json`: statement; no Mathlib match; complete 1726-character proof of the canonical shifted Hom comparison for the unit telescope.
- `lem-sfb-scalar-unit-equality-detection.json`: statement; no Mathlib match; complete 871-character abstract adjunction/finite-stage equality proof.
- `lem-sfb-rational-derived-scalar-invertible.json`: statement; no Mathlib match; complete 1093-character construction of inverse scalar maps on internal modules and complexes.
- `lem-sfb-rationalization-localization-hom-criterion.json`: statement; no Mathlib match; complete 1685-character abstract scalar-fraction proof.
- `lem-sfb-linear-localization-descent.json`: statement; Mathlib leaf, `CategoryTheory.Localization.functor_linear_iff`, `Mathlib/CategoryTheory/Localization/Linear.lean:79`.

Also written: `citations.json` for every citation of every parent step, `child-citations.json` for the new proof steps, this report, and sandbox-only search/reconstruction records. The four new non-Mathlib nodes are delivered statement-only with status unsplit, as the mandatory preflight requires. Their complete proofs in words, with sources and per-step dependencies, are preserved below in this report; each extracted argument is therefore delivered concretely while respecting the standard new-child shape. Each proof is well under 3000 characters, and every individual step is under 650 characters. No unit or chapter record is changed: this item realizes the bounded-constructible complement of unit step 2, rather than the whole unit statement.

## Attachments

No finished project declaration under `lean/WeilConjectures/` states the entire item: its instance in `WeilConjectures/CategoryTheory/ModuleObjects/EllAdicRationalization.lean` still has `sorry`. I read the corresponding supplementary module under `lean/Sheaf/UpstreamExtra/WeilConjectures/CategoryTheory/ModuleObjects/` and its private helpers as implementation evidence, not as finished attachments. Its `integral_scalar_map_eq` splits precisely into the new continuity and abstract equality arguments. The private `rationalization_localization_of_hom` motivates the new generic criterion.

The existing closed declarations `CategoryTheory.Rationalization.exists_smul_eq_map` and `CategoryTheory.Rationalization.map_eq_map_iff` already belong to `lem-sfb-rationalization-scalar-fractions` and are reused unchanged.

## WANTED

None. All sources used are present in the read-only repository or its Mathlib source.

## What was wrong and what changed

The seven-step proof obscured separate interfaces and used proofs of cited nodes as though their statements provided those interfaces. The statement of `lem-weil-pbc-continuous-constructible-integral-image` only asserts triangulated closure of an essential image; it does not state `derived_nsmul_isIso`. The statement of `lem-weil-pbc-integral-constructible-sequential-hom` only gives factorization through a stage; the old proof used its private helpers to obtain an isomorphism of Hom colimits. These are C3/C4 issues, repaired by statements expressly asserting the inverse-scalar and canonical Hom comparisons. The final scalar-fraction calculation is now its own generic criterion, with the exact Mathlib scalar-preservation input exposed.

The source/target coefficient categories are not replaced by raw scalar localization categories. The restricted functor's compatibility is already part of `def-sfb-bounded-constructible-extend-scalars`, with identity components on the underlying derived images. The triangulation input is the valid integral specialization; no rational Serre claim is needed. Exactness of actual continuous scalar extension and the exact-functor derived comparison justify ambient triangulatedness explicitly.

Removed parent proof dependencies that are now used only inside children: Hom-colimit definition, strict localization model and model transport, sheaf-source continuity, scalar fractions. The old essential-image closure citation and factorization-only sequential lemma are no longer used. Their nodes and proofs are untouched. Existing denominator-clearing and integral-model theorems remain the essential-surjectivity route; they are not re-created as new clauses of the item.

## Not duplicates

- lem-sfb-integral-localization-hom-colimit vs lem-weil-pbc-integral-constructible-sequential-hom: the latter only asserts factorization of individual maps; the new lemma asserts the canonical isomorphism of shifted Hom colimits, including equality detection, for the specified localization-unit telescope.
- lem-sfb-integral-localization-hom-colimit vs lem-weil-pbc-integral-constructible-sheaf-hom: the latter has a single constructible sheaf as source and an actual complex colimit; the new lemma has any bounded constructible source and the specified derived scalar-unit cocone, with strict-model transport.
- lem-sfb-integral-localization-hom-colimit vs lem-weil-pbc-integral-localization-complex-model: the latter supplies a representative and compatible cocone legs, not preservation by Hom.
- lem-sfb-integral-localization-hom-colimit vs lem-weil-pbc-integral-localization-colimit-transport: the latter is conditional on a functor's continuity on strict complex models; the new lemma verifies this condition for shifted Hom from integral bounded constructible sources.
- lem-sfb-integral-localization-hom-colimit vs lem-weil-pbc-scalar-localization-derived-hom: the latter is for ordinary sheafified section localizations and assumes coproduct compactness of the source; this lemma proves the canonical telescope comparison for the actual continuous internal coefficient categories and constructible sources without that additional hypothesis.
- lem-sfb-scalar-unit-equality-detection vs lem-weil-pbc-filtered-colimit-modules-elementwise: the existing result detects equality in a filtered module colimit; the new result derives scalar-power equality from equality under an arbitrary adjoint functor, using an explicitly prescribed unit telescope and its Hom preservation.
- lem-sfb-scalar-unit-equality-detection vs lem-sfb-rationalization-scalar-fractions: the latter concerns equality under the canonical Verdier rationalization Q; the new lemma concerns an arbitrary adjunction and a unit cocone, prior to proving that scalar extension is a localization.
- lem-sfb-rational-derived-scalar-invertible vs lem-weil-pbc-continuous-constructible-integral-image: image closure is different from invertibility of scalar powers on every ambient rational derived object. The existing source file proves this as a supporting theorem, but the old node statement does not include it.
- lem-sfb-rational-derived-scalar-invertible vs sk-def-sfb-rationalization: the existing definition gives invertible scalars in an abstract rationalization; the new result constructs inverse maps in the actual derived continuous E coefficient category.
- lem-sfb-rationalization-localization-hom-criterion vs lem-sfb-rationalization-scalar-fractions: the existing node calculates morphisms in the canonical rationalization; the new node proves full faithfulness of another functor using explicit lifting and equality hypotheses, and essential surjectivity is an assumption.
- lem-sfb-rationalization-localization-hom-criterion vs thm-sfb-extend-scalars-localization: the generic criterion contains no geometry or integral/rational coefficients and assumes the hard geometric properties (models, denominators, equality); it does not repackage the item's proof into a specialized restatement.
- lem-sfb-linear-localization-descent vs lem-sfb-additive-localization-linear: the existing leaf constructs the linear structure on the target of a localization and makes its localization functor linear; the new leaf gives scalar preservation by a functor out of that localization, with all three linear structures already fixed.
- lem-sfb-linear-localization-descent vs def-sfb-rationalization-linear: the existing definition extends the scalar action on a rationalized category; it does not give scalar preservation for its induced functors.

Before creation I searched the whole DAG by ids, titles, concepts and cited declarations, and the whole blueprint with `blueprint_refs.py search` for scalar equality, localization telescope, localization criterion, scalar unit, Hom continuity, torsion cone, fraction criterion, Hom scalar, inverts torsion, shifted Hom, linear localization, localization additive, linearity descends, linear induced functor, integral localization, scalar telescope and rationalization full faithfulness. No existing node states any new result. Near matches listed above were opened and distinguished. Blueprint ancestry is the unchanged item, with empty via and same_as lists.

## Review by Q59

I read the live node, its chapter and unit, the current main-20261015 statement and proof, and Bhatt–Scholze Section 6.8: Lemma 6.8.2(2) identifies the actual continuous coefficient ring after inverting ell; Lemma 6.8.12 gives the relevant Hom continuity; Proposition 6.8.14(2) supplies the rationalization route. I also read the strict-model and transport node statements and their Lean signatures, the sheaf-source statement, the private bounded-source induction, and the supporting inverse-scalar proof in ContinuousConstructibleIntegralImage. I checked Stacks algebra.tex, Tags 00D6 (lemma-directed-colimit) and 00D7 (lemma-zero-directed-limit), directly for the finite-stage equality step. For the generic scalar-fraction criterion I read the blueprint's full-faithfulness paragraph and the supplementary module's private generic proof. For the Mathlib leaf I read Localization/Linear.lean:66–95, including every variable and instance surrounding functor_linear_iff. It requires no additivity of G to prove scalar preservation, and I have not claimed that as a separate Mathlib conclusion.

For parent step 1 I opened each of the seven cited statements: continuous integral coefficients and the coefficient morphism define the very same inclusion; the restricted-functor definition explicitly includes the comparison isomorphism; the integral triangulated lemma has topological Noetherianity and finite E exactly as here. The exactness node asserts preservation of arbitrary short exact sequences. The exact-functor clause of the derived-category definition identifies the actual left derived functor with its termwise construction; the exact-derived-triangulated node then supplies shift and triangle compatibility. All coefficient hypotheses are retained, and additivity gives the required Z-linearity.

For parent step 2 the new inverse-scalar lemma says exactly that every ell-power identity is invertible on every ambient rational derived object. The cone-zero node states the equivalence for a distinguished triangle used here; rationalization defines W by existence of a torsion cone in the integral triangulated source. Mapping the annihilation equation gives an invertible zero endomorphism, whose cancellation makes the identity zero. The full inclusion reflects inverses because the ambient inverse is itself a morphism of the full subcategory. This three-line cone argument is left elementary, instead of being made into a new node that only restates a clause.

For parent step 3 I checked that the denominator statement gives an integral morphism with the equation ell^n h=L(u), for any two integral bounded constructible objects. Its source and target are the actual coefficient categories of step 1. The integral-model statement produces an integral bounded constructible object and an ambient isomorphism for every rational bounded constructible object. Its inverse is automatically a morphism in the rational full subcategory. No lisse lattice existence or gluing proof is hidden in this step: these are the conclusions of the existing theorems being cited.

For parent step 4 the derived extension statement gives the needed adjunction. The telescope definition gives precisely the inverse-scalar-unit legs, whose zeroth member is the unit. The new Hom statement asserts an isomorphism, not just factorization, and at shift zero is exactly the Hom-colimit hypothesis of the new abstract equality lemma. K and B are bounded constructible, hence B is bounded below as required by the strict-model theorem. Thus the equality lemma applies without a further compactness assumption.

For parent step 5 I checked each hypothesis of the generic criterion independently: the source is the valid integral Z-linear triangulated category; the target is only preadditive; actual scalar extension is additive and consequently Z-linear; inversion and target scalar units were proved in step 2; denominator lifting and essential surjectivity were established in step 3; equality detection was established in step 4. The conclusion therefore concerns the unchanged restricted functor and exactly W_{ell^N}.

I reviewed the child proofs as well. The Hom comparison uses the full statements of complex-model existence, conditional colimit transport and sheaf-source continuity. Its bounded induction has a zero base below the cohomological lower bound, one truncation triangle for each degree, and a terminal identification with K; extension stability supplies precisely the comparison for the middle term. Isomorphism, shift and equivalent-index transport are written explicitly as precomposition/reindexing of the same cocones, not arbitrary identifications of abstract group objects. The equality lemma uses the precise elementwise filtered-colimit equality statement and proves the transition formula by induction. The inverse-scalar lemma constructs the inverse from the actual constant field coefficient, transports the multiplication identities through p_X^*, and uses the module action equations to obtain natural chain isomorphisms. The generic criterion clears both denominators, applies the equality hypothesis to the two integral numerators, invokes the equality clause of the existing scalar-fractions theorem, and cancels invertible scalars; its surjectivity step specifies the inverse-scalar fraction. Object transport and the quasi-inverse construction are explicit. No child depends on the parent, and none reproduces the geometric localization theorem with its proof suppressed.

Small cases checked in words: zero source, zero target, empty scheme and a single-degree complex in the Hom comparison; arbitrary shifts and a uniform lower bound; torsion B and stage zero; scalar a=0 and a=1 in the abstract equality statement (at a=0 stage one kills both representatives, while at a=1 the Hom-unit is injective); exponent n=0 and empty X in the inverse-scalar statement; M={1}, 0 in M, zero R, and zero objects in the generic criterion. In the 0-in-M case the invertibility hypothesis forces the target to have zero identities, consistently with the collapsed rationalization. No statement dispute or missing hypothesis was found.

I checked delivery-errors B–E against the files: complete self-contained statements, explicit definition dependencies and correct sources, genuine recorded searches, verbatim parent and child citation quotes, no cycle, no duplicate or restated geometric clause, no hidden non-elementary fact inside an elementary marker. Complete proofs of the four children are supplied below, while the child JSON files follow the required unsplit statement-only format. All five new nodes were searched with the required command and their own statements in mind; four non-Mathlib results had two distinct semantic phrasings, plus LeanSearch, Loogle and grep. The scalar-descent leaf has a direct exact declaration match, including its file and line. No unavailable service is reported as a negative result. The unused searches for a prospective generic cone lemma remain honestly logged; that lemma was not created because the cone argument is elementary from the cited inputs.

## What remains

No mathematical part of this repair is left unfinished. Server check_dag and parent review_split passed before this report. The first full dry run required new children to be unsplit statement-only; their complete proof words were moved here and the combined definition citations were separated into individually parsed links. The corrected full dry run passed at 90514eab2d4 with all five new nodes admitted. Direct delivery follows that successful check. This is a stage-1 delivery only, not a claim that the Lean theorem has been proved.

## Complete proofs in words of the extracted nodes

These proofs are retained here because new node JSON files must be statement-only. The human return asks for the finer mathematical arguments themselves; none has been discarded.

### lem-sfb-rationalization-localization-hom-criterion

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-thm-sfb-rationalization-comparison/thm-sfb-extend-scalars-localization.proof.md, Morphisms of the rationalization, full faithfulness, and conclusion; generic algebraic assembly extracted by the agent.

1. The localization universal property gives $G$ and $e:QG\cong F$. By [lem-sfb-linear-localization-descent], $G$ preserves scalars. On morphisms $\alpha:QA\to QB$ put $H(\alpha)=e_B\circ G(\alpha)\circ e_A^{-1}$. Naturality gives $H(Q(u))=F(u)$, and bilinearity gives $H(m\alpha)=mH(\alpha)$.

   Uses: `lem-weil-pbc-localization-universal-property`, `lem-sfb-linear-localization-descent`. Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-thm-sfb-rationalization-comparison/thm-sfb-extend-scalars-localization.proof.md, Full faithfulness; induced functor and naturality.

2. If $H(\alpha)=H(\beta)$, choose $r,s\in M$ and $u,v$ with $r\alpha=Q(u)$ and $s\beta=Q(v)$ using [lem-sfb-rationalization-scalar-fractions]. Then $(rs)\alpha=Q(su)$ and $(rs)\beta=Q(rv)$, so $F(su)=F(rv)$. Hypothesis (ii) and the equality clause of the same theorem imply $Q(su)=Q(rv)$. Since $(rs)\operatorname{id}$ is invertible in the rationalization, cancel it to obtain $\alpha=\beta$.

   Uses: `lem-sfb-rationalization-scalar-fractions`, `sk-def-sfb-rationalization`. Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-thm-sfb-rationalization-comparison/thm-sfb-extend-scalars-localization.proof.md, Full faithfulness; injectivity after clearing both denominators.

3. Given $h:FA\to FB$, use (i) to choose $m,u$ with $mh=F(u)$. Put $\alpha=Q(u)\circ(m\operatorname{id}_{QA})^{-1}$. Then $m\alpha=Q(u)$, so $mH(\alpha)=F(u)=mh$. Cancel $m\operatorname{id}_{FA}$, invertible by hypothesis, to get $H(\alpha)=h$. Thus $H$ is bijective. Every object of the rationalization is isomorphic to a $Q$-image by [lem-sfb-additive-localization-linear]; conjugation by those isomorphisms gives bijections on all Hom sets. Hence $G$ is fully faithful.

   Uses: `lem-sfb-additive-localization-linear`. Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-thm-sfb-rationalization-comparison/thm-sfb-extend-scalars-localization.proof.md, Full faithfulness; surjectivity and transport to all objects.

4. For each $Y\in\mathcal D$ choose $A$ and $FA\cong Y$ by essential surjectivity of $F$; compose with $e_A$ to get $G(QA)\cong Y$. Choosing these preimages and lifting each conjugated morphism by the Hom bijections constructs a quasi-inverse to $G$; injectivity verifies identities, composition and the two inverse isomorphisms. Precomposition with this equivalence is an equivalence on every functor category. Composing it with the equivalence for $Q$ from the localization universal property gives exactly that property for $F\cong QG$.

   Uses: `lem-weil-pbc-localization-universal-property`. Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-thm-sfb-rationalization-comparison/thm-sfb-extend-scalars-localization.proof.md, Conclusion; explicit quasi-inverse and transport of the universal property.

Proof length: 1685 characters.

### lem-sfb-rational-derived-scalar-invertible

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, F inverts W: multiplication by ell on rational coefficients is invertible.

1. The constant functions with values $\ell$ and $\ell^{-1}$ multiply to $1$ on every profinite set, since $E$ has characteristic zero. They therefore give mutually inverse global scalar sections of $\underline E$. Pulling their unit and multiplication identities along the monoidal $p_X^*$ gives inverse scalar sections of $E_X$.

   Uses: `sk-def-sfb-condensed-ring`, `sk-def-sfb-pulled-back-coefficients`. Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.8.2(2), continuous coefficients.

2. For an internal $E_X$-module, compose the coefficient action with either scalar section tensored with its identity. Associativity and the unit axiom show that the two resulting module endomorphisms compose to the identity in either order. Every module morphism commutes with them by the action-morphism equation. Consequently they act degreewise as inverse chain maps on every complex; their images under the derived localization remain inverse. This is independent of the representative by that same naturality.

   Uses: `sk-def-sfb-module-objects`, `sk-def-sfb-derived-categories`. Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.8.2(2); explicit inverse on modules and complexes.

3. For $n=0$ the map is the identity. For $n+1$ use $\ell^{n+1}\operatorname{id}=(\ell^n\operatorname{id})\circ(\ell\operatorname{id})$; the inverse is the corresponding composite of inverse scalar maps. Induction gives the assertion and the stated inverse.

   Uses: elementary calculation. Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.8.2(2); powers of the inverse scalar.

Proof length: 1093 characters.

### lem-sfb-integral-localization-hom-colimit

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Full faithfulness: the displayed commutation of Hom with the scalar telescope for bounded constructible K and B.

1. Choose the strict bounded-below complex model of $t_B$ supplied by [lem-weil-pbc-integral-localization-complex-model]; its comparison identifies every cocone leg, not just the vertex. To use [lem-weil-pbc-integral-localization-colimit-transport] with $\operatorname{Hom}(K,-[q])$, it remains to verify continuity on the good-truncated scalar telescopes of a strictly bounded-below complex $C$.

   Uses: `lem-weil-pbc-integral-localization-complex-model`, `lem-weil-pbc-integral-localization-colimit-transport`. Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.8.12 and Proposition 6.8.14(2).

2. If $C$ is zero below $a$, its good-truncation comparison is a termwise isomorphism, so its indicated cocone is a genuine complex colimit and all stages have cohomology zero below $a$. Reindex along $\operatorname{AsSmall}(\mathbf N)\simeq\operatorname{ULift}\mathbf N$. The sheaf-source theorem [lem-weil-pbc-integral-constructible-sheaf-hom] gives the canonical comparison in every shift for each constructible module in degree zero.

   Uses: `lem-weil-pbc-integral-constructible-sheaf-hom`. Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.8.12 and Proposition 6.8.14(2).

3. For this fixed diagram and cocone, continuity is unchanged by source isomorphism (precompose every Hom group by that isomorphism) or by source shift (replace $q$ by $q-r$ for a source shifted by $r$), and holds for zero. Choose cohomological bounds $b\leq c$ for $K$. Start with $\tau_{\leq b-1}K=0$. For $r=b,\ldots,c$, the truncation triangle has endpoints $\tau_{\leq r-1}K$ and $H^r(K)[-r]$; continuity for the first is the induction hypothesis and for the second the sheaf case. Apply [lem-weil-pbc-hom-colimit-extension] to obtain it for $\tau_{\leq r}K$. At $r=c$ this is $K$.

   Uses: `lem-weil-pbc-truncation-triangle`, `lem-weil-pbc-hom-colimit-extension`. Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.8.12 and Proposition 6.8.14(2).

4. Apply the colimit-transport theorem to each shifted Hom functor and the strict model chosen in step 1. Its leg compatibility identifies the comparison with the canonical map in the statement. Reindexing by the inverse equivalence identifies cocones and their universal properties, yielding both indexing conventions.

   Uses: `lem-weil-pbc-integral-localization-colimit-transport`. Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.8.12 and Proposition 6.8.14(2).

Proof length: 1726 characters.

### lem-sfb-scalar-unit-equality-detection

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-thm-sfb-rationalization-comparison/thm-sfb-extend-scalars-localization.proof.md, Full faithfulness; adjunction and finite-stage equality, expanded by the agent.

1. Apply the adjunction Hom bijection to $F(f)=F(g)$. Its unit formula and naturality give $\eta_B\circ f=UF(f)\circ\eta_K=UF(g)\circ\eta_K=\eta_B\circ g$. Since $t_0=\eta_B$, $f$ and $g$ represent the same element of the asserted Hom colimit at stage zero.

   Uses: elementary calculation. Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-thm-sfb-rationalization-comparison/thm-sfb-extend-scalars-localization.proof.md, Full faithfulness; adjunction unit formula.

2. Regard abelian groups as $\mathbf Z$-modules and apply [lem-weil-pbc-filtered-colimit-modules-elementwise], clause (2). There is a common stage $n$ and two transition arrows from zero whose images of $f,g$ agree. The natural-number indexing category is thin, so those arrows coincide.

   Uses: `lem-weil-pbc-filtered-colimit-modules-elementwise`. Source: literature/stacks-project/algebra.tex, Tag 00D6, lemma-directed-colimit; Tag 00D7, lemma-zero-directed-limit.

3. The transition $0\to0$ is the identity. If the transition $0\to n$ is $a^n\operatorname{id}_B$, its composite with $a\operatorname{id}_B$ is $a^{n+1}\operatorname{id}_B$ by bilinearity. Induction therefore identifies postcomposition to stage $n$ with multiplication by $a^n$ on Hom. The equality at that stage is exactly $a^nf=a^ng$.

   Uses: elementary calculation. Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-thm-sfb-rationalization-comparison/thm-sfb-extend-scalars-localization.proof.md, Full faithfulness; transition calculation.

Proof length: 871 characters.
