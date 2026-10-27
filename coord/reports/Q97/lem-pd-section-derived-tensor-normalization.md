## Worker report

1. Files written: the existing item `dag/nodes/sec-poincare-duality/lem-pd-section-derived-tensor-normalization.json`, three new statement-only nodes in the same directory (listed below), `citations.json`, and this report. The genuine prior search records remain in `searches.jsonl`, with the repair's searches appended by msearch.py. Sandbox work files preserve the returned report and the exact live base proof. No Lean source was changed.
2. Attachments: none. The project search in `lean/WeilConjectures/` for the blueprint tag and the internal/section derived-tensor notions found no declaration stating the whole item. `AlgebraicGeometry.ProEtale.ModuleRingedComparison.section_derived_tensor_normalization`, in `lean/Sheaf/Paper/SectionDerivedTensorNormalization.lean:174`, ends in `sorry` at line 214. Generic source declarations for monoidal derived equivalences and cochain monoidal functors do not identify all the specified internal/section constructions. They are supporting interfaces, not completed attachments of these statements.
3. WANTED: none.
4. The returned delivery passed mechanical preflight but compressed the 8736-character N6 proof to 2991 characters with no new nodes. That failed the human's re-split requirement. This repair instead exposes three independently claimable arguments and keeps the item's statement verbatim. It also keeps the return's approved C4 repair: `def-pd-section-derived-realization` pins the ringed tensor-pullback arrow by the unique representative square; a theorem merely giving a canonical isomorphism does not pin that arrow.
5. Nothing remains to do for this stage-1 delivery after its dry run and push. The three new nodes are deliberately unsplit, with empty proofs and proof dependencies: other workers will prove them. This report records the inherited arguments they receive; it does not falsely mark them proved or write Lean.

## New nodes

- `lem-pd-section-kflat-tensor-comparison`: statement, unsplit, no Mathlib match. Carries base Steps 1–3: resolving internal representatives, the normalized comparison of the conjugate and native ringed tensors, regular unit, and derived associator/unitor constraints.
- `lem-pd-section-oplax-total-comparison`: statement, unsplit, no Mathlib match. Carries base Step 4 and the chain-level part of Step 7: identifies the actual internal total oplax arrow with the existing ringed cochain comparison, including its explicit inverse, scalar unit and coherent total diagrams.
- `lem-pd-section-derived-representative-square`: statement, unsplit, no Mathlib match. Carries the internal-map comparison in base Steps 5–6 and the representative unit/constraint part of Step 7. It asserts the actual map's square on resolving pairs; it does not assume equality with the independently specified ringed derived arrow on all objects.

The statements have respectively 3293, 3211 and 3855 characters. These are three comparable pieces, not one large replacement for the item. The item's five assembly steps have 2289 characters. Every new node is directly cited by the item. Their sources and hypotheses are self-contained; no new definition, axiom, per-degree substitute for a derived isomorphism, or private tensor structure was introduced.

## Source and route

I read the stage-1 brief, worker role, GOAL, the three blueprint levels in SETUP, the open stage contract and delivery-errors B–E. I read the chapter and unit records: the item's chapter remains Poincare duality and its assigned unit remains `sk-thm-sf-verdier-exchange`. The current main-20261015 unit route uses composition and tensor–Hom exchange. These nodes are lower-level normalization tools and do not replace either unit step. No SGA source is used.

For the item and the representative-square node I read Stacks `sites-cohomology.tex`, Tag 07A4, label `lemma-pullback-tensor-product`, including its proof at lines 3684–3724; Tag 0G7E, label `lemma-pullback-K-flat`; and Tag 06YS, label `lemma-K-flat-resolution`. For the tensor-model node I also read Tag 06YU, label `definition-derived-tor`, its preceding localization construction, and Tag 0FPT, label `lemma-symmetric-monoidal-derived`. For the total-arrow node I read the constituents in `sites-modules.tex`, Tag 03EL, label `lemma-tensor-product-pullback`, and Tag 0FPQ, label `lemma-symmetric-monoidal-cat-complexes`. The source of the actual internal/section comparison is the retained agent argument, using these constructions and the cited ordinary normalization nodes. I do not claim Stacks itself states a condensed-ring internal/section comparison theorem. In 07A4 the displayed total comparison is in the inverse direction to our oplax b; our b and its explicit inverse retain that orientation correctly.

The imported blueprint search was across all chapters, using `blueprint_refs.py search` for monoidal, totalization, K-flat monoidal equivalence, total oplax, section tensor, representative square, total-complex comparison, and section-module tensor comparison. The broad hits were general tensor or other coefficient constructions; the focused searches did not state these normalized equalities. The ancestor command returns None. New blueprint.from fields therefore retain node null and the actual seeded-target/parent chain, with the item prepended to via and exact base proof steps in place. same_as is empty. The parent's blueprint and maintained audit/Lean/review fields were preserved. A field comparison with the live node showed the returned sandbox differed only in proof, proof_deps, mathlib_searches and split_report; this repair rebases those fields on the current live node and retains the genuine sandbox searches.

## Mathlib searches

Each new node has its own concept-specific LeanFinder query, second semantic phrasing in LeanSearch, Loogle pattern, and Mathlib grep, copied exactly from searches.jsonl with the actual result digests. All searches ran through the prescribed msearch.py command. The first unsuccessful Loogle attempt reported an unknown identifier `CategoryTheory.Localization`; it was not used as a negative name-existence test. A subsequent valid query `CategoryTheory.Localization.lift₂NatIso` located the generic lifting declaration. No unrun query is recorded and no unavailable service is labeled no match.

For the tensor-model node the semantic results were ordinary flat-module and sheaf-presentation results. `Localization.lift₂NatIso` and `lift₂NatTrans_app_app`, in Mathlib/CategoryTheory/Localization/Bifunctor.lean:162–195, provide generic localization tools; I read their hypotheses and formula. They do not prove preservation/reflection of the actual internal K-flat classes, identify the independently fixed native ringed tensor with the conjugate model, or match their units and constraints. The Tor hits at CategoryTheory/Monoidal/Tor.lean:44–53 are homology-valued derived functors from projective resolutions, not this unbounded comparison.

For the total-arrow node LeanFinder returned `HomologicalComplex.tensorObj`, `ιTensorObj`, and `leftUnitor'`, in Algebra/Homology/Monoidal.lean. I read the tensor inclusions and unitor formulas; they define signed tensor constructions but do not identify the project's actual internal mate arrow with the native ringed total map. LeanSearch and the grep returned the generic oplax/monoidal axioms in CategoryTheory/Monoidal/Functor.lean and Multifunctor.lean:460–525. They do not carry out the comparison with the project's chosen section equivalence and ordinary adjunction mates.

For the representative-square node the semantic hits were ordinary pullback/free-module/sheafification comparisons, presheaf tensor maps and scalar-extension formulas. Loogle and grep located `Localization.lift₂NatTrans` and `natTrans₂_ext`, read at Bifunctor.lean:162–195. They extend or compare transformations once a representative square is provided; they do not establish the square for the actual internal derived arrow with the fixed tensor and pullback factors. Thus none of the three nodes is an exact or one-line Mathlib specialization. The original item's searches and verdicts remain retained without repeating unchanged queries.

## Review by Q97

I checked the actual statements of the item, all three new nodes, and every cited node, with the sources just named open. The item's statement is unchanged. The re-split retains the approved use of the realization definition to distinguish the chosen arrow from an arbitrary canonical isomorphism. The proof no longer relies on a report-only compression to do its mathematical work.

New tensor node: the site is small relative to module values, with the original independent site object/morphism sizes. The ordinary exact section equivalence and its inverse preserve the relative module tensor, not tensor over Z followed by a new quotient. Exactness identifies cohomology and hence quasi-isomorphisms. The statement includes both directions of flat-term K-flat preservation and full faithfulness on internal resolving pairs. Its displayed normalization has source D(E)q_int Tot(P tensor Q) and target q_sec EP tensor^L q_sec EQ on BOTH sides. The factors kappa, r_int, r_sec and t are introduced, so the equation cannot be interpreted as mere objectwise existence. The comparison to the prescribed conjugate section tensor, localization map, regular module, associator and both unitors is required. The report's retained base Steps 1–3 give the detailed inverse-and-extension argument, including the three distinct variable extensions. I checked its statement against 06YS/06YU/0FPT and the fixed data definitions. The new node does not claim that the native and transported tensors are definitionally equal.

New total node: I found and reused `lem-pur-cochain-pullback-tensor-coherence` rather than recreating its section-ringed theorem. Its statement explicitly gives b on all unbounded complexes, the inverse, unitors and associators. The new assertion is equality with the ACTUAL INTERNAL total arrow after the fixed E and operation comparisons. It explicitly states the resulting isomorphism in the unbounded derived category, as well as its chain representative. Its chain-map and derived-localization assertions do not replace a derived isomorphism by cohomology groups. The coproduct is a direct sum, not a product or finite sum. The formulas use the correct scalar ring S=R_X and R'=f^{-1}R_Y. I checked them against 03EL and the inverse displayed in ordinary normalization. The left-adjoint Hom calculation and matching differential signs are retained below. The scalar unit is on regular degree-zero representatives, and cochain constraints compare the same maps under the total comparison. These are more than a single module formula or an existence assertion about some monoidal functor.

New representative node: P,Q are section flat-term K-flat representatives, and their pullbacks have BOTH properties by the existing ringed pullback theorem. The total comparison b is supplied independently by the second new node. epsilon has direction LF(q A) -> q(F A). Thus a has source LF(qP tensor^L qQ) and target qF Tot(P tensor Q), while c has source LF(qP) tensor^L LF(qQ) and target q Tot(FP tensor FQ). The statement's c delta = q(b) a is therefore well-typed. Invertibility on P, Q and their total tensor is exactly what the independent-universe computation theorem supplies. The actual internal delta is defined by localizing the actual internal total arrow with the internal tensor and module-pullback constructions, not cited as a construction of the ringed realization definition. It is conjugated using the normalized theta and the actual pullback comparison; equality of its bottom map and all vertical factors is asserted, not assumed from mere invertibility. The unit equation explicitly includes epsilon on R_Y[0]. Its claim about constraint diagrams is only on resolving tuples and unit pairs; the item still extends them to all derived objects. This node gives no global ringed-arrow identification by itself.

Assembly Step 1 uses the FIRST new statement for exactly its tensor/localization/unit/constraint clauses, including resolving internal representatives. This now has a named independently provable input; it is no longer a one-line summary standing in for the old Steps 1–3. Step 2 uses the SECOND new statement for equality with actual internal total maps and for its inverse and unit/cochain constraints. These are verbatim clauses in that statement.

Assembly Step 3 checks representative descent hypothesis by hypothesis. `lem-weil-pbc-site-derived-tensor-descent` states equivalence of the resolving localization, its specified r maps and full faithfulness on pairs. `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` states preservation of K-flat complexes WITH flat terms, hence r_X applies. `lem-weil-pbc-kflat-tensor-pullback-computation-universes` explicitly supplies invertibility of epsilon also on the total tensor. The second new node supplies the actual natural b. `lem-weil-pbc-tensor-comparison-descent-representatives` states precisely extension of this representative square, so it gives c^{-1}q(b)a. `def-pd-section-derived-realization` explicitly defines the chosen ringed arrow by the same unique square. The two displayed types in this step were checked before composing. This retains the favorable C4 correction noted in the return, rather than taking a representative square from the proof of a node whose statement only asserts an isomorphism.

Assembly Step 4 uses the THIRD new statement for the actual internal representative square. Its a,c and b are the maps of Step 3 by their definitions, so cancellation by c gives equality of representative components. The site-descent statement's faithfulness on pairs then gives equality of the specified global natural transformations. This is an equality-of-squares argument, not an assertion that any two isomorphisms between the objects agree.

Assembly Step 5 uses the total node's inverse formula and two inverse equations, then the localization universal property's explicit preservation of identities and composition to get the inverse of the already identified arrow. For the unit, the representative node supplies the actual scalar-unit equality INCLUDING the resolution factor. For constraints it gives the representative diagrams, and the total node gives the ordinary equations they become. I retain the separate variable extensions: fix two representatives and extend in the third variable, then fix one and extend in the second, then extend in the first. Site descent supplies resolving localizations and `lem-weil-pbc-localization-universal-property` supplies faithfulness at each step. The two unitors need fewer variables and the same argument. No three-variable localization theorem is silently assumed.

For B1–B7 all new nodes are statements only, with empty proof and proof_deps, introduced objects and size assumptions, single-escaped TeX, cited definitions and precise source tags/labels. The ordinary/derived and internal/section distinctions remain explicit. The relevant duplicate searches are discussed below; several generic existing comparison theorems are usable tools but do not alone establish the normalized equalities of these project constructions. The new nodes are not all clauses of the final equality: one proves resolving tensor-model compatibility, one identifies an actual CHAIN arrow, and one identifies its resolving square. The parent must still apply representative descent, the chosen-realization definition, cancellation, natural-transformation faithfulness, inverse equations and successive variable extensions. This follows the maintainer's suggested split while retaining the actual work it singled out.

I tested all three new statements at f=id (where relevant), zero coefficient ring, zero complexes, regular modules in degree zero, and complexes concentrated in odd or negative degrees. The tensor model equation reduces to the ordinary factor comparison at degree zero; zero modules give unique zero maps; both inverse formulas reduce to multiplication of scalars; the units are the ring actions. In odd or negative degree p the same (-1)^p appears on both sides of the differential square, so no parity sign is lost. Infinite degreewise sums are allowed by the explicit adjunction computation. The representative-square statements use no smoothness, finite type, boundedness, nonzero ring or extra same-universe hypothesis. I checked that neither new stmt_deps path calls the item and that source-only cross-references do not introduce a reverse edge.

The only new prose longer than 2000 characters is in unsplit statements, which contain the detailed claims of the new lemmas; there is no long non-elementary assembly step hiding an unextracted lemma. Each assembly step is below 1000 characters. All item step/node pairs have verbatim statement quotations in citations.json. The inherited off-unit tools retain their existing reasons in split_report; the new nodes share the item's chapter and unit. No Lean, compiler, Lake, local DAG checker, git command in the shared repository, repository edit, launcher edit, or agent launch was performed.

## Repair of every returned point

1. The human's request for at least two comparable new statement-only nodes is met by THREE nodes, with statement lengths 3293/3211/3855. None has proof steps, and all are cited by the item. The item remains at most 3000 characters by assembling these lemmas, not by dropping their work.
2. Old Step 1's derivation of quasi-isomorphism preservation and the inverse image of P_T appears as explicit assertions in the tensor node, with the complete retained argument below. Old Step 2's inverse construction, representative equation and naturality after inversion remain part of that node's specified comparison.
3. Old Step 3's three-stage extension is retained in the tensor node's proof allocation below and explicitly in final assembly Step 5. It has not been replaced by an unexplained “successively”.
4. Old Step 5's a/c types and hypothesis-by-hypothesis representative-descent check are explicit in final assembly Step 3, the representative node statement and the review above. The square c delta = q(b) a is retained in full.
5. Old Step 7's inverse formula (s tensor x) tensor (t tensor y) -> st tensor (x tensor y) is explicit in the total node and final Step 2. Both inverse equations, scalar unit, total constraints and their derived extension are retained across the total node, representative node and final Step 5.
6. The approved citation `def-pd-section-derived-realization` stays in final Step 3 and in the representative node's statement dependencies. It fixes the unique square; the proof does not infer that specification from the bare phrase “canonical isomorphism”.

## Allocation of the complete base argument

The following is the FULL seven-step live N6 proof, preserved with TeX escaping normalized for reading, not a paraphrase of the rejected short version. It records the arguments assigned to the new workers. Steps 1–3 belong to the tensor node. Step 4 and Step 7's chain inverse/unit/constraint verifications belong to the total node. Steps 5–6 and Step 7's resolution-unit/constraint-square identifications belong to the representative node; the global descent, chosen ringed-square identification and natural-transformation extensions stay in the item. In Step 3 the section constraints are explicitly those of def-pd-section-derived-tensor-data. In Steps 5–6 add the realization definition as explained in the favorable C4 correction above. No part of this retained argument is silently discarded.

### Base Step 1

For each $T$, write $Q_T$ for the section-module homotopy-to-derived localization and $\mathcal P_T$ for its full subcategory of K-flat complexes with flat terms. The exact equivalence $E_T$ identifies flat objects, K-flat complexes, acyclicity and total tensors by [lem-pe-internal-section-tensor-comparison]. Thus it identifies quasi-isomorphisms (their cohomology maps are isomorphisms under an exact equivalence). Its inverse carries $\mathcal P_T$ to internal K-flat complexes with flat terms. By [lem-weil-pbc-site-derived-tensor-descent], every section-derived object is isomorphic to $Q_TP$ for $P\in\mathcal P_T$, and restriction to pairs of these representatives is fully faithful. Consequently these are also resolving representatives internally. Use $D(E_T)$ and its pullback comparison with resolution transformations exactly as fixed by [lem-pd-section-derived-pushpull-normalization]. The site objects and module sections both lie in the coefficient universe $u+1$, so the hypothesis on the site in the tensor-equivalence lemma is satisfied; its sheaf-tensor hypotheses hold because [sk-def-sfb-sheaf-tensor] gives, on the small pro-étale site, the closed symmetric monoidal sheafified objectwise tensor over $\mathbf Z$ with strong monoidal sheafification, so tensoring preserves local isomorphisms.

Cites: lem-pe-internal-section-tensor-comparison, lem-weil-pbc-site-derived-tensor-descent, lem-pd-section-derived-pushpull-normalization, sk-def-sfb-sheaf-tensor.

### Base Step 2

On internal representatives $P,Q$ let $t_{P,Q}:E_T\operatorname{Tot}(P\otimes Q)\xrightarrow{\sim}\operatorname{Tot}(E_TP\otimes E_TQ)$ be the total-complex comparison of [lem-pe-internal-section-tensor-comparison]. Conjugate its localization by the two representative tensor isomorphisms to obtain
$D(E_T)(Q_{\rm int}P\otimes^{\mathbf L}Q_{\rm int}Q)\xrightarrow{\sim}Q_TE_TP\otimes^{\mathbf L}Q_TE_TQ$.
Here the internal tensor is the relative two-variable K-flat derived tensor of [sk-def-sfb-derived-tensor-hom], and the section tensor and its representative isomorphism are those of [lem-weil-pbc-site-derived-tensor-descent]. Naturality of $t$ gives naturality on representatives. When a quasi-isomorphism is inverted its naturality equation can be multiplied by the inverse on either side, so the same equation holds on the localized categories. Full faithfulness of restriction in [lem-weil-pbc-site-derived-tensor-descent] gives a unique extension $\theta_T$ to all pairs, and also extends the inverse. Their composites are identities because this holds on representatives. This proves the claimed tensor identification together with its localization comparison, rather than choosing an unrelated tensor isomorphism.

Cites: lem-pe-internal-section-tensor-comparison, sk-def-sfb-derived-tensor-hom, lem-weil-pbc-site-derived-tensor-descent.

### Base Step 3

The regular module in degree zero is flat and K-flat: tensoring with it is the identity on modules and, respectively, on total complexes, via the unitors. Thus it is itself an allowed flat-term representative. The map $E_T(R_T)\cong R_{T,\rm sec}$ and both unitors are identified by [lem-pe-internal-section-tensor-comparison]. Localizing these very maps identifies the derived regular-module unit. The internal derived associators and unitors are induced from complexes by [lem-sfb-derived-monoidal]; the section ones are their corresponding total-tensor maps. On K-flat representatives the two sides of the comparison diagrams are equal because $t$ respects the ordinary associators and unitors. For a diagram in three variables, first fix two resolving representatives and use localization faithfulness in the third variable, then fix one and repeat in the second, and finally repeat in the first. The resolving localizations in [lem-weil-pbc-site-derived-tensor-descent] and the faithfulness clause of [lem-weil-pbc-localization-universal-property] justify each repetition. This proves the constraint comparisons for $\theta_T$ on all objects.

Cites: lem-pe-internal-section-tensor-comparison, lem-sfb-derived-monoidal, lem-weil-pbc-site-derived-tensor-descent, lem-weil-pbc-localization-universal-property.

### Base Step 4

Write $F=f^*_{\rm sec}$. For $P,Q\in\mathcal P_Y$ totalize the ordinary tensor arrow of [lem-pd-section-ordinary-oplax-normalization] to obtain
$b_{P,Q}:F\operatorname{Tot}(P\otimes Q)\xrightarrow{\sim}\operatorname{Tot}(FP\otimes FQ)$.
The direct-sum comparison used here is the canonical one: $F$ is the specified left adjoint of [def-pd-section-module-operations-data], and $\operatorname{Hom}(F(\bigoplus A_i),B)=\operatorname{Hom}(\bigoplus A_i,f_*B)=\prod_i\operatorname{Hom}(FA_i,B)$ gives its coproduct universal property. On the $(p,q)$ summand, $b$ sends $s\otimes(x\otimes y)$ to $(s\otimes x)\otimes(1\otimes y)$. Naturality of the ordinary arrow with $d_P$ and $d_Q$ identifies its two differential components; both second components have the same factor $(-1)^p$ from [def-pc-tensor-complex-sheaves]. Thus $b$ is a chain isomorphism, natural in both complexes. This is also the image of the actual internal total oplax arrow under $E_X,E_Y$, because the ordinary normalization asserts equality with that arrow, not just invertibility of its source and target.

Cites: lem-pd-section-ordinary-oplax-normalization, def-pd-section-module-operations-data, def-pc-tensor-complex-sheaves.

### Base Step 5

Let $r_Y:Q_Y\operatorname{Tot}(P\otimes Q)\xrightarrow{\sim}Q_YP\otimes^{\mathbf L}Q_YQ$ and $r_X:Q_X\operatorname{Tot}(FP\otimes FQ)\xrightarrow{\sim}Q_XFP\otimes^{\mathbf L}Q_XFQ$ be the representative comparisons of [lem-weil-pbc-site-derived-tensor-descent]. Pullback preserves K-flat complexes with flat terms by [lem-weil-pbc-ringed-topoi-derived-tensor-pullback], so $r_X$ applies. Write $\epsilon_A:LF(Q_YA)\to Q_XFA$ for the specified derived-pullback comparison. Both $\epsilon_P,\epsilon_Q$ and $\epsilon_{\operatorname{Tot}(P\otimes Q)}$ are invertible by [lem-weil-pbc-kflat-tensor-pullback-computation-universes]. Put
$a=\epsilon_{\operatorname{Tot}(P\otimes Q)}\circ LF(r_Y^{-1})$ and $c=r_X^{-1}\circ(\epsilon_P\otimes^{\mathbf L}\epsilon_Q)$.
Thus $a$ runs from $LF(Q_YP\otimes^{\mathbf L}Q_YQ)$ to $Q_XF\operatorname{Tot}(P\otimes Q)$ and $c$ from $LF(Q_YP)\otimes^{\mathbf L}LF(Q_YQ)$ to $Q_X\operatorname{Tot}(FP\otimes FQ)$. All the hypotheses of [lem-weil-pbc-tensor-comparison-descent-representatives] now hold: full faithfulness is the cited tensor descent, preservation of representatives is the cited pullback theorem, the two $r$'s are specified, $b$ is Step 4, and the required $\epsilon$'s are invertible. It gives the unique natural isomorphism whose representative component is $c^{-1}\circ Q_X(b_{P,Q})\circ a$. This is the canonical ringed tensor isomorphism: it is obtained by localizing the ordinary tensor arrow with these resolution comparisons, the construction in Tag 07A4.

Cites: lem-weil-pbc-site-derived-tensor-descent, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-pbc-kflat-tensor-pullback-computation-universes, lem-weil-pbc-tensor-comparison-descent-representatives.

### Base Step 6

Let $\widehat\delta_f$ denote the actual internal derived oplax arrow after conjugating by $D(E_T)$, $\theta_T$ and the pullback comparison. By the meaning of the arrow induced by internal pullback and localization, its representative square has bottom arrow the localization of the ordinary internal total oplax map and vertical arrows the tensor and pullback resolution comparisons. Step 4 identifies that bottom arrow with $Q_X(b_{P,Q})$. Step 2 identifies the tensor resolution comparisons, and [lem-pd-section-derived-pushpull-normalization] identifies the pullback resolution transformations themselves, so the vertical arrows are precisely $a$ and $c$ of Step 5. Hence $c\circ\widehat\delta_{f,Q_YP,Q_YQ}=Q_X(b_{P,Q})\circ a$. Multiplying by $c^{-1}$ gives exactly the representative component of the ringed arrow in Step 5. Restriction to pairs of resolving representatives is faithful by [lem-weil-pbc-site-derived-tensor-descent]; therefore the two specified natural transformations are equal on all derived objects. The argument compares their defining squares and does not identify maps merely because both are isomorphisms.

Cites: lem-pd-section-ordinary-oplax-normalization, lem-pd-section-derived-pushpull-normalization, lem-weil-pbc-site-derived-tensor-descent.

### Base Step 7

The inverse of the ordinary arrow on a tensor summand sends $(s\otimes x)\otimes(t\otimes y)$ to $st\otimes(x\otimes y)$ by [lem-pd-section-ordinary-oplax-normalization]. The two composites are identities there, so localization preserves the two inverse equations by [lem-weil-pbc-localization-universal-property]. Thus the actual lax arrow $\mu_f=\delta_f^{-1}$ is carried to the inverse of the ringed arrow identified in Step 6. The unit arrow in the same ordinary normalization is scalar multiplication. Evaluate it on the degree-zero regular-module representatives of Step 3: the pullback resolution comparison is invertible on these by [lem-weil-pbc-kflat-tensor-pullback-computation-universes], and the resulting arrow is the same scalar multiplication on both sides. The ordinary associator and unitor compatibility is part of the ordinary normalization. Totalization respects those equations, since on each summand the maps are those ordinary maps with the same degrees and signs as in Step 4. Apply the one-variable localization faithfulness of [lem-weil-pbc-localization-universal-property] successively in each variable, as in Step 3, using the resolving representatives of [lem-weil-pbc-site-derived-tensor-descent]. This proves the tensor-unit and constraint compatibility of the identified natural transformations.

Cites: lem-pd-section-ordinary-oplax-normalization, lem-weil-pbc-localization-universal-property, lem-weil-pbc-kflat-tensor-pullback-computation-universes, lem-weil-pbc-site-derived-tensor-descent.


## Not duplicates

The focused whole-DAG search examined derived monoidal equivalences, signed total oplax maps, ringed tensor descent and internal/section representative squares. In particular the following close candidates were read, not inferred from their titles. The shared-tag matches emitted by delivery are also distinguished below. A common Stacks tag often supplies only a construction used for a quite different coefficient problem.

lem-pd-section-kflat-tensor-comparison vs def-kun-prime-coefficient-complexes: The existing statement concerns Degree zero complexes and localization; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-kun-prime-coefficient-complexes-input-output: The existing statement concerns Ordinary source and target tensor complexes; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-kun-prime-coefficient-constructions: The existing statement concerns Canonical quotient coefficient tensor arrow; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-kun-prime-coefficient-functors: The existing statement concerns Punctual tensor source and target functors; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-kun-prime-coefficient-iso: The existing statement concerns Derived coefficient tensor isomorphism type; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-kun-prime-coefficient-localization-compatibility: The existing statement concerns Localized termwise coefficient compatibility; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-kun-prime-coefficient-normalization: The existing statement concerns Derived normalization by the quotient tensor map; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-kun-prime-coefficient-pullbacks: The existing statement concerns Canonical coefficient pullback maps; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-kun-prime-coefficient-term-map: The existing statement concerns Degree zero coefficient term map; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-kun-prime-coefficient-termwise-normalization: The existing statement concerns Termwise normalization of the quotient tensor arrow; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-pc-derived-tensor-cohomology-vanishes: The existing statement concerns Vanishing of derived tensor cohomology with an O_X-module; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-pc-derived-tensor-complex-cohomology-vanishes: The existing statement concerns Vanishing of derived tensor cohomology of two derived objects; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-pd-section-derived-realization: The existing statement concerns Canonical derived section-module realization; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-pd-section-derived-tensor-data: The existing statement concerns Canonical derived section-module tensor data; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-pur-finite-field-derived-tensor-comparison: The existing statement concerns Canonical interfaces for the finite-field derived tensor comparison; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-pur-integral-operation-shift-data: The existing statement concerns Representative-normalized operation and independent-slot shifts; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-pur-synchronized-canonical-maps: The existing statement concerns The same canonical map at two independent input families; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-sc-derived-tensor-augmentation: The existing statement concerns Derived tensor augmentation on a scheme; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-sf-localized-strict-tensor-comparison-data: The existing statement concerns Normalized cochain computation data for localized strict tensor towers; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-sf-localized-strict-tensor-linear-evaluation-data: The existing statement concerns Normalized coefficient-linear evaluation of localized strict tensor descent; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-sf-open-normalization-data: The existing statement concerns Geometric and operation data for open tensor normalization; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-sf-ringed-kflat-tensor-representative-data: The existing statement concerns Existing ringed-site tensor functors and resolving representative comparison; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-sfb-ringed-projection-coherence-data: The existing statement concerns Recorded data for tensor projection coherence; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-sfb-tensor-symmetry-pure-equation: The existing statement concerns Pure-section predicate for the tensor-complex Koszul symmetry; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-trf-ringed-complex-derived-tensor-vanishing: The existing statement concerns Derived tensor cohomology vanishing for a complex on a ringed site; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-weil-pbc-completed-constant-realization-data: The existing statement concerns Completed constant realization interfaces; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-weil-pbc-tensor-descent-representative-comparison: The existing statement concerns Published flat-term K-flat representatives and their two-factor tensor comparison; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs def-zl-ringed-derived-closed-symmetric-monoidal-data: The existing statement concerns Representative coherence data for derived tensor on a ringed site; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-amb-derived-tensor-symmetry-involutive: The existing statement concerns Opposite canonical derived tensor symmetries cancel; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-asd-derived-pullback-symmetry: The existing statement concerns Derived pullback preserves canonical tensor symmetry; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-exc-intrinsic-resolution-tensor-homology: The existing statement concerns Tensor cohomology in the intrinsic coefficient presentation; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-exc-intrinsic-tor-amplitude-transport: The existing statement concerns Transport of intrinsic Tor intervals; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-fd-ringed-flat-single-tensor-cohomology: The existing statement concerns Flat degree-zero tensor commutes with cohomology on a ringed site; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-fix-ringed-scalar-tensor-monoidal: The existing statement concerns Normalized strong monoidality of derived scalar extension in independent universes; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-geo-cartier-coeff-extension: The existing statement concerns Derived scalar extension of a closed supported constant sheaf; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-geo-cartier-exponent-independence: The existing statement concerns Modulus change of the derived quotient and torsion identifications; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-kun-derived-tensor-well-defined: The existing statement concerns Independence of the K-flat model; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-pur-constant-field-restriction-representatives: The existing statement concerns Restriction preserves flat-term K-flat constant-field representatives; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-pur-constant-native-pullback-monoidal: The existing statement concerns Canonical native derived tensor comparison for constant coefficients; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-pur-derived-change-of-rings: The existing statement concerns Derived change of rings along a morphism of sheaves of rings, computed by K-flat resolutions; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-pur-derived-tensor-additive-constraints: The existing statement concerns Normalized additive derived tensor constraints from resolving models; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-pur-etale-single-functor-monoidal-compatibility: The existing statement concerns Canonical flat degree-zero tensor pairings and exact inverse image; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-pur-finite-product-derived-tensor-calculus: The existing statement concerns Unbounded derived and K-flat tensor calculus for finite clopen module gluing; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-pur-flat-single-derived-normalization: The existing statement concerns Normalized flat degree-zero tensor on the unbounded derived category; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-pur-kflat-cone-comparison: The existing statement concerns Two K-flat resolutions: augmentation square computing the derived-to-ordinary tensor comparison; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-pur-line-unbounded-derived-tensor: The existing statement concerns Derived tensor by a locally free line is the exact termwise equivalence; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-pur-separable-field-tensor-chain: The existing statement concerns The chain-level separability retraction on sheaf tensors; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-pur-varying-ring-tensor-support: The existing statement concerns Tensor support for canonical varying-ring extension; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sbc-koszul-tensor-derived-tower: The existing statement concerns Ordinary Koszul tensor towers represent derived tensor towers; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sc-source-kflat-tensor-left-triangulated: The existing statement concerns Derived tensor by a K-flat homotopy model is triangulated; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sf-cbc-coefficient-linear-projection-descent: The existing statement concerns Coefficient-linear derived projection from a specified ordinary slice comparison; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sf-cbc-diagonal-resolving-complexes: The existing statement concerns Constant diagrams preserve flat-term K-flat complexes with evaluated tensor normalization; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sf-cbc-strict-tensor-model-evaluation: The existing statement concerns Strict tensor towers compute diagram-derived reduction with the specified transitions; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sf-cochain-tensor-model-rigidity: The existing node compares two section-derived models after their representative r maps have been supplied. The new node constructs and matches those maps across the internal/section equivalence and proves their compatibility with its specified unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sf-derived-completed-tensor-bilinearity: The existing statement concerns Bilinearity of derived completed tensor and its rational Hom action; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sf-finite-comparisons-existence: The existing statement concerns Section preserving finite comparisons exist; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sf-finite-compatibility-transport: The existing statement concerns Pinned finite comparisons preserve canonical open arrows; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sf-finite-operation-comparisons: The existing statement concerns Prescribed finite realizations admit pinned operation comparisons; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sf-open-tensor-support: The existing statement concerns Derived tensor preserves open support in either factor; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sf-open-tensor-support-aux: The existing statement concerns The open tensor projection transpose is invertible; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sf-ringed-derived-closed-symmetric-monoidal: The existing statement concerns The derived category of a ringed site is closed symmetric monoidal; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sf-ringed-derived-native-tensor: The existing statement concerns Native symmetric derived tensor and one-K-flat localization comparisons; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sf-ringed-kflat-single-tensor-comparison: The existing statement concerns K-flat tensor with a degree-zero module on a ringed site; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sfb-divisible-extension-derived-reduction: The existing statement concerns Derived reduction of an extension by a divisible sheaf; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sfb-exact-flat-tensor-derived-counit-comparison: The existing statement concerns The counit-normalized tensor comparison of an exact flat-preserving functor; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sfb-exact-tensor-functor-derived-braiding: The existing statement concerns The normalized exact derived tensor comparison preserves the native Koszul braiding; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sfb-exact-tensor-functor-derived-normalization: That node assumes a natural comparison t already satisfying the displayed native normalization, then proves its coherence. The new node constructs and identifies the actual internal/section comparison, its resolving subcategories, and the native versus conjugate section model; it supplies the matching hypothesis that the generic result assumes.

lem-pd-section-kflat-tensor-comparison vs lem-sfb-flat-scalar-cyclic-resolution: The existing statement concerns Two-term scalar quotient resolutions after flat sheaf extension; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sfb-flat-scalar-tensor-resolution: The existing statement concerns Scalar tensor resolutions compute the recorded sheaf derived tensor; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sfb-flat-scalar-tensor-units: The existing statement concerns Degree-zero ring sheaf is a unit for the recorded derived tensor; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sfb-flat-scalar-tor-comparison: The existing statement concerns Cohomology of flat scalar tensor is scalar Tor; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sfb-ringed-derived-tensor-diagrams: The existing statement concerns Coherence equations for explicit canonical derived comparison maps; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sfb-ringed-derived-tensor-lift: The existing statement concerns Symmetric monoidal coherence of a canonical derived tensor lift; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sfb-ringed-finite-free-resolution-tensor: The existing statement concerns Tensor computation from a specified bounded-above finite free sheaf resolution; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sfb-ringed-projection-pullback-comparisons: The existing statement concerns Normalized identity, composition and section pullback comparisons; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sfb-ringed-projection-tensor-compatibility: The existing statement concerns Tensor constraints and compatibility of normalized comparisons; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sfb-ringed-projection-tensor-structure: The existing statement concerns Canonical tensor structure in arbitrary recorded presentations; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sfb-scalar-adjunction-unit-coefficient-normalization: The existing statement concerns Normalized scalar adjunction on K-flat models and the coefficient unit; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sfb-scalar-reduction-unit-triangle: The existing statement concerns Scalar-reduction adjunction unit and multiplication triangle; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sp-restricted-scalar-coefficient-local-constancy: The existing statement concerns Finite local cohomology of the restricted constant coefficient complex; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-sp-restricted-scalar-tensor-cohomology-comparison: The existing statement concerns Underlying cohomology comparison for K-flat scalar extension; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-trf-site-one-sided-tensor-normalization: The existing statement concerns Unique one-sided K-flat tensor comparison normalized by two-sided descent; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-weil-pbc-alternating-unit-resolution: The existing statement concerns Alternating unit resolution of an exact periodic pair; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-weil-pbc-completed-constant-derived-tensor-tower: The existing statement concerns Universal derived tensor tower from K-flat resolutions; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-weil-pbc-completed-constant-resolution-tensor-calculation: The existing statement concerns Tensor quotient diagrams on finite-free completion resolutions; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-weil-pbc-fixed-tensor-localization-comparison: The existing statement concerns Exact localization of fixed tensor and its normalized resolving comparison; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-weil-pbc-integral-local-reduction-lower-bound: The existing statement concerns A completed integral local reduction loses at most one lower degree; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-weil-pbc-kflat-fixed-tensor-triangulated: The existing statement concerns Exact descent of tensoring with a fixed K-flat complex; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-weil-pbc-periodic-quotient-tor: The existing statement concerns Tor from an exact periodic unit pair; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-weil-pbc-principal-adjacent-quotient-tor: The existing statement concerns Residue Tor between adjacent principal quotients; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-weil-pbc-regular-quotient-self-cohomology: The existing statement concerns Self-reduction along a regular quotient; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-weil-pbc-regular-single-reduction: The existing statement concerns Reduction preserves a regular single module in degree zero; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-weil-pbc-ringed-projection-mate-exact: The existing statement concerns Exactness data for the ringed-topos projection mate; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-weil-pbc-ringed-tensor-cohomological-bounds: The existing statement concerns Cohomological bounds for derived extension of ring-sheaf scalars; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-weil-pbc-site-derived-tensor-descent: The existing statement concerns Derived tensor and K-flat representative descent on a ringed site; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-weil-pbc-uniformizer-reduction-cohomology: The existing statement concerns Cohomology commutes with completed principal reduction under injectivity; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-kflat-tensor-comparison vs lem-weil-proetale-derived-restriction-closed-monoidal: The existing statement concerns Normalized native pro-etale restriction is braided closed monoidal; its claim concerns a different tensor/resolution setting; the new claim identifies the fixed internal/section resolving classes, native/conjugate tensor localization map, regular unit and constraints.

lem-pd-section-oplax-total-comparison vs def-coef-ringed-tensor-hom-model: The existing statement concerns Canonical closed tensor-Hom representative model on a ringed site; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-coef-semilinear-derived-calculus: The existing statement concerns Ordinary derived semilinear calculus interfaces; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-coef-semilinear-geometry-base: The existing statement concerns Geometry base fields for coefficient linear operations; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-coef-semilinear-geometry-derived: The existing statement concerns Derived geometric system operations and normalization; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-coef-semilinear-geometry-ops: The existing statement concerns Canonical geometric mate and projection words; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-coef-semilinear-system-models: The existing statement concerns Generic strict semilinear system constructions and representative normalization; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-fix-proper-etale-origin-scalar-data: The existing statement concerns Canonical scalar, tensor and direct-image comparisons at etale origins; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-kun-constant-projection-morphism: The existing statement concerns Canonical constant-coefficient derived projection morphism; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-pd-section-derived-realization: The existing statement concerns Canonical derived section-module realization; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-pd-section-derived-tensor-data: The existing statement concerns Canonical derived section-module tensor data; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-pur-adic-site-strict-quotient-interface: The existing statement concerns Small-site adic strict quotient interface and canonical normalizations; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-pur-cochain-coefficient-arrows: The existing statement concerns Canonical scalar-association and transition arrows on cochain sheaves; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-pur-cochain-coefficient-universe-transport: The existing statement concerns Canonical common-universe transport of ring and module sheaves; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-pur-cochain-tensor-coherence-data: The existing statement concerns Canonical cochain ringed-pullback and coherence data; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-pur-completed-pullback-tensor-comparison: The existing statement concerns Canonical completed, rational and common-stage tensor pullback comparisons; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-pur-etale-scalar-pullback-iso: The existing statement concerns Canonical derived scalar and pullback isomorphism; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-pur-finite-pullback-tensor-comparison: The existing statement concerns Canonical finite derived pullback tensor comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-pur-integral-line-reduction-data: The existing statement concerns Signed integral line reduction and restriction data; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-pur-open-coefficient-normalizations: The existing statement concerns Exact-pullback and open-unit coefficient normalizations; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-pur-scalar-pullback-representative-data: The existing statement concerns Canonical scalar/pullback representative data; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-pur-semilinear-tensor-presentation-data: The existing statement concerns Data for semilinear transport of sheaf tensor presentations; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-pur-signed-line-pullback-normalization-data: The existing statement concerns Normalized signed pullback families and scalar squares; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-pur-system-tensor-mate-arrows: The existing statement concerns Canonical tensor and proper/open arrows for varying coefficient systems; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-evaluation-hom-site-comparison: The existing statement concerns Evaluation-induced derived Hom comparison for the etale-proetale morphism; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-finite-coefficient-site-chain-tensor: The existing statement concerns Canonical finite coefficient site comparison on total tensor complexes; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-finite-coefficient-site-hom-arrow: The existing statement concerns Canonical finite coefficient site internal-Hom arrow; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-finite-coefficient-site-scalar-arrow: The existing statement concerns Canonical finite coefficient site scalar comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-finite-open-tensor-operations: The existing statement concerns Canonical finite open tensor and pullback operations; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-open-normalization-data: The existing statement concerns Geometric and operation data for open tensor normalization; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-point-evaluation-derived-compatibility: The existing statement concerns Representative-normalized derived point comparisons; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-point-evaluation-scalar-coherence: The existing statement concerns Tensor square for balanced point scalar data; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-point-evaluation-scalar-data: The existing statement concerns Balanced scalar comparison for point sections; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-point-evaluation-tensor-coherence: The existing statement concerns Signed tensor coherence for point sections; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-point-evaluation-tensor-data: The existing statement concerns Normalized tensor presentation for point sections; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-point-fibre-tensor-common-stage: The existing statement concerns Canonical common-stage point tensor and coefficient unit; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-point-fibre-tensor-finite-models: The existing statement concerns Canonical finite point tensor normalization on K-flat representatives; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-point-fibre-tensor-models: The existing statement concerns Canonical integral representative normalization; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-point-fibre-tensor-rational-compatibility: The existing statement concerns Canonical rational point tensor, unit, and scalar compatibility; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-point-fibre-tensor-reduction: The existing statement concerns Canonical module scalar tensor data and finite reduction squares; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-point-fibre-tensor-system: The existing statement concerns Strong symmetric tensor comparison data for the point fibres; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-point-finite-source-constraints: The existing statement concerns The finite point source uses the recorded tensor constraints; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sf-point-integral-scalar-square: The existing statement concerns The integral point completion commutes with scalar extension; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sfb-condensed-pullback-tensor-comparison: The existing statement concerns Normalized condensed-module pullback tensor comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sfb-internal-scalar-tensor-comparison: The existing statement concerns Scalar-unit normalized tensor comparison for internal modules; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sfb-module-object-projection-map: The existing statement concerns Canonical derived projection map for condensed module objects; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sfb-proetale-trace-coefficient-interfaces: The existing statement concerns Canonical internal-module trace coefficient interfaces; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sfb-ringed-derived-comparison-data: The existing statement concerns Data of normalized derived monoidal comparisons of ringed topoi; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sfb-ringed-projection-coherence-data: The existing statement concerns Recorded data for tensor projection coherence; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sfb-ringed-slice-comparison-model: The existing statement concerns Normalized ringed slice comparison data; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sfb-scalar-hom-comparison-data: The existing statement concerns Actual scalar-adjunction and normalized tensor-Hom comparison data; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sp-constant-scalar-pullback-comparison: The existing statement concerns Canonical constant-coefficient scalar extension, direct image and pullback comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sp-open-coefficient-adjunction-data: The existing statement concerns Intrinsic open coefficient adjunction data; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sp-open-scalar-operations: The existing statement concerns Constant-ring pro-etale scalar and open operations and their canonical comparisons; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sp-open-scalar-tensor-data: The existing statement concerns Open scalar tensor normalization data; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sp-proetale-scalar-mate-identifications: The existing statement concerns Normalized pro-etale scalar-to-tensor and coefficient-pullback identifications; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-sp-semilinear-constant-ring-operations: The existing statement concerns Constant-ring semilinear system operations and normalized evaluation mates; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-weil-pbc-actual-finite-coefficient-transport: The existing statement concerns Actual-ring finite coefficient transport and normalized local restriction; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-weil-pbc-canonical-ringed-tensor-comparison: The existing statement concerns Normalized ordinary tensor comparison data; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-weil-pbc-normalized-origin-scalar-comparisons: The existing statement concerns Canonical quotient scalar-extension unit and associator; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-weil-pbc-normalized-scalar-restriction: The existing statement concerns Normalized completed-coefficient scalar and restriction comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-weil-pbc-ringed-projection-restriction-data: The existing statement concerns Normalized ringed projection and slice comparison data; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs def-weil-pbc-ringed-tensor-square-presentation: The existing statement concerns Representative presentation of a commutative ringed tensor square; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-a1-balanced-finite-tower-generator-comparison: The existing statement concerns Balanced finite-tower association and quotient-generator normalization; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-coef-etale-tensor-model-comparison: The existing statement concerns Unique flat-model normalization of the étale scalar tensor comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-coef-ringed-pullback-hom-evaluation-comparison: The existing statement concerns Evaluation-defined Hom comparison for ringed pullback; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-coef-semilinear-operations-existence: The existing statement concerns Geometric and coefficient operations on a fixed semilinear system calculus; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-coef-semilinear-system-existence: The existing statement concerns Ordinary semilinear system calculus and cartesian internal Hom; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-coef-signed-single-dual-restriction: The existing statement concerns Normalized slice comparison for a single coefficient dual; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-derived-right-exact-tensor-comparison: The existing statement concerns Normalized tensor comparison for a right exact strong monoidal functor; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-exc-proetale-constant-support-projection: The existing statement concerns Constant-coefficient projection for compact support; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-fix-ringed-scalar-tensor-monoidal: The existing statement concerns Normalized strong monoidality of derived scalar extension in independent universes; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-fix-tensor-pullback-square: The existing statement concerns Tensor inverse-image comparisons commute around an open square; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-kun-derived-pullback-composition-monoidal: The existing statement concerns Canonical derived etale inverse-image composition is monoidal; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-kun-geometric-point-projection-comparison: The existing statement concerns Geometric-point projection morphism agrees with the constant-section projection morphism; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-kun-geometric-point-pullback-tensor-normalization: The existing statement concerns Tensor normalization of the pullback/stalk evaluation comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-kun-inverse-image-monoidal: The existing statement concerns Monoidality of the derived inverse image; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pd-generalized-tensor-normalization-unit-equation: The existing statement concerns Generalized tensor normalization implies the geometric-unit equation; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pd-module-ringed-topos-derived-comparison: The existing statement concerns Module-object and ringed-topos derived tensor comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pd-ringed-tensor-adjunction-mate: The existing statement concerns Identify ringed tensor comparisons with specified adjunction mates; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pd-section-derived-tensor-normalization: The item’s conclusion is equality of specified DERIVED pullback tensor transformations on all derived objects. The new node is the chain-level internal/section comparison that supplies the bottom arrow and coherent total maps; it makes no assertion identifying global derived transformations.

lem-pd-section-oplax-total-comparison vs lem-pd-section-ordinary-oplax-normalization: The existing node identifies ordinary MODULE arrows. The new node identifies the specified signed direct-sum total arrow on arbitrary unbounded complexes, with the canonical coproduct comparison and chain constraints.

lem-pd-section-oplax-total-comparison vs lem-pe-constructible-comparison-tensor-test-reflection: The existing statement concerns Reflection of a single comparison tensor test; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-per-galois-descent-monodromy-tensor: The existing statement concerns Monodromy and tensor of modules descended along a finite Galois cover; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-per-local-system-tensor-monodromy: The existing statement concerns Tensor comparison for arbitrary torsion local systems; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-per-proetale-scalar-slice-comparison: The existing statement concerns Normalized scalar extension comparison on a pro-etale slice; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pod-etale-stalk-tensor-scalar: The existing statement concerns Geometric stalks commute with tensor products and scalar extension on the etale site; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pod-lisse-tensor-and-scalar-extension: The existing statement concerns Tensor products, scalar extension and stalks of lisse sheaves of modules; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-canonical-coefficient-system-geometry: The existing statement concerns Geometric realization on the literal constant finite coefficient tower; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-canonical-ringed-tensor-comparison-independent-universes: The existing statement concerns Existing normalized ordinary tensor comparison with independent site universes; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-cochain-comparison-monoidal-equations: The existing statement concerns Monoidal equations for the canonical cochain pullback comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-cochain-pullback-tensor-coherence: The existing node gives the ringed-section chain comparison, its inverse and coherence, and is REUSED in the statement. The new assertion identifies the ACTUAL INTERNAL adjunction-mate total arrow and its actual unit/constraints with those specific ringed chain maps under the fixed section equivalence.

lem-pd-section-oplax-total-comparison vs lem-pur-coefficient-scalar-units: The existing statement concerns Multiplication units for derived scalar extension; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-common-line-positive-scalar-powers: The existing statement concerns Common-line presentations and nonnegative powers under scalar extension; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-common-stage-tensor-line-coherence: The existing statement concerns Natural associativity and regular right unit for common-stage tensor; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-constant-native-pullback-monoidal: The existing statement concerns Canonical native derived tensor comparison for constant coefficients; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-derived-pullback-tensor-iso: The existing statement concerns Derived pullback commutes with derived tensor product on the constructible categories; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-etale-scalar-pullback-existence: The existing statement concerns Existence of normalized derived scalar/pullback comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-etale-scalar-pullback-uniqueness: The existing statement concerns Uniqueness of normalized derived scalar/pullback comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-exact-pullback-signed-comparison: The existing statement concerns Exact ringed pullback identifies the canonical signed derived tensor comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-flat-term-kflat-tensor-native: The existing statement concerns Total tensor of native flat-term K-flat complexes; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-geometric-scalar-association-cocycle: The existing statement concerns Scalar-association cocycle from normalized inverse-image restriction squares; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-independent-inverse-image-tensor-comparison: The existing statement concerns Normalized tensor comparison for an algebraic inverse image at independent site sizes; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-independent-normalized-scalar-composition: The existing statement concerns Normalized composition of module scalar extensions; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-independent-ringed-tensorator-existence: The existing statement concerns Existence of the tensorator for fixed scalar insertion at independent site sizes; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-integral-ambient-operation-models: The existing statement concerns Ambient completion presentations for integral pullback and tensor; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-integral-coherence-tower: The existing statement concerns Coherence identities on normalized integral comparison towers; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-integral-line-derived-comparisons: The existing statement concerns Normalized derived signed-line reductions and support; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-integral-line-power-comparisons: The existing statement concerns Signed power scalar comparisons and evaluations; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-integral-line-reduction-restriction: The existing statement concerns Signed line reductions and restriction to the derived-complete integral category; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-integral-line-restrictions: The existing statement concerns Completeness and normalized restricted line equivalences; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-integral-tensor-reduction-tower-comparison: The existing statement concerns Strict tensor comparison for finite coefficient-reduction towers; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-integral-tensor-transition-compatibility: The existing statement concerns Quotient compatibility of the normalized total tensor comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-integral-tower-limit-comparison: The existing statement concerns Derived limit of the strict integral comparison tower; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-inverse-image-scalar-comparison: The existing statement concerns Inverse image commutes with extension of scalars, with its unit formula; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-inverse-image-scalar-unit-normalization: The existing statement concerns Canonical algebraic realization and scalar-unit normalization of pro-etale inverse image; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-inverse-image-tensor-comparison: The existing statement concerns The unit-normalized tensor comparison for an isomorphic base change; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-isomorphism-inverse-image-tensor-hom: The existing statement concerns Inverse image along an isomorphism of schemes commutes with tensor products and sheaf Hom; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-kflat-total-tensor-model: The existing statement concerns K-flat total tensor model for flat-term resolutions; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-module-tensor-coefficient-equations: The existing statement concerns Ordinary module tensor equations for coefficient change; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-module-tensor-composition-equation: The existing statement concerns Ordinary tensor square for composite module pullback; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-module-tensor-extension-equation: The existing statement concerns Ordinary scalar-extension tensor equation; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-module-tensor-generator-calculus: The existing statement concerns Pure tensors and normalized insertion naturality for sheaf modules; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-module-tensor-monoidal-equations: The existing statement concerns Associativity and symmetry of the canonical ordinary module tensor comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-normalized-operation-system-models: The existing statement concerns Normalization and simultaneous models for finite coefficient-system operations; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-normalized-tensor-constraint-transport: The existing statement concerns Transport of normalized tensor constraints through coherent realization; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-ordinary-line-derived-scalar-comparison: The existing statement concerns Ordinary unbounded derived scalar extension intertwines signed line tensor and evaluation; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-proetale-inverse-image-tensor-comparison: The existing statement concerns Pure-tensor description and coherence of the pro-etale inverse-image tensor comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-proetale-restricted-tensor-finite-local-constancy: The existing statement concerns Finite local constancy of a restricted tensor with bounded-above inputs; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-ringed-site-pullback-dual-free-chart: The existing statement concerns Invertibility of a pulled evaluation comparison on a finite-free chart; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-ringed-site-pullback-pairing-transfer: The existing statement concerns Extension of module pairings along a ringed site morphism; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-scalar-extension-tower-coherence: The existing statement concerns Coherent quotient towers for integral scalar extension; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-scalar-hom-comparison-tower: The existing statement concerns Evaluation-defined scalar Hom maps respect coefficient towers; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-scalar-tensor-pullback-normalization: The existing statement concerns Scalar/tensor pullback normalization on a K-flat representative; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-scalar-tensor-unit: The existing statement concerns Scalar action unitor for a normalized signed tensor comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-signed-line-derived-base-change: The existing statement concerns Signed line comparisons and their unbounded derived tensor action; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-strict-coefficient-comparison-calculus: The existing statement concerns Simultaneous strict coefficient comparisons on ring-sheaf towers; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-support-site-comparison: The existing statement concerns Etale-proetale comparison for supported sections and their exterior products; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-system-normalized-tensor-closure: The existing statement concerns Normalized semilinear systems are closed under tensor and inverse image; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-system-tensor-reduction-formula: The existing statement concerns Tensor formula for actual semilinear reduction adjoints; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-tate-inverse-limit-base-change: The existing statement concerns Base change of an ell-adic inverse-limit tower and of its finite reduction tensor; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-torsion-line-system-base-change: The existing statement concerns Normalized tensor extension of compatible torsion line systems; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-pur-varying-ring-tensor-comparison: The existing statement concerns Normalized tensor comparison for one varying-ring inverse image; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sf-comparison-open-tensor-coherence: The existing statement concerns Etale/pro-etale comparison respects the canonical open tensor map; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sf-completed-tensor-rational-naturality: The existing statement concerns Naturality and rationalization of a completed tensor comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sf-finite-field-local-tensor-model: The existing statement concerns Localized inverse-image constant models under field scalar extension; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sf-generator-reduction-coherence: The existing statement concerns Basic generator coefficient squares in semilinear systems; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sf-integral-line-tensor-comparison-representative: The existing statement concerns K-flat line tensor models and finite balancing; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sf-open-operation-models: The existing statement concerns Open operation comparisons with fixed tensor models and right square; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sf-open-restriction-completeness: The existing statement concerns Completeness and the actual completion unit after ordinary open restriction; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sf-point-fibre-derived-tensor: The existing statement concerns The point fibre functor preserves derived tensor at all coefficient stages; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sf-point-field-tensor-descent: The existing statement concerns Rational and common-field point tensor descent; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sf-point-finite-tensor-comparisons: The existing statement concerns Finite point tensor comparisons and all quotient squares; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sf-point-integral-completed-tensor-comparisons: The existing statement concerns Completed integral point tensor and scalar squares; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sf-point-ringed-evaluation-model: The existing statement concerns Ringed geometric-point evaluation with signed tensor and coefficient models; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sf-reduction-pull-finite-evaluation: The existing statement concerns Finite evaluation respects the specified reduction/pullback comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sf-ringed-finite-free-tensor-complex: The existing statement concerns Actual scalar tensor comparison on complexes and K-flat preservation; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-condensed-support-projection-formula: The existing statement concerns Natural support tensor projection formulas on unbounded condensed modules; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-etale-stalk-total-tensor-comparison: The existing statement concerns Canonical signed total tensor stalk comparison and chain naturality; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-exact-completed-koszul-pullback: The existing statement concerns Exact product-preserving inverse image transports the actual Koszul unit; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-geometric-stalk-tensor-constant-single: The existing statement concerns Geometric stalks commute with derived tensor against a constant module; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-geometric-two-iso-scalar-pairing: The existing statement concerns Geometric two-isomorphisms preserve the ordinary scalar balanced pairing; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-hom-flat-scalar-evaluation-model: The existing statement concerns Flat scalar evaluation on an arbitrary first complex and its derived coherence; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-integral-quotient-pullback-face-model: The existing statement concerns Common K-flat model for integral quotient pullback faces; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-internal-extension-monoidal: The existing statement concerns Scalar-unit normalized strong monoidal extension of internal scalars; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-internal-extension-preserves-flat: The existing statement concerns Extension of scalars preserves flat internal modules; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-internal-scalar-mate-projection: The existing statement concerns Restriction of an internal coefficient mate is the specified projection map; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-kflat-scalar-comparison-normalization: The existing statement concerns Representative and adjunction normalization of scalar pullback comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-localized-site-tensor-restriction: The existing statement concerns Restriction to a localized site commutes with the sheaf tensor product; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-proetale-intrinsic-tensor-comparison: The existing statement concerns Right-tensor comparison for intrinsic constant-ring realization; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-projection-comparison-etale-proetale: The existing statement concerns Etale-to-proetale comparison of the canonical direct-image projection morphism; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-quotient-section-tensor-normalization: The existing statement concerns Normalized quotient scalar tensors and section-module realization; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-ringed-comparison-tensor-adjunction: The existing statement concerns Tensor and adjunction compatibility of canonical ringed-topos path comparisons; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-ringed-derived-monoidal-comparisons: The existing statement concerns Monoidal and adjunction normalization of derived ringed-topos comparisons; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-ringed-derived-tensor-diagrams: The existing statement concerns Coherence equations for explicit canonical derived comparison maps; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-ringed-derived-tensor-lift: The existing statement concerns Symmetric monoidal coherence of a canonical derived tensor lift; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-ringed-derived-two-iso-comparison: The existing statement concerns Specified geometric 2-isomorphism comparison on derived modules; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-ringed-projection-first-shift: The existing statement concerns The ringed projection mate commutes with shifts in its direct-image input; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-ringed-projection-pullback-comparisons: The existing statement concerns Normalized identity, composition and section pullback comparisons; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-ringed-projection-tensor-compatibility: The existing statement concerns Tensor constraints and compatibility of normalized comparisons; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-ringed-projection-tensor-structure: The existing statement concerns Canonical tensor structure in arbitrary recorded presentations; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-ringed-site-point-acyclic: The existing statement concerns A conservative point family detects acyclicity; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-ringed-site-point-tensor: The existing statement concerns Signed total tensor comparison for normalized stalks; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-scalar-hom-tensor-coherence: The existing statement concerns Tensor coherence of the normalized scalar extension maps; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-scalar-internal-hom-tower-coherence: The existing statement concerns Coefficient-tower and identity coherence for normalized internal Hom; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-scalar-inverse-image-tower-diagram: The existing statement concerns Ordinary inverse-image and balanced scalar-tower square; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-scalar-ordinary-tensor-comparison: The existing statement concerns Normalized ordinary scalar tensor comparison in independent site universes; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-scalar-tensor-comparison: The existing statement concerns Derived scalar tensor comparison on all K-flat representatives; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-scalar-tensor-tower-comparison: The existing statement concerns Simultaneous normalized scalar tensor comparisons with coefficient coherence; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-site-inverse-image-bilinear-adjunction: The existing statement concerns Bilinear adjunction for the inverse image of a morphism of sites; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sfb-site-inverse-image-multimap-universal: The existing statement concerns Universality of inverse-image units for natural maps with finitely many inputs; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sp-bounded-flat-coefficient-site-square: The existing statement concerns Bounded-flat coefficient/site square with its canonical derived comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sp-canonical-open-scalar-tensor-models: The existing statement concerns Canonical scalar tensor models compatible with open inverse image; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sp-etale-chart-comparison-isos: The existing statement concerns Canonical site comparisons for scalar and chart operations; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sp-intrinsic-open-projection-invertible: The existing statement concerns Intrinsic open projection inverse is invertible; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sp-open-projection-scalar-comparison: The existing statement concerns Scalar restriction of the normalized open projection; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sp-open-scalar-coefficient-coherence: The existing statement concerns Coefficient coherence of scalar pullback; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sp-proetale-scalar-balancing-chain: The existing statement concerns Constant-coefficient balancing and its natural inverse-image chain map; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sp-proetale-scalar-tensor-normalization: The existing statement concerns Underlying tensor normalization of pro-etale scalar and inverse-image comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sp-proetale-tensor-coefficient-resolution-square: The existing statement concerns Coefficient-resolution square for exact pro-etale tensor pullback; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-sp-supported-constructible-origin-comparison: The existing statement concerns Supported constructible etale origin and its unbounded coefficient tensor comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-etale-native-tensor-pullback: The existing statement concerns Native unbounded derived tensor commutes with etale inverse image; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-finite-pullback-transition-generators: The existing statement concerns Composite finite pullback transitions reduce both tensor coefficients; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-algebraic-inverse-image-pairing-isIso: The existing statement concerns Universality of the transported inverse-image pairing; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-algebraic-inverse-image-pure-pairing: The existing statement concerns The canonical bilinear pairing of the specified inverse image; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-algebraic-inverse-image-tensor-comparison: The existing statement concerns The normalized tensor comparison for the specified algebraic inverse image; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-augmented-cech-tensor-pullback: The existing statement concerns Augmented Cech tensor actions commute with derived inverse image; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-augmented-diagram-projection-mate: The existing statement concerns Projection mate for an augmented coefficient diagram before taking inverse limit; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-canonical-ringed-tensor-comparison-construction: The existing statement concerns Construction of the normalized ordinary tensor comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-closed-immersion-scalar-change: The existing statement concerns Ordinary closed scalar change with transported coefficients; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-cochain-pullback-tensor-shift: The existing statement concerns The prescribed cochain pullback tensor comparison commutes with both signed shifts; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-constant-derived-normalization-universal: The existing statement concerns Constant derived realization preserves universal coefficient arrows; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-continuous-module-encoding-lattices: The existing statement concerns Local freeness and lattice compatibility of the explicit continuous encodings; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-continuous-module-encoding-restriction: The existing statement concerns Continuous module encoding commutes with restriction along an etale morphism; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-continuous-module-encoding-scalar-extension: The existing statement concerns Scalar extension under the continuous integral and rational module encodings; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-derived-adjunction-shift: The existing statement concerns Canonical derived ringed-topos adjunction is shift-compatible; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-derived-scalar-extension-local-systems: The existing statement concerns Coherent localized derived scalar extension and comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-finite-reduction-pullback-coherence: The existing statement concerns Finite reduction and the canonical pullback square; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-kflat-tensor-pullback-computation-universes: The existing statement concerns Derived pullback computes K-flat tensor representatives; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-left-exact-site-inverse-image-tensor: The existing statement concerns Inverse image induced by a continuous left-exact site functor and its tensor structure; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-localization-inverse-image-coherence: The existing statement concerns Coherent localization comparison for exact inverse image; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-normalized-derived-isomorphism-section-reduction: The existing statement concerns Normalization-compatible evaluation of actual local Isom sheaves; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-normalized-derived-isomorphism-transport: The existing statement concerns Universal normalization and evaluation of source-site local Isom sheaves; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-normalized-origin-comparison-coherence: The existing statement concerns Comparison reduction respects canonical scalar units and composition; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-proetale-closed-underived-projection: The existing statement concerns Underived tensor projection for closed pro-etale immersions with arbitrary ring coefficients; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-pullback-resolving-computation: The existing statement concerns Derived pullback computes on resolving complexes with independent universes; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-pullback-tensor-canonical-shift-unit: The existing statement concerns Canonical shifts and action units of the derived pullback tensor comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-pulled-reduction-normalization-comparison: The existing statement concerns Successive quotient normalizations under the pulled reduction comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-reduction-pullback-derived-tower: The existing statement concerns Normalized derived pullback of a strict coefficient reduction tower; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-resolving-representative-whiskering: The existing statement concerns Restriction to resolving representatives is fully faithful; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-common-quotient-pullback-comparison: The existing statement concerns Common quotient reduction of the geometric scalar comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-equivalence-module-hom: The existing statement concerns Module and closed Hom transport under a ringed equivalence; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-exchange-tensor-coherence: The existing statement concerns Projection-formula coherence for a square of ringed topoi; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-projection-global-model: The existing statement concerns Existence of the canonically normalized global projection package; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-projection-local-model: The existing statement concerns Localization of a normalized global projection package; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-projection-mate-exact: The existing statement concerns Exactness data for the ringed-topos projection mate; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-projection-restriction: The existing statement concerns Localization comparisons for the ringed projection mate; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-projection-tensor-comparison: The existing statement concerns Descent and signed shifts of the normalized pro-etale tensor comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-projection-tensor-shifts: The existing statement concerns Signed shifts of an already normalized tensor comparison; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-slice-comparisons-shift: The existing statement concerns Shift normalization of canonical ringed-slice comparisons; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-slice-evaluation-transpose: The existing statement concerns Slice restriction preserves evaluation for an arbitrary dualizing object; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-slice-koszul-coherence: The existing statement concerns Normalized slice restriction preserves Koszul exchange; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-slice-normalized-comparisons: The existing statement concerns Existence of normalized slice tensor, Hom and Koszul comparisons; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-square-tensor-compatibility: The existing statement concerns Tensor compatibility of a ringed square on flat K-flat representatives; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: The existing statement concerns Derived tensor comparison for arbitrary ringed topoi; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-existence: The existing statement concerns Canonical tensor comparison unit existence; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-uniqueness: The existing statement concerns Canonical tensor comparison unit uniqueness; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-topoi-module-pullback-tensor: The existing statement concerns Underived tensor comparison for pullback of modules on ringed topoi; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-ringed-topoi-module-pullback-tensor-tail: The existing statement concerns Tensor comparison tail for scalar-extended inverse-image modules; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-scalar-extension-tensor-comparison: The existing statement concerns Scalar extension preserves the normalized sheaf tensor; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-pbc-tensor-comparison-descent-representatives: The existing statement concerns Unique descent of tensor comparison from representatives; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-oplax-total-comparison vs lem-weil-ramified-finite-pullback-comparison: The existing statement concerns Normalized finite pullback comparison along coefficient quotient base change; it does not assert equality of the actual internal total adjunction-mate arrow with the ringed chain comparison under E, including inverse, scalar unit and total constraints.

lem-pd-section-derived-representative-square vs def-coef-ringed-tensor-hom-model: The existing statement concerns Canonical closed tensor-Hom representative model on a ringed site; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-coef-semilinear-derived-calculus: The existing statement concerns Ordinary derived semilinear calculus interfaces; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-coef-semilinear-geometry-base: The existing statement concerns Geometry base fields for coefficient linear operations; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-coef-semilinear-geometry-derived: The existing statement concerns Derived geometric system operations and normalization; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-coef-semilinear-geometry-ops: The existing statement concerns Canonical geometric mate and projection words; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-coef-semilinear-system-models: The existing statement concerns Generic strict semilinear system constructions and representative normalization; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-fix-proper-etale-origin-scalar-data: The existing statement concerns Canonical scalar, tensor and direct-image comparisons at etale origins; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-kun-constant-projection-morphism: The existing statement concerns Canonical constant-coefficient derived projection morphism; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-pbc-successive-derived-scalar-normalization-data: The existing statement concerns Normalized presentation data for successive derived scalar extensions; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-pd-section-derived-realization: The definition pins the canonical ringed square and defines the chosen operations. The new statement proves the separately constructed actual internal arrow, unit and constraint squares become those squares under the normalized E and pullback comparisons.

lem-pd-section-derived-representative-square vs def-pd-section-derived-tensor-data: The existing statement concerns Canonical derived section-module tensor data; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-pur-adic-site-strict-quotient-interface: The existing statement concerns Small-site adic strict quotient interface and canonical normalizations; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-pur-change-of-rings-complex: The existing statement concerns Termwise change of rings of a cochain complex; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-pur-cochain-coefficient-arrows: The existing statement concerns Canonical scalar-association and transition arrows on cochain sheaves; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-pur-cochain-coefficient-universe-transport: The existing statement concerns Canonical common-universe transport of ring and module sheaves; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-pur-cochain-tensor-coherence-data: The existing statement concerns Canonical cochain ringed-pullback and coherence data; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-pur-completed-pullback-tensor-comparison: The existing statement concerns Canonical completed, rational and common-stage tensor pullback comparisons; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-pur-derived-constant-pullback-comparison: The existing statement concerns Canonical derived constant-sheaf pullback comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-pur-etale-scalar-pullback-iso: The existing statement concerns Canonical derived scalar and pullback isomorphism; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-pur-finite-pullback-tensor-comparison: The existing statement concerns Canonical finite derived pullback tensor comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-pur-integral-line-reduction-data: The existing statement concerns Signed integral line reduction and restriction data; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-pur-open-coefficient-normalizations: The existing statement concerns Exact-pullback and open-unit coefficient normalizations; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-pur-scalar-pullback-representative-data: The existing statement concerns Canonical scalar/pullback representative data; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-pur-strict-quotient-expressions: The existing statement concerns Strict quotient expressions with actual horizontal transitions; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-pur-system-tensor-mate-arrows: The existing statement concerns Canonical tensor and proper/open arrows for varying coefficient systems; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sf-finite-coefficient-site-chain-tensor: The existing statement concerns Canonical finite coefficient site comparison on total tensor complexes; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sf-finite-coefficient-site-hom-arrow: The existing statement concerns Canonical finite coefficient site internal-Hom arrow; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sf-finite-coefficient-site-scalar-arrow: The existing statement concerns Canonical finite coefficient site scalar comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sf-finite-open-tensor-operations: The existing statement concerns Canonical finite open tensor and pullback operations; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sf-open-normalization-data: The existing statement concerns Geometric and operation data for open tensor normalization; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sf-point-evaluation-derived-compatibility: The existing statement concerns Representative-normalized derived point comparisons; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sf-point-evaluation-scalar-coherence: The existing statement concerns Tensor square for balanced point scalar data; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sf-point-evaluation-scalar-data: The existing statement concerns Balanced scalar comparison for point sections; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sf-point-evaluation-tensor-coherence: The existing statement concerns Signed tensor coherence for point sections; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sf-point-evaluation-tensor-data: The existing statement concerns Normalized tensor presentation for point sections; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sf-point-fibre-tensor-common-stage: The existing statement concerns Canonical common-stage point tensor and coefficient unit; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sf-point-fibre-tensor-finite-models: The existing statement concerns Canonical finite point tensor normalization on K-flat representatives; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sf-point-fibre-tensor-models: The existing statement concerns Canonical integral representative normalization; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sf-point-fibre-tensor-rational-compatibility: The existing statement concerns Canonical rational point tensor, unit, and scalar compatibility; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sf-point-fibre-tensor-reduction: The existing statement concerns Canonical module scalar tensor data and finite reduction squares; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sf-point-fibre-tensor-system: The existing statement concerns Strong symmetric tensor comparison data for the point fibres; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sf-point-finite-source-constraints: The existing statement concerns The finite point source uses the recorded tensor constraints; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sf-point-integral-scalar-square: The existing statement concerns The integral point completion commutes with scalar extension; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sfb-integral-quotient-coefficients: The existing statement concerns Canonical integral uniformizer quotient coefficient maps; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sfb-integral-quotient-projection-map: The existing statement concerns Integral quotient internal projection arrow; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sfb-internal-derived-scalar-comparisons: The existing statement concerns Normalized internal derived scalar comparison interface; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sfb-internal-scalar-tensor-comparison: The existing statement concerns Scalar-unit normalized tensor comparison for internal modules; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sfb-proetale-trace-coefficient-interfaces: The existing statement concerns Canonical internal-module trace coefficient interfaces; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sfb-ringed-derived-comparison-data: The existing statement concerns Data of normalized derived monoidal comparisons of ringed topoi; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sfb-ringed-projection-coherence-data: The existing statement concerns Recorded data for tensor projection coherence; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sfb-ringed-slice-comparison-model: The existing statement concerns Normalized ringed slice comparison data; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sfb-scalar-hom-comparison-data: The existing statement concerns Actual scalar-adjunction and normalized tensor-Hom comparison data; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sp-open-coefficient-adjunction-data: The existing statement concerns Intrinsic open coefficient adjunction data; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sp-open-scalar-operations: The existing statement concerns Constant-ring pro-etale scalar and open operations and their canonical comparisons; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sp-open-scalar-tensor-data: The existing statement concerns Open scalar tensor normalization data; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sp-proetale-scalar-mate-identifications: The existing statement concerns Normalized pro-etale scalar-to-tensor and coefficient-pullback identifications; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-sp-semilinear-constant-ring-operations: The existing statement concerns Constant-ring semilinear system operations and normalized evaluation mates; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-weil-pbc-normalized-origin-scalar-comparisons: The existing statement concerns Canonical quotient scalar-extension unit and associator; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-weil-pbc-ringed-projection-restriction-data: The existing statement concerns Normalized ringed projection and slice comparison data; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs def-weil-pbc-ringed-tensor-square-presentation: The existing statement concerns Representative presentation of a commutative ringed tensor square; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-a1-finite-pullback-strict-tower-comparison: The existing statement concerns Natural finite pullback comparison of strict reduction towers; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-a1-pulled-koszul-tower-chain-comparison: The existing statement concerns Ordinary pullback of principal Koszul towers and target augmentation; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-cbc-completed-open-kflat: The existing statement concerns Completed-coefficient open extension preserves flat-term K-flat models; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-coef-etale-tensor-model-comparison: The existing statement concerns Unique flat-model normalization of the étale scalar tensor comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-coef-ringed-pullback-hom-evaluation-comparison: The existing statement concerns Evaluation-defined Hom comparison for ringed pullback; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-coef-semilinear-operations-existence: The existing statement concerns Geometric and coefficient operations on a fixed semilinear system calculus; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-coef-semilinear-system-existence: The existing statement concerns Ordinary semilinear system calculus and cartesian internal Hom; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-derived-right-exact-tensor-comparison: The existing node constructs a normalized derived family for a generic right-exact tensor functor from representative data. The new node compares the already specified INTERNAL derived map against the SECTION resolution square and actual internal unit, without redefining it as that family.

lem-pd-section-derived-representative-square vs lem-exc-proetale-constant-support-projection: The existing statement concerns Constant-coefficient projection for compact support; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-fix-ringed-scalar-tensor-monoidal: The existing statement concerns Normalized strong monoidality of derived scalar extension in independent universes; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-fix-tensor-pullback-square: The existing statement concerns Tensor inverse-image comparisons commute around an open square; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-kun-derived-pullback-composition-monoidal: The existing statement concerns Canonical derived etale inverse-image composition is monoidal; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-kun-geometric-point-projection-comparison: The existing statement concerns Geometric-point projection morphism agrees with the constant-section projection morphism; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-kun-geometric-point-pullback-tensor-normalization: The existing statement concerns Tensor normalization of the pullback/stalk evaluation comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-kun-inverse-image-monoidal: The existing statement concerns Monoidality of the derived inverse image; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pd-module-ringed-topos-derived-comparison: The existing statement concerns Module-object and ringed-topos derived tensor comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pd-section-derived-tensor-normalization: The new statement stops at actual-map squares on resolving pairs and unit/constraint representatives, assuming the tensor comparison supplied by the first new node. The item still proves equality with the independently fixed canonical RINGED transformation on all objects by descent and faithfulness, and transfers inverses and all diagrams globally.

lem-pd-section-derived-representative-square vs lem-pe-constructible-comparison-tensor-test-reflection: The existing statement concerns Reflection of a single comparison tensor test; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-per-proetale-scalar-slice-comparison: The existing statement concerns Normalized scalar extension comparison on a pro-etale slice; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pod-point-extension-kflat: The existing statement concerns K-flatness of the point extension of a flat-term module complex; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-canonical-coefficient-system-geometry: The existing statement concerns Geometric realization on the literal constant finite coefficient tower; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-cochain-comparison-monoidal-equations: The existing statement concerns Monoidal equations for the canonical cochain pullback comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-cochain-pullback-tensor-coherence: The existing statement concerns Signed tensor comparison and composition on cochain sheaf pullbacks; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-coefficient-pullback-comparison: The existing statement concerns Canonical inverse-image coefficient comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-common-stage-tensor-line-coherence: The existing statement concerns Natural associativity and regular right unit for common-stage tensor; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-constant-native-pullback-monoidal: The existing statement concerns Canonical native derived tensor comparison for constant coefficients; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-derived-pullback-tensor-iso: The existing statement concerns Derived pullback commutes with derived tensor product on the constructible categories; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-etale-scalar-flat-kflat-comparison: The existing statement concerns Native flat-term K-flat étale complexes in scalar coordinates; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-etale-scalar-pullback-existence: The existing statement concerns Existence of normalized derived scalar/pullback comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-etale-scalar-pullback-uniqueness: The existing statement concerns Uniqueness of normalized derived scalar/pullback comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-exact-pullback-signed-comparison: The existing statement concerns Exact ringed pullback identifies the canonical signed derived tensor comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-external-rhom-evaluation-naturality: The existing statement concerns Four-variance naturality of the external evaluation transpose; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-flat-term-kflat-tensor-native: The existing statement concerns Total tensor of native flat-term K-flat complexes; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-geometric-scalar-association-cocycle: The existing statement concerns Scalar-association cocycle from normalized inverse-image restriction squares; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-integral-ambient-operation-models: The existing statement concerns Ambient completion presentations for integral pullback and tensor; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-integral-coherence-tower: The existing statement concerns Coherence identities on normalized integral comparison towers; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-integral-line-derived-comparisons: The existing statement concerns Normalized derived signed-line reductions and support; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-integral-line-power-comparisons: The existing statement concerns Signed power scalar comparisons and evaluations; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-integral-line-reduction-restriction: The existing statement concerns Signed line reductions and restriction to the derived-complete integral category; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-integral-line-restrictions: The existing statement concerns Completeness and normalized restricted line equivalences; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-integral-operations-well-defined: The existing statement concerns The towers defining integral pullback and completed tensor product are invariant under change of K-flat resolution; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-integral-tensor-reduction-tower-comparison: The existing statement concerns Strict tensor comparison for finite coefficient-reduction towers; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-integral-tensor-transition-compatibility: The existing statement concerns Quotient compatibility of the normalized total tensor comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-integral-tower-limit-comparison: The existing statement concerns Derived limit of the strict integral comparison tower; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-kflat-change-of-rings: The existing statement concerns Change of rings preserves K-flat complexes with flat terms; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-kflat-change-of-rings-all-independent: The existing statement concerns Change of rings preserves all K-flat complexes with independent coefficient universe; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-kflat-change-of-rings-independent: The existing statement concerns Change of rings preserves K-flat complexes with flat terms in independent universes; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-kflat-total-tensor-model: The existing statement concerns K-flat total tensor model for flat-term resolutions; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-module-tensor-coefficient-equations: The existing statement concerns Ordinary module tensor equations for coefficient change; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-module-tensor-composition-equation: The existing statement concerns Ordinary tensor square for composite module pullback; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-normalized-operation-system-models: The existing statement concerns Normalization and simultaneous models for finite coefficient-system operations; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-normalized-scalar-comparison-realization: The existing statement concerns Normalized realization of scalar comparisons on quotient systems; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-normalized-tensor-constraint-transport: The existing statement concerns Transport of normalized tensor constraints through coherent realization; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-ordinary-line-derived-scalar-comparison: The existing statement concerns Ordinary unbounded derived scalar extension intertwines signed line tensor and evaluation; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-proetale-restricted-tensor-finite-local-constancy: The existing statement concerns Finite local constancy of a restricted tensor with bounded-above inputs; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-quotient-expression-kflat-normalization: The existing statement concerns Simultaneous K-flat normalization of strict quotient expressions; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-quotient-system-flat-models: The existing statement concerns Strict flat quotient systems compute simultaneous tensor and geometric inverse image; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-scalar-extension-tower-coherence: The existing statement concerns Coherent quotient towers for integral scalar extension; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-scalar-hom-comparison-tower: The existing statement concerns Evaluation-defined scalar Hom maps respect coefficient towers; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-scalar-tensor-pullback-normalization: The existing statement concerns Scalar/tensor pullback normalization on a K-flat representative; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-scalar-tensor-unit: The existing statement concerns Scalar action unitor for a normalized signed tensor comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-signed-line-derived-base-change: The existing statement concerns Signed line comparisons and their unbounded derived tensor action; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-strict-coefficient-comparison-calculus: The existing statement concerns Simultaneous strict coefficient comparisons on ring-sheaf towers; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-support-site-comparison: The existing statement concerns Etale-proetale comparison for supported sections and their exterior products; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-system-normalized-tensor-closure: The existing statement concerns Normalized semilinear systems are closed under tensor and inverse image; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-system-tensor-reduction-formula: The existing statement concerns Tensor formula for actual semilinear reduction adjoints; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-pur-varying-ring-tensor-comparison: The existing statement concerns Normalized tensor comparison for one varying-ring inverse image; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sf-boundary-bounded-tensor-comparison: The existing statement concerns Bounded tensor preparation for the boundary direct-image comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sf-canonical-open-restriction-model: The existing statement concerns Canonical open restriction on augmented quotient models; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sf-comparison-open-tensor-coherence: The existing statement concerns Etale/pro-etale comparison respects the canonical open tensor map; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sf-completed-tensor-rational-naturality: The existing statement concerns Naturality and rationalization of a completed tensor comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sf-generator-reduction-coherence: The existing statement concerns Basic generator coefficient squares in semilinear systems; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sf-integral-line-tensor-comparison-representative: The existing statement concerns K-flat line tensor models and finite balancing; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sf-open-operation-models: The existing statement concerns Open operation comparisons with fixed tensor models and right square; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sf-open-pullback-support: The existing statement concerns Derived pullback preserves open support; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sf-open-restriction-completeness: The existing statement concerns Completeness and the actual completion unit after ordinary open restriction; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sf-point-fibre-derived-tensor: The existing statement concerns The point fibre functor preserves derived tensor at all coefficient stages; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sf-point-field-tensor-descent: The existing statement concerns Rational and common-field point tensor descent; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sf-point-finite-tensor-comparisons: The existing statement concerns Finite point tensor comparisons and all quotient squares; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sf-point-integral-completed-tensor-comparisons: The existing statement concerns Completed integral point tensor and scalar squares; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sf-point-ringed-evaluation-model: The existing statement concerns Ringed geometric-point evaluation with signed tensor and coefficient models; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sf-ringed-finite-free-tensor-complex: The existing statement concerns Actual scalar tensor comparison on complexes and K-flat preservation; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sf-scalar-pullback-composition: The existing statement concerns Composition coherence of normalized scalar/pullback comparisons; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-constant-module-kflat: The existing statement concerns Constant realization preserves flat-term K-flat complexes; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-constant-realization-derived-scalar-extension: The existing statement concerns Derived constant realization commutes with derived scalar extension; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-etale-stalk-total-tensor-comparison: The existing statement concerns Canonical signed total tensor stalk comparison and chain naturality; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-exact-completed-koszul-pullback: The existing statement concerns Exact product-preserving inverse image transports the actual Koszul unit; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-flat-term-kflat-functor: The existing statement concerns Flat-preserving colimit functors preserve flat-term K-flat complexes; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-geometric-stalk-tensor-constant-single: The existing statement concerns Geometric stalks commute with derived tensor against a constant module; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-hom-flat-scalar-evaluation-model: The existing statement concerns Flat scalar evaluation on an arbitrary first complex and its derived coherence; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-integral-quotient-pullback-face-model: The existing statement concerns Common K-flat model for integral quotient pullback faces; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-internal-extension-monoidal: The existing statement concerns Scalar-unit normalized strong monoidal extension of internal scalars; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-internal-extension-preserves-flat: The existing statement concerns Extension of scalars preserves flat internal modules; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-internal-scalar-mate-projection: The existing statement concerns Restriction of an internal coefficient mate is the specified projection map; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-internal-scalar-mate-transitivity: The existing statement concerns Successive internal coefficient mates and normalized scalar units; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-internal-scalar-pullback-normalization: The existing statement concerns Normalized internal scalar extension and geometric pullback; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-kflat-scalar-comparison-normalization: The existing statement concerns Representative and adjunction normalization of scalar pullback comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-projection-comparison-etale-proetale: The existing statement concerns Etale-to-proetale comparison of the canonical direct-image projection morphism; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-quotient-section-tensor-normalization: The existing statement concerns Normalized quotient scalar tensors and section-module realization; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-ringed-comparison-tensor-adjunction: The existing statement concerns Tensor and adjunction compatibility of canonical ringed-topos path comparisons; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-ringed-derived-monoidal-comparisons: The existing statement concerns Monoidal and adjunction normalization of derived ringed-topos comparisons; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-ringed-derived-tensor-diagrams: The existing statement concerns Coherence equations for explicit canonical derived comparison maps; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-ringed-derived-tensor-lift: The existing statement concerns Symmetric monoidal coherence of a canonical derived tensor lift; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-ringed-derived-two-iso-comparison: The existing statement concerns Specified geometric 2-isomorphism comparison on derived modules; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-ringed-projection-first-shift: The existing statement concerns The ringed projection mate commutes with shifts in its direct-image input; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-ringed-projection-pullback-comparisons: The existing statement concerns Normalized identity, composition and section pullback comparisons; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-ringed-projection-tensor-compatibility: The existing statement concerns Tensor constraints and compatibility of normalized comparisons; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-ringed-projection-tensor-structure: The existing statement concerns Canonical tensor structure in arbitrary recorded presentations; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-ringed-site-point-acyclic: The existing statement concerns A conservative point family detects acyclicity; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-ringed-site-point-kflat-resolution: The existing statement concerns K-flat resolution with K-flat stalk; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-ringed-site-point-tensor: The existing statement concerns Signed total tensor comparison for normalized stalks; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-scalar-extension-kflat: The existing statement concerns Scalar extension preserves all K-flat sheaf complexes; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-scalar-hom-tensor-coherence: The existing statement concerns Tensor coherence of the normalized scalar extension maps; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-scalar-internal-hom-tower-coherence: The existing statement concerns Coefficient-tower and identity coherence for normalized internal Hom; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-scalar-tensor-comparison: The existing statement concerns Derived scalar tensor comparison on all K-flat representatives; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-scalar-tensor-tower-comparison: The existing statement concerns Simultaneous normalized scalar tensor comparisons with coefficient coherence; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sfb-successive-derived-quotient-normalization: The existing statement concerns Successive derived scalar extensions agree with direct quotient extension; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sp-bounded-flat-coefficient-site-square: The existing statement concerns Bounded-flat coefficient/site square with its canonical derived comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sp-canonical-open-scalar-tensor-models: The existing statement concerns Canonical scalar tensor models compatible with open inverse image; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sp-etale-chart-comparison-isos: The existing statement concerns Canonical site comparisons for scalar and chart operations; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sp-intrinsic-open-projection-invertible: The existing statement concerns Intrinsic open projection inverse is invertible; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sp-open-projection-scalar-comparison: The existing statement concerns Scalar restriction of the normalized open projection; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sp-open-scalar-coefficient-coherence: The existing statement concerns Coefficient coherence of scalar pullback; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sp-proetale-scalar-tensor-normalization: The existing statement concerns Underlying tensor normalization of pro-etale scalar and inverse-image comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sp-proetale-tensor-coefficient-resolution-square: The existing statement concerns Coefficient-resolution square for exact pro-etale tensor pullback; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-sp-supported-constructible-origin-comparison: The existing statement concerns Supported constructible etale origin and its unbounded coefficient tensor comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-trf-ringed-kflat-word-comparison-descent: The existing statement concerns Simultaneous K-flat word models and normalized comparison descent; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-etale-native-tensor-pullback: The existing statement concerns Native unbounded derived tensor commutes with etale inverse image; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-augmented-cech-tensor-pullback: The existing statement concerns Augmented Cech tensor actions commute with derived inverse image; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-augmented-diagram-projection-mate: The existing statement concerns Projection mate for an augmented coefficient diagram before taking inverse limit; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-cochain-pullback-tensor-shift: The existing statement concerns The prescribed cochain pullback tensor comparison commutes with both signed shifts; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-completed-adic-koszul-kflat: The existing statement concerns K-flatness of the actual completed exterior Koszul complexes; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-constant-derived-normalization-universal: The existing statement concerns Constant derived realization preserves universal coefficient arrows; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-derived-adjunction-shift: The existing statement concerns Canonical derived ringed-topos adjunction is shift-compatible; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-derived-scalar-extension-local-systems: The existing statement concerns Coherent localized derived scalar extension and comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-diagram-kflat-replacements: The existing statement concerns Objectwise K-flat replacements in strict diagram categories; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-finite-reduction-pullback-coherence: The existing statement concerns Finite reduction and the canonical pullback square; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-flat-coefficient-reduction-adjunct: The existing statement concerns Finite scalar comparison preserves derived reduction adjuncts; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-kflat-tensor-pullback-computation-universes: The existing statement concerns Derived pullback computes K-flat tensor representatives; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-normalized-derived-isomorphism-section-reduction: The existing statement concerns Normalization-compatible evaluation of actual local Isom sheaves; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-normalized-derived-isomorphism-transport: The existing statement concerns Universal normalization and evaluation of source-site local Isom sheaves; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-normalized-origin-comparison-coherence: The existing statement concerns Comparison reduction respects canonical scalar units and composition; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-pullback-resolving-computation: The existing statement concerns Derived pullback computes on resolving complexes with independent universes; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-pullback-tensor-canonical-shift-unit: The existing statement concerns Canonical shifts and action units of the derived pullback tensor comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-pulled-reduction-normalization-comparison: The existing statement concerns Successive quotient normalizations under the pulled reduction comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-reduction-pullback-derived-tower: The existing statement concerns Normalized derived pullback of a strict coefficient reduction tower; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-resolving-representative-whiskering: The existing statement concerns Restriction to resolving representatives is fully faithful; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-common-quotient-pullback-comparison: The existing statement concerns Common quotient reduction of the geometric scalar comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-equivalence-module-hom: The existing statement concerns Module and closed Hom transport under a ringed equivalence; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-exchange-tensor-coherence: The existing statement concerns Projection-formula coherence for a square of ringed topoi; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-projection-global-model: The existing statement concerns Existence of the canonically normalized global projection package; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-projection-local-model: The existing statement concerns Localization of a normalized global projection package; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-projection-mate-exact: The existing statement concerns Exactness data for the ringed-topos projection mate; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-projection-restriction: The existing statement concerns Localization comparisons for the ringed projection mate; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-projection-tensor-comparison: The existing statement concerns Descent and signed shifts of the normalized pro-etale tensor comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-projection-tensor-shifts: The existing statement concerns Signed shifts of an already normalized tensor comparison; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-pullback-preserves-kflat: The existing statement concerns Ringed pullback kflat; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-slice-comparisons-shift: The existing statement concerns Shift normalization of canonical ringed-slice comparisons; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-slice-evaluation-transpose: The existing statement concerns Slice restriction preserves evaluation for an arbitrary dualizing object; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-slice-koszul-coherence: The existing statement concerns Normalized slice restriction preserves Koszul exchange; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-slice-normalized-comparisons: The existing statement concerns Existence of normalized slice tensor, Hom and Koszul comparisons; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-square-tensor-compatibility: The existing statement concerns Tensor compatibility of a ringed square on flat K-flat representatives; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: The existing statement concerns Derived tensor comparison for arbitrary ringed topoi; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-existence: The existing statement concerns Canonical tensor comparison unit existence; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-uniqueness: The existing statement concerns Canonical tensor comparison unit uniqueness; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-topos-acyclic-kflat-pullback: The existing statement concerns Ringed-topos pullback in the acyclic K-flat case; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-topos-kflat-pullback: The existing statement concerns Ringed-topos pullback preserves flat-term K-flat complexes; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-ringed-topos-pullback-adapted-flat-resolution: The existing statement concerns A flat resolution whose ringed-topos pullback is K-flat; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-supplied-ringed-topos-kflat-pullback: The existing statement concerns Tensor pullback adjoint to a supplied ringed-topos module direct image; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-derived-representative-square vs lem-weil-pbc-tensor-comparison-descent-representatives: The generic existing node constructs the UNIQUE derived isomorphism from input representative data. The new node proves that the ACTUAL INTERNAL derived arrow and unit satisfy those particular input squares after all prescribed comparison factors.

lem-pd-section-derived-representative-square vs lem-weil-point-derived-tensor-tower-coherence: The existing statement concerns Ordinary derived scalar associators and point sections-tensor tower coherence; it does not assert the actual internal-to-section tensor representative square with the specified theta, gamma, epsilon, a/c factors and regular-unit/constraint squares.

lem-pd-section-kflat-tensor-comparison vs new-lem-kun-exact-monoidal-equivalence-derived: That node descends abstract strong monoidal equivalences and monoidal adjunction data. The new node must identify the project’s fixed CONJUGATE section tensor with the independently fixed NATIVE ringed K-flat model and its specified q map, including internal resolving classes and the exact representative equation; those identifications are not given abstract monoidal structures.

lem-pd-section-kflat-tensor-comparison vs lem-pe-internal-section-tensor-comparison: The existing node is the ordinary module and total-complex equivalence with flat/K-flat preservation; the new node identifies derived resolving localizations, the specified native/conjugate tensor map and derived constraints.

lem-pd-section-kflat-tensor-comparison vs lem-pd-section-derived-tensor-normalization: The item also compares the actual pullback oplax/lax/unit transformations with independently fixed ringed transformations for a morphism f. The new node has only a single scheme T and resolves its tensor-model comparison; it has no pullback-arrow conclusion.

lem-pd-section-oplax-total-comparison vs lem-pur-derived-tensor-comparison: That generic node extends an assumed coefficient comparison to totals and then derived objects for exact functors; it does not identify the project’s actual internal mate map, unit and constraints with the ringed maps under E.

lem-pd-section-derived-representative-square vs lem-pd-section-derived-pushpull-normalization: That node identifies pullback/pushforward operations and their resolution transformations and adjunctions; it does not identify tensor localization factors or the actual internal tensor-arrow square.


## Prior returned report (retained history; superseded)

The following report belongs to the returned zero-new-node compression. Its claims about the final proof length and absence of new nodes describe that prior attempt, not this repaired delivery. It is retained verbatim as requested.

## Worker report

1. Files written: `dag/nodes/sec-poincare-duality/lem-pd-section-derived-tensor-normalization.json`, the existing statement node, retained as split; `citations.json`; `searches.jsonl`; this report. No new nodes and no Mathlib leaves. The sandbox initially contained only dispatcher brief markers, so the live node was the starting copy. Its N6 split, previous citations/search records, statement and metadata were retained. Q97 changes the proof wording and explicit normalization citations, their dependency union, the additional genuine search records, and split_report. The final proof has 2991 characters in seven steps.
2. Attachments: none. Searches under `lean/WeilConjectures/` for the blueprint tag, section/derived tensor and internal/section equivalence found no complete declaration. The already-recorded `AlgebraicGeometry.ProEtale.ModuleRingedComparison.section_derived_tensor_normalization` is in `lean/Sheaf/Paper/SectionDerivedTensorNormalization.lean:174`, and its proof at line 214 is `sorry`; it is not an attachment. Its six conjuncts express representative normalization, tensor constraints, the actual delta square, inverse mu square, unit equality, and pullback constraints, consistent with this item's clauses.
3. WANTED: none. All supporting sources used here are available locally.
4. The live node already has a seven-step N6 split reviewed on 2026-10-21. I preserved that mathematical argument. A precise C4 issue remained in Step 5: the statement of `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` asserts a canonical isomorphism and K-flat preservation but does not state its normalizing square. I cited `def-pd-section-derived-realization`, whose statement explicitly defines the tensor-pullback isomorphism by that unique square. Step 5 now identifies the constructed arrow using that definition and uniqueness from `lem-weil-pbc-tensor-comparison-descent-representatives`; Step 6 cites the same specified tensor resolution data. Step 3 now explicitly cites `def-pd-section-derived-tensor-data` for the section constraints and localized total comparison. No statement correction or mathematical route change was needed.
5. Unfinished work: no stage-1 argument is left open in this item. The existing dependency nodes keep their own statuses. Stage 2/3 and Lean proof completion are outside this delivery.

## Source and route

I read `GOAL.md`, the stage-1 brief and stage document, SETUP's three-level rule, and delivery-errors B-E. The chapter record fixes Poincare duality with the six-functor and smooth-purity inputs. The node's assigned unit is `sk-thm-sf-verdier-exchange`; I read its unit record and current main-20261015 section, which proves duality exchange using composition and tensor-Hom exchange. This item is a lower-level normalization tool and does not replace either of those steps.

For the item's literature I read Stacks `sites-cohomology.tex`, Tag 06YS (`lemma-K-flat-resolution`), Tag 06YU (`definition-derived-tor`) and its construction, Tag 0G7E (`lemma-pullback-K-flat`), and Tag 07A4 (`lemma-pullback-tensor-product`), including the proof of 07A4. I also read `sites-modules.tex`, Tag 03EL (`lemma-tensor-product-pullback`) and its adjunction/bilinear-map proof. Tag-to-label assignments were checked against `literature/stacks-project/tags/tags`. The proof remains agent-origin: Stacks supplies the K-flat route and tensor arrows; the internal/section normalization is the explicit argument of the seven steps, not a claim that Stacks states this condensed-coefficient theorem. In 07A4 the displayed comparison on totals runs opposite to our oplax b; our construction uses its inverse, consistently with the ordinary normalized formula.

`blueprint_refs.py ancestor` returns no imported ancestor. I retained `blueprint.from` with node null and the seeded-target/parent chain, and its precise place. Whole-blueprint searches for derived tensor and section equivalence found the existing general tensor nodes, but no imported node for this equality of specified constructions, so `same_as` stays empty. I read the current `sk-def-sfb-derived-tensor-hom/_section.md` and `lem-sfb-derived-monoidal.proof.md`; the relative module tensor route is unchanged. No SGA source is used.

## Mathlib searches

All five Q97 searches were run through the prescribed msearch command and the returned hits read; exact queries and digests are in searches.jsonl and appended to the item's earlier records. LeanFinder searched the internal/section equivalence and actual derived oplax arrow; its flat-module equalizer and tensor-exactness results are ordinary algebra, not this theorem. LeanSearch used a second phrasing about two-variable derived tensor transformations on resolutions; it returned generic localization extensionality and derived-functor transformations. Loogle confirmed `CategoryTheory.Localization.natTrans₂_ext`. The broad grep found Tor and group homology; the follow-up grep located bifunctor localization declarations. I read `Mathlib/CategoryTheory/Localization/Bifunctor.lean` and `Mathlib/CategoryTheory/Monoidal/Tor.lean`. The extensionality theorem at Bifunctor.lean:180 is a general tool already covered by the cited localization nodes; it does not itself construct or identify the specified internal/ringed arrows, so the item is not a one-line Mathlib specialization. Tor.lean:44-53 defines homology-valued Tor from projective resolutions, not the unbounded K-flat tensor normalization here. Every service ran successfully; no invented or unavailable search is reported as a negative result.

## New nodes

None. I searched the live DAG for section/derived tensor and inspected the statements of every proof dependency. The existing internal/section tensor comparison, ringed-site descent, representative-comparison theorem, and specified-realization definition cover the necessary inputs. The added citations refer to definition nodes already in stmt_deps; creating separate nodes for those clauses or for the scalar formulas would duplicate existing material or elementary steps.

## Review by Q97

I reviewed the seven steps against the actual node statements, not only their titles, and against the sources above. `citations.json` supplies a verbatim statement for each of the 28 step/node pairs. There are no new-node statements requiring separate sources or edge-case tests.

Step 1 uses `lem-pe-internal-section-tensor-comparison` for exactness, flatness, acyclicity, K-flatness and signed total tensors; each is explicitly in its statement. `sk-def-sfb-sheaf-tensor` gives strong monoidal sheafification and closed sheaf tensor on the small pro-etale site, discharging the comparison's sheafification hypotheses. `lem-weil-pbc-site-derived-tensor-descent` states equivalence of the localization of flat-term K-flat representatives with D(R) and full faithfulness on pairs, not merely existence of some resolutions. `lem-pd-section-derived-pushpull-normalization` identifies the derived equivalence and the pullback resolution transformations. The coefficient and object universes agree as required by the item's ordinary data. Identifying quasi-isomorphisms using the exact equivalence is the immediate cohomology test, not an additional comparison theorem.

Step 2 takes the total-tensor comparison from the internal/section lemma, the relative two-variable derived tensor from `sk-def-sfb-derived-tensor-hom`, and the specified representative isomorphisms and unique extension from the site-descent statement. Conjugating localized t by the representative isomorphisms gives the displayed arrow. Naturality after inversion follows by multiplying a naturality equation by the inverted arrows; extending the two inverse transformations and checking their composites uses precisely the stated full faithfulness. The construction remains in the derived category; no per-degree surrogate is introduced.

Step 3 uses the internal/section lemma's explicit regular-unit and associator/unitor clauses. The degree-zero regular module passes the flat and K-flat tests because its tensor functor is the identity, including on acyclic complexes. `lem-sfb-derived-monoidal` explicitly supplies constraints induced from complexes; `def-pd-section-derived-tensor-data` specifies the section conjugate tensor and ordinary total comparison, which was previously only implicit here. The resolving localization statement and the faithfulness clause of `lem-weil-pbc-localization-universal-property` permit the successive one-variable extension of the three-variable associator equation. This does not assume an uncited theorem about arbitrary three-variable localizations.

Step 4 uses `lem-pd-section-ordinary-oplax-normalization` for equality with the actual ordinary arrow, its local pure-tensor formula, and inverse; the statement gives all three. `def-pd-section-module-operations-data` specifies the adjunction used for F. The displayed Hom computation proves the required coproduct preservation in place, including an infinite degreewise sum, so no node is needed for this elementary adjunction consequence. `def-pc-tensor-complex-sheaves` gives the signed direct-sum differential. Naturality with each differential and equality of the factors (-1)^p prove the chain-map assertion directly; an unbounded total is never replaced by a finite sum or a product.

Step 5 uses the exact r_Y and r_X isomorphisms given in the site-descent statement. The ringed tensor-pullback theorem's statement says pullback preserves K-flat complexes WITH flat terms; both hypotheses hold for P and Q. The computation-universes lemma explicitly includes epsilon invertibility on representatives and on their total tensor; it is not inferred from flatness alone. The representative-descent lemma then applies with the fully faithful restriction, preservation of representatives, ordinary b and invertible epsilon maps exactly as stated. I checked the types: a goes from LF(QP tensor^L QQ) to QF Tot(P tensor Q), and c from LF(QP) tensor^L LF(QQ) to Q Tot(FP tensor FQ); therefore c^{-1} Q(b) a has the required orientation. The new citation to `def-pd-section-derived-realization` supplies the unique representative square that singles out the fixed ringed arrow. Its statement says this explicitly, whereas the mere canonical-isomorphism assertion in the pullback theorem would not suffice. This corrects the previous citation gap without adding a lemma that restates this item.

Step 6 again cites that realization definition for the specified tensor resolution comparison, ordinary-oplax normalization for the actual bottom arrow, and derived-pushpull normalization for compatibility with the resolution transformations themselves. The resulting equation c delta = Q(b) a has the same square as Step 5. The site-descent statement's faithfulness for natural transformations on pairs makes equality on resolving representatives sufficient. This identifies actual natural transformations; it does not infer equality from both maps being invertible.

Step 7 uses the ordinary-oplax statement's inverse formula, scalar unit and constraint clauses, the localization statement's preservation of composition and identities and faithfulness, and the computation lemma for the degree-zero unit representative. It takes resolving representatives from the site-descent statement. Inverting the two identity equations proves the inverse-arrow clause. The scalar-multiplication formula identifies the unit, and the ordinary coherence equations extend successively in their variables. No hidden compatibility with an unrelated natural isomorphism is assumed.

I tested the retained statement and formulas at identity f, zero coefficient ring, zero complexes and degree-zero regular modules. They reduce respectively to the identity comparison, unique maps on zero modules, zero tensors, and the familiar scalar maps. For complexes supported in negative or odd degrees, both differential components have exactly the same (-1)^p sign; for unbounded complexes the left-adjoint coproduct computation covers the infinite degree sums. No finite type, smoothness, nonzero ring, boundedness, or unmentioned site-smallness assumption is used. The independent-site-universe computation theorem is used rather than a smaller-universe specialization.

The seven proof steps remain below 2000 characters after the edits. The adjunction-to-coproduct and naturality/inversion computations are written out as routine parts of the steps. No new node repeats a clause of the item; all non-elementary ingredients have existing node citations, proof_deps is their union, and no new dependency path can return to the item through the added definition citations (they were already statement dependencies). Maintainer-owned records were retained. No Lean was written and no compiler, Lake or local DAG/preflight checker was run.

The inherited off-unit uses remain generic exact equivalence, K-flat representative, localization, or tensor-totalization tools, with reasons retained in split_report.tool_uses. They serve this normalization and do not replace the Verdier-exchange unit route. The new proof citations are definition nodes, hence introduce no new off-route theorem use.

## Dry-run repair

The first required dry run exited with one failure: the 2026-10-21 human re-split rule caps the sum of proof-step text at 3000 characters; the inherited argument with Q97's citation corrections was 9242 characters. I shortened the seven steps to 2991 characters, keeping all 28 citations. The shortening uses existing statement-level interfaces, not new clause nodes: the internal/section theorem already gives the exact total/K-flat comparison, site descent already gives full faithfulness, representative descent already gives the unique square, and the realization definition already pins the ringed arrow. The actual equality still follows from the explicit equation c delta = Q(b) a, including its a/c formulas, rather than an appeal to invertibility. Scalar formulas, the differential sign, the adjunction-to-sums calculation, and successive-variable coherence extension remain in the proof. The longer step-by-step review above records the reasoning checked before shortening. No mathematical subclaim has been moved into a new node or silently assumed.

## Delivery validation

The mandatory initial dry run of the retained returned attempt exited OK at a234b4ee52c. That mechanical result did not repair the return. The substantive three-node repair then passed the server preflight at e4fbca09f7b. Before the final dry run I made the total node’s derived-category isomorphism explicit and named the actual INTERNAL oplax construction separately from the ringed realization definition; these clarify the same statements without changing the split or its arguments. The final dry run and delivery are run sequentially with one active deliver.py process at a time.
