## Worker report

Files written:

- `dag/nodes/sec-smooth-purity/prop-sf-pf-reduction.json`: unchanged statement, four-step assembly proof, status split.
- `dag/nodes/sec-smooth-purity/lem-sf-pf-reduction-witnessed-flat-domains.json`: statement, status unsplit, no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-sf-pf-reduction-proper-open-identities.json`: statement, status unsplit, no Mathlib match.
- `dag/units/sk-prop-sf-pf-reduction.json`: only realized and realized_by; the item realizes the statement and the two children with the parent realize its one counit-tensor proof paragraph.
- `report.md`, `citations.json`, and actual search log `searches.jsonl`. Research outputs and the returned-item snapshot remain sandbox-only.

Attachments: none. I searched the project source for the blueprint tag and coefficient/projection notions. `WeilConjectures.projectionFiniteReduction` in `lean/Sheaf/Paper/ProjectionFiniteReduction.lean` ends with sorry. The upstream Etale `projectionMapOfCompactification_constantSingle` and `hasProjectionFormula_iff_reductionModIdeal` have proofs, but their statements retain reduction as an endofunctor of the original A-module category on the etale site, whereas this item specifies an intrinsic B-linear square on the pro-etale site. No silent category identification is used to attach them. The upstream pro-etale finite projection formula covers invertibility only, not the coefficient square. None gives every clause of this item as stated.

WANTED: none. The current blueprint proof and unit, supporting DAG statements, upstream Lean and cited Stacks passages are present.

What was wrong: the returned split had eight proof paragraphs totalling 7862 characters, with substantial domain construction and coefficient coherence still assigned to one worker. The sandbox initially contained only dispatcher marker files, no node, report or searches. I copied the current live returned node, retained all its statement, source, earlier Mathlib searches and maintainer metadata, and saved the exact proof as returned-item.json for comparison. The initial dry run exited on the genuinely missing report; it did not indicate any mathematical failure. No parent statement error was introduced or repaired in this return.

Unfinished work: the two new children intentionally have statement only, no proof steps or proof dependencies, and status unsplit so separate later workers can prove them. No Lean writing, compilation or build was performed.

## Repair of the re-split return

The parent statement is byte-for-byte equal to the live returned statement. Its proof now has 2071 text characters, below 3000. Exactly two new, independently claimable argument nodes have been added. Neither states the final reduction square or the parent's invertibility equivalence.

| Returned step | Work now assigned to |
| --- | --- |
| 1: descent, Tor reflection, flat constructible models, coefficient tensor and pullback/tensor domains | witnessed-flat-domains child |
| 2: the explicitly typed vertical maps u,v and the actual square | parent step 2 |
| 3: Nagata compactification, extension-by-zero domains and their open tensor identification | witnessed-flat-domains child |
| 4: projection factorization, proper comparison as counit mate and factorization of c_f | definitions in the proper-open-identities child; used by parent step 3 |
| 5: proper-factor ringed-topos coefficient square and its exact equality | proper-open-identities child |
| 6: faithful open restriction, normalized units, tensor/pullback coherence and open equality | proper-open-identities child |
| 7: naturality and pasting, with identification of the two resulting composites | parent step 3 |
| 8: cancellation only for the reduced map, then the finite projection theorem for the original maps | parent step 4 |

The allocation sizes are 2177 characters of old argument for the domain child (steps 1,3) and 3082 for the factor-identities child (steps 4,5,6). The second child has a genuine proper counit-mate comparison and an open-unit normalization calculation; the first has a genuine simultaneous flat-model and site/domain construction. These are comparable workloads, not a whole-proposition wrapper paired with an elementary auxiliary. In particular the second child concludes two factor identities and the normalization of c_f; the parent still proves the resulting square by pasting them. This expressly preserves the source's route. The new children are not claimed to be their own completed splits.

## Review by NI

I read the main-20261015 `sec-six-functors-basics/sk-prop-sf-pf-reduction` statement, proof and unit, the older recorded unit in dag/units, all eight returned paragraphs, and the current Lean theorem/docstring. The chapter and unit route remain fixed. The proof uses the unit's compactification/counit-tensor calculation, never axiom (A3) or (A5) of the abstract datum to assume the concrete result.

For the domain child I read the statements of lem-sf-proetale-constructible-origin, lem-sf-comparison-tor-amplitude and lem-sf-flat-model, including the Noetherian constructible variant. These supply precisely etale origins, reflection/preservation of the same Tor interval, and bounded flat constructible representatives, respectively. Finite-type schemes over the standing field are Noetherian; all degrees and coefficient exponents have their positive/finite hypotheses. On P tensor B each term is flat as a B-module by `(P tensor_A B) tensor_B N = P tensor_A N` and exact scalar restriction; this never assumes B is A-flat. On a common finite stratification its values stay finite. Exact constant-coefficient inverse image and the finite total tensor preserve flat terms with the sum interval. I also read thm-nagata-compactification (Y is qcqs), lem-trf-open-ctf (open extension preserves the input interval), and lem-cbc-extension-zero-projection-formula (the exact displayed derived isomorphism). These justify the compactification and proper-factor domains, rather than using the mere definition of ctf as a preservation theorem. The child records all the witnesses and simultaneous models that the parent uses. Its source is the domain preparation implicit in the current blueprint paragraph; the detailed argument is agent-written and is retained verbatim below, with those existing results as its future proof inputs.

For the factor-identities child I read def-exchange-projection in full: its pi is the adjunct of counit tensor identity and its gamma includes pullback composition. I read det-sp-reduction-direct-image, which states the B-linear proper mate and the subsequent canonical open comparison for the same compactification, and lem-fix-compact-support-coefficient-change, which specifies the canonical c_f and its compatibility with counits. I read lem-weil-pbc-ringed-exchange-tensor-coherence: it is for arbitrary commuting ringed-topos squares, with small sites in one universe, not just cartesian squares. Applied to the A/B constant-ring square over r it yields the proper identity with no flatness assumption. I read Stacks sites-cohomology.tex Tag 0E48, remark-compatible-with-diagram, and the surrounding Tag 07A4, lemma-pullback-tensor-product: they give the specified tensor and projection/exchange composites, not a claim of equality from stalks. I read lem-sf-open-tensor-normalization and Stacks Tag 0GL1, lemma-j-shriek-and-tensor, and sites-modules.tex Tag 0E8I with the same label. The Stacks tensor isomorphism alone is not treated as the simultaneous normalization theorem. The separately existing normalization node supplies fully faithful open extension and identity restrictions for d and gamma. The open coefficient calculation from returned step 6, plus the canonical s,t and their pullback-composition coherence, is retained below. Existing lem-fix-open-scalar-tensor-normalization supplies precisely that open subidentity and should be reused when the child is proved; it does not state the proper identity or normalization of c_f. Neither ring map nor open scalar restriction is asserted to be faithful on arbitrary derived morphisms.

For parent step 1 I opened the new domain statement and checked that it actually supplies both coefficient stages, H and j_!H, the compactification and all etale witnesses, with the Tor bounds. For parent step 2 I checked the exact statements of lem-fix-operation-reduction and lem-fix-compact-support-coefficient-change: s,t and c_f are isomorphisms on these finite-Tor domains. The upper horizontal arrow is rho(PF_A), not PF_A, and the vertical targets really have B-actions. The source/target formulas of u and v are displayed in the parent.

For parent step 3 I checked every map against the full projection clause of def-exchange-projection and the concrete-projection clause of def-sf-pf. The new factor statement explicitly gives each equation the pasting uses, as well as naturality of c and factorization of c_f. Its proper identity first uses pi_B at rho(j_!K); moving d_K through pi_B is ordinary naturality, after which gamma_B has its correct domain j_!K_B. The parent explicitly writes that move, the naturality move of c, and both substitutions. No equality on stalks, determination by the unit, or hypothetical invertibility of pi is used.

For parent step 4 I read all hypotheses of thm-sf-pf-finite and lem-weil-finite-compact-projection-formula: the first is etale, the latter also identifies the concrete pro-etale compactification map for witnessed etale origins. The finite-Tor second input and bounded constructible first input are furnished at each of A,B by step 1. This proves both original maps invertible. Cancellation of u,v alone is used only for rho(PF_A), never as a conservativity assertion for reduction.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 of delivery-errors against the files. Both new statements introduce their objects, coefficients, sites and specified maps, use derived-category isomorphisms, contain no proof sketches, and are unsplit. New proof arguments are in this report, as required for statement-only children. I retained the complete old argument below rather than summarizing away its steps. Searches were run by msearch.py, their complete outputs were read, and exact queries and outcomes are recorded. No search was invented. The closest module-flatness and ordinary sheaf adjunction hits are not full matches and require genuine additional sheaf/derived/site constructions. Blueprint searches and the whole-DAG same-tag scan were read; the differences are recorded below. No source from the forbidden SGA route is used.

Edge cases checked: m=n makes rho and all coefficient comparisons identities, so the factor equations reduce to naturality/identity equations; m=1,n>1 need not be flat and neither statement assumes it. K=0 or L=0 gives zero objects/maps. If f or either compactification factor is an identity, the corresponding unit/counit maps and tensor identifications reduce to identities and the other factor equation remains. For an empty source, zero flat models and the empty compactification input work; degenerate Tor intervals and shifted complexes use the stated additive interval endpoints. Degree-zero finite free constant sheaves on a point reduce the domain claim to ordinary module base change and tensor associativity. These checks found no new statement dispute.

The largest parent step has 734 characters, so none exceeds the 2000-character long-step review threshold. I additionally checked its pasting computation directly as above. The new statements are independent tasks; no child proof relies on the parent conclusion. The existing item metadata, old searches and existing tool_uses are preserved by the delivery overlay. The sole off-unit parent theorem comparison is declared in split_report.tool_uses. The server checker is run only through the authorized remote tool. This is my own review under the direct-delivery brief; no second reader or sub-agent was started.

## Not duplicates

lem-sf-pf-reduction-witnessed-flat-domains vs lem-sf-flat-model: the existing statement gives a flat model for one complex, not the simultaneous coefficient-reduced models, tensor inputs and compactification-origin witnesses.

lem-sf-pf-reduction-witnessed-flat-domains vs sk-lem-sf-flat-model: the existing statement gives flat models and thick generation, not the same-degree-bound A/B and proper-input realization package.

lem-sf-pf-reduction-witnessed-flat-domains vs det-sf-flat-model-generation: the existing statement gives stratification and thick generation; it does not state coefficient-change models or the proper-factor input witnesses.

lem-sf-pf-reduction-witnessed-flat-domains vs lem-sfb-finite-flat-constructible-total-tensor: the existing statement starts with two etale flat models over one ring; it does not descend intrinsic pro-etale inputs, construct the simultaneous B-models, or prepare compactification inputs.

lem-sf-pf-reduction-witnessed-flat-domains vs det-prop-scalar-six-ctf: the existing statement gives ctf preservation for condensed coefficient passage and generation; it does not produce these same-bound etale flat models or the compactification witnesses.

lem-sf-pf-reduction-witnessed-flat-domains vs lem-sfb-constructible-local-tor-etale-origin: the existing statement gives a site-origin equivalence for a single complex, not simultaneous flat A/B models and compactification tensor domains.

lem-sf-pf-reduction-witnessed-flat-domains vs lem-per-noetherian-ctf-flat-model: the existing statement works with a Noetherian F_l-algebra and a single etale input, without the general mixed-characteristic finite-quotient pair or compactification tensor-domain package.

lem-sf-pf-reduction-witnessed-flat-domains vs lem-sf-comparison-tor-amplitude: the existing statement transfers Tor bounds between sites, without constructing flat coefficient reductions or the compactification inputs.

lem-sf-pf-reduction-witnessed-flat-domains vs lem-trf-open-ctf: the existing statement preserves one input under j_!, not the etale witnesses and coefficient/tensor models in this child.

lem-sf-pf-reduction-proper-open-identities vs lem-sbc-strict-perfect-tower-projection: the existing statement concerns local perfectness and invertibility of the strict tower projection for strict towers or completed objects, not the two finite-ring compactification-factor identities and normalization of c_f.

lem-sf-pf-reduction-proper-open-identities vs def-sbc-quotient-exchange-scalar-comparisons: the existing statement defines quotient specialization and scalar comparison equation, rather than asserting these two finite-quotient proper/open tensor identities.

lem-sf-pf-reduction-proper-open-identities vs def-sbc-strict-augmented-coefficient-presentation: the existing statement defines normalized strict augmented coefficient square presentation, rather than asserting these two finite-quotient proper/open tensor identities.

lem-sf-pf-reduction-proper-open-identities vs lem-sbc-strict-reduction-pullback-square: the existing statement concerns the normalized coefficient reduction square before taking mates for strict towers or completed objects, not the two finite-ring compactification-factor identities and normalization of c_f.

lem-sf-pf-reduction-proper-open-identities vs lem-sbc-strict-projection-coaugmentation: the existing statement concerns strict coefficient projection and the normalized limit coaugmentation for strict towers or completed objects, not the two finite-ring compactification-factor identities and normalization of c_f.

lem-sf-pf-reduction-proper-open-identities vs def-sbc-quotient-coefficient-presentation: the existing statement defines quotient coefficient presentations and exact derived scalar restriction, rather than asserting these two finite-quotient proper/open tensor identities.

lem-sf-pf-reduction-proper-open-identities vs lem-sbc-strict-tower-mate-evaluation: the existing statement concerns normalized evaluation of the actual strict tower square mate for strict towers or completed objects, not the two finite-ring compactification-factor identities and normalization of c_f.

lem-sf-pf-reduction-proper-open-identities vs lem-sbc-strict-quotient-exchange-unit-equation: the existing statement concerns coaugmentation equation for the strict perfect-coefficient exchange for strict towers or completed objects, not the two finite-ring compactification-factor identities and normalization of c_f.

lem-sf-pf-reduction-proper-open-identities vs def-sbc-strict-coefficient-exchange-arrows: the existing statement defines canonical strict coefficient exchange arrows and evaluation, rather than asserting these two finite-quotient proper/open tensor identities.

lem-sf-pf-reduction-proper-open-identities vs lem-sf-constant-semilinear-generator-comparison: the existing statement concerns scalar restriction identifies the single proper and open reduction generators for strict towers or completed objects, not the two finite-ring compactification-factor identities and normalization of c_f.

lem-sf-pf-reduction-proper-open-identities vs lem-sf-generator-reduction-coherence: the existing statement concerns basic generator coefficient squares in semilinear systems for strict towers or completed objects, not the two finite-ring compactification-factor identities and normalization of c_f.

lem-sf-pf-reduction-proper-open-identities vs lem-weil-pbc-completed-reduction-pullback-square: the existing statement concerns completed reduction respects the strict inverse-image square for strict towers or completed objects, not the two finite-ring compactification-factor identities and normalization of c_f.

lem-sf-pf-reduction-proper-open-identities vs lem-weil-pbc-ringed-square-tensor-compatibility: the existing statement concerns tensor compatibility of a ringed square on flat k-flat representatives for inverse-image or tensor squares, with no canonical open tensor projection identity and no factorization of c_f.

lem-sf-pf-reduction-proper-open-identities vs lem-weil-pbc-ringed-exchange-tensor-coherence: the existing statement is reused for the proper identity, but has neither the normalized open scalar/tensor identity nor the compact-support coefficient-map factorization.

lem-sf-pf-reduction-proper-open-identities vs lemma-weil-pbc-completed-exchange-coherence: the existing statement concerns completed exchange coherence for strict towers or completed objects, not the two finite-ring compactification-factor identities and normalization of c_f.

lem-sf-pf-reduction-proper-open-identities vs lem-weil-pbc-finite-reduction-pullback-coherence: the existing statement concerns finite reduction and the canonical pullback square for inverse-image or tensor squares, with no canonical open tensor projection identity and no factorization of c_f.

lem-sf-pf-reduction-proper-open-identities vs lem-weil-pbc-finite-reduction-pullback-square: the existing statement concerns finite reduction respects the inverse-image square for inverse-image or tensor squares, with no canonical open tensor projection identity and no factorization of c_f.

lem-sf-pf-reduction-proper-open-identities vs lem-weil-pbc-ordered-exchange-coefficient-comparison: the existing statement states coefficient normalization of the raw ordered completed exchange, a different exchange or comparison equation; it does not state the canonical finite A/B proper and open factor equations together.

lem-sf-pf-reduction-proper-open-identities vs lem-weil-pbc-finite-level-rectangle: the existing statement states finite-level exchange rectangle, a different exchange or comparison equation; it does not state the canonical finite A/B proper and open factor equations together.

lem-sf-pf-reduction-proper-open-identities vs lem-weil-pbc-completed-exchange-unit: the existing statement concerns completed exchange extends the ordinary mate along its unit for strict towers or completed objects, not the two finite-ring compactification-factor identities and normalization of c_f.

lem-sf-pf-reduction-proper-open-identities vs def-weil-pbc-ringed-tensor-square-presentation: the existing statement defines representative presentation of a commutative ringed tensor square, rather than asserting these two finite-quotient proper/open tensor identities.

lem-sf-pf-reduction-proper-open-identities vs lem-weil-pbc-flat-scalar-tower-exchange: the existing statement concerns flat scalar restriction transports the strict-diagram adjunction mate for strict towers or completed objects, not the two finite-ring compactification-factor identities and normalization of c_f.

lem-sf-pf-reduction-proper-open-identities vs lem-weil-pbc-intrinsic-finite-exchange-rectangle: the existing statement states finite exchange rectangle for intrinsic coefficient reduction, a different exchange or comparison equation; it does not state the canonical finite A/B proper and open factor equations together.

lem-sf-pf-reduction-proper-open-identities vs lem-pur-projection-comparison-etale-origin: the existing statement compares etale and pro-etale sites at one coefficient ring, without changing the coefficient ring or supplying the two factor identities.

lem-sf-pf-reduction-proper-open-identities vs lem-sp-categorical-projection-mate-square: the existing statement is an abstract proper-projection result conditional on compatible tensor comparison data; it does not establish the canonical geometric open comparison or identify c_f.

lem-sf-pf-reduction-proper-open-identities vs lem-sp-compact-projection-base-change: the existing statement changes the scheme by base change with fixed coefficients (or works in a coefficient tower); it is not the intrinsic change A to B between two module categories.

lem-sf-pf-reduction-proper-open-identities vs lem-pur-finite-proper-product-transpose: the existing statement concerns the symmetry/transpose of an external product over a fixed ring; it does not assert change-of-ring identities for the two compactification factors.

lem-sf-pf-reduction-proper-open-identities vs lem-sp-completion-mate-comparison: the existing statement concerns the strict quotient-tower exchange realizes the completed-adjunction mate for strict towers or completed objects, not the two finite-ring compactification-factor identities and normalization of c_f.

lem-sf-pf-reduction-proper-open-identities vs lem-amb-shriek-tensor-composition: the existing statement compares compactifications for composition of scheme maps at fixed coefficients; it does not assert the two coefficient-ring change factor identities.

lem-sf-pf-reduction-proper-open-identities vs lem-amb-compactification-projection-composition: the existing statement compares compactifications for composition of scheme maps at fixed coefficients; it does not assert the two coefficient-ring change factor identities.

lem-sf-pf-reduction-proper-open-identities vs lem-amb-shriek-projection-open-restriction: the existing statement concerns compact-support projection maps commute with open base restriction for strict towers or completed objects, not the two finite-ring compactification-factor identities and normalization of c_f.

lem-sf-pf-reduction-proper-open-identities vs lem-pur-co-smooth-pf-exchange-coherence: the existing statement concerns a cartesian scheme square at fixed coefficients; the present equations use the identity of underlying sites and a possibly nonflat ring map.

lem-sf-pf-reduction-proper-open-identities vs lem-fix-etale-origin-scalar-projection-square: the existing statement compares the restriction of one scalar-coefficient proper mate with an etale-origin arrow; it does not include an arbitrary second tensor input L or the normalized open tensor equation.

lem-sf-pf-reduction-proper-open-identities vs lem-pur-finite-forward-product-symmetry: the existing statement concerns the symmetry/transpose of an external product over a fixed ring; it does not assert change-of-ring identities for the two compactification factors.

lem-sf-pf-reduction-proper-open-identities vs lem-fix-open-scalar-tensor-normalization: the existing statement already gives the open subidentity and should be cited for that subargument; it does not give the proper projection identity and the specified proper/open factorization of c_f.

lem-sf-pf-reduction-proper-open-identities vs lem-sf-open-tensor-normalization: the existing statement normalizes open maps and restrictions but does not give the proper coefficient mate identity or its relation to c_f.

lem-sf-pf-reduction-proper-open-identities vs lem-sf-pf-coefficient-realization-transport: the existing statement assumes all primitive-map compatibilities, including the open gamma comparison, as supplied data; this child establishes the two canonical finite coefficient factor equations rather than assuming them.

lem-sf-pf-reduction-proper-open-identities vs det-sp-reduction-direct-image: the existing statement is reused to pin c_f to the proper mate followed by open scalar comparison, but states no projection/tensor factor identity.

Neither new node equals a clause of the parent. The first has only object/model/domain conclusions; the second stops at the two separate factor identities. No existing statement searched supplies either whole new statement by one-line specialization. Their proof workers should cite the existing component theorems named above; those components were deliberately not recreated as new nodes.

## Preserved argument, verbatim from the returned split

These are the exact returned paragraphs, retained as the proof work allocation for the unsplit children and the audit trail for the assembly. They are report text, not proof steps in a statement-only child.

### Returned step 1 — lem-sf-pf-reduction-witnessed-flat-domains

First check the coefficient domains, without invoking axioms (A3) or (A5) of the datum. By [lem-sf-proetale-constructible-origin], choose bounded constructible étale representatives of $K,L$ and retain their comparison isomorphisms as étale-origin witnesses. By clause (ii) of [lem-sf-comparison-tor-amplitude], the representatives have the same finite Tor amplitudes. The constructible variant of [lem-sf-flat-model] applies because $X,Y$ are finite type over a field, hence Noetherian: choose bounded flat constructible étale models $P,Q$. With $A=A_{E,n}$ and $B=A_{E,m}$, their termwise tensors with $B$ represent the derived reductions. Each term remains flat over $B$, since $(P^i\otimes_A B)\otimes_B N=P^i\otimes_A N$ for a $B$-module sheaf $N$ and restriction of scalars is exact; it remains constructible since on a common finite stratification its values are finite modules tensored with the finite ring $B$. Thus the reductions are bounded constructible and have finite Tor amplitude, with the same bounds. The same models show that $K\otimes_A^L Lf^*L$ is bounded constructible of finite Tor amplitude: inverse image is exact for constant coefficients, takes each flat locally constant term on a stratum to such a term on its inverse image, and the bounded total tensor model has amplitude bounded by the sums of the two intervals. Clause (i) of [lem-sf-comparison-tor-amplitude] returns these objects and their finite-Tor properties to the pro-étale site. All operations below are taken on these witnessed realizations.

Cited existing statements: lem-sf-proetale-constructible-origin, lem-sf-comparison-tor-amplitude, lem-sf-flat-model.

### Returned step 2 — parent assembly

Put $\rho_T=-\otimes_A^L B$ on each scheme $T$, and suppress the subscript when its scheme is determined. Let $c_f(M):\rho Rf_{!,A}M\xrightarrow{\sim}Rf_{!,B}\rho M$ be [lem-fix-compact-support-coefficient-change], and let $s$ and $t$ denote the tensor and pullback comparisons of [lem-fix-operation-reduction]. Define $u$ by $\rho(Rf_{!,A}K\otimes_A^L L)\xrightarrow{s}\rho Rf_{!,A}K\otimes_B^L L_m\xrightarrow{c_f(K)\otimes1}Rf_{!,B}K_m\otimes_B^L L_m$. Define $v$ by $\rho Rf_{!,A}(K\otimes_A^L Lf_A^*L)\xrightarrow{c_f(K\otimes Lf_A^*L)}Rf_{!,B}\rho(K\otimes_A^L Lf_A^*L)\xrightarrow{Rf_{!,B}(s,t)}Rf_{!,B}(K_m\otimes_B^L Lf_B^*L_m)$. Both $u$ and $v$ are isomorphisms by the cited statements and the domains checked in step 1. The square to be proved is precisely
$$
\begin{array}{ccc}
\rho(Rf_{!,A}K\otimes_A^L L)&\xrightarrow{\rho(\operatorname{PF}_{A})}&\rho Rf_{!,A}(K\otimes_A^L Lf_A^*L)\\
{\scriptstyle u}\downarrow&&\downarrow{\scriptstyle v}\\
Rf_{!,B}K_m\otimes_B^L L_m&\xrightarrow{\operatorname{PF}_{B}}&Rf_{!,B}(K_m\otimes_B^L Lf_B^*L_m).
\end{array}
$$
In particular its upper arrow is the reduction of the level-$n$ map.

Cited existing statements: lem-fix-operation-reduction, lem-fix-compact-support-coefficient-change.

### Returned step 3 — lem-sf-pf-reduction-witnessed-flat-domains

As before, $Y$ is quasi-compact and quasi-separated, so [thm-nagata-compactification] gives $f=pj$ with $j:X\hookrightarrow\overline X$ open and $p:\overline X\to Y$ proper. Put $M=j_!K$. Apply [lem-trf-open-ctf]: $M$ is bounded constructible with the same Tor bounds as $K$. Apply the same lemma to $K\otimes_A^L Lf_A^*L$, whose domain was checked in step 1. The open projection isomorphism [lem-cbc-extension-zero-projection-formula] identifies its extension by zero with $M\otimes_A^L Lp_A^*L$, using $Lj^*Lp^*=Lf^*$. This checks both proper-factor inputs. Their étale-origin witnesses are supplied by [lem-sf-proetale-constructible-origin].

Cited existing statements: thm-nagata-compactification, lem-trf-open-ctf, lem-cbc-extension-zero-projection-formula, lem-sf-proetale-constructible-origin.

### Returned step 4 — lem-sf-pf-reduction-proper-open-identities

By [def-exchange-projection] and [def-sf-pf], at either coefficient ring $R=A,B$ the specified map is $\operatorname{PF}_R=Rp_{*,R}(\gamma_R)\circ\pi_R$, with $\pi_R$ the adjunct of $(\varepsilon_R\otimes1)\circ\mu_R$. For proper $p$, the compactification $(\operatorname{id},p)$ identifies $Rp_!$ with $Rp_*$ by [def-compact-support-direct-image-detailed]. The canonical coefficient map $c_M:\rho Rp_{*,A}M\to Rp_{*,B}\rho M$ is the mate of $Lp_B^*\rho\cong\rho Lp_A^*$. More generally [det-sp-reduction-direct-image] pins the compact-support coefficient comparison for $f=pj$ to this proper mate followed by the canonical coefficient comparison for $j_!$. This is the same canonical tensor comparison $c_f$ used in step 2 [lem-fix-compact-support-coefficient-change]. The domains checked in step 3 apply. Here $A,B$ are finite rings killed by powers of $\ell$, and $p,j,f$ are maps of separated finite-type $k$-schemes, as required.

Cited existing statements: def-exchange-projection, def-sf-pf, def-compact-support-direct-image-detailed, det-sp-reduction-direct-image, lem-fix-compact-support-coefficient-change.

### Returned step 5 — lem-sf-pf-reduction-proper-open-identities

Apply [lem-weil-pbc-ringed-exchange-tensor-coherence] with the four ringed topoi $(\overline X_{\mathrm{proet}},A)$, $(Y_{\mathrm{proet}},A)$, $(\overline X_{\mathrm{proet}},B)$, $(Y_{\mathrm{proet}},B)$. The vertical maps are $p_A,p_B$; the horizontal maps are the identity maps of the underlying topoi with structure-ring maps $A\to B$. Their derived pullbacks are $\rho_{\overline X},\rho_Y$. The square commutes as a square of ringed topoi, and its pullback comparison is exactly $t:Lp_B^*\rho_Y\cong\rho_{\overline X}Lp_A^*$. These are small sites in a common chosen universe. Its exchange map is the mate $c$ pinned in step 4, and its projection maps are precisely $\pi_A,\pi_B$, since all are defined using the same tensor comparison and counit. With inputs $E=M,Q=L$, its displayed equality therefore says
$$Rp_{*,B}(s,t)\circ c_{M\otimes Lp_A^*L}\circ\rho\pi_A
=\pi_B\circ(c_M\otimes1)\circ s.$$
The lemma requires no Cartesian hypothesis and no flatness of $B$ over $A$. This supplies the entire proper-factor mate calculation formerly inline.

Cited existing statements: lem-weil-pbc-ringed-exchange-tensor-coherence.

### Returned step 6 — lem-sf-pf-reduction-proper-open-identities

For the open factor use [lem-sf-open-tensor-normalization] with $g=\operatorname{id}_{\overline X}$ and structure-ring map $A\to B$. Its $\beta$ is $d_H:\rho j_{!,A}H\xrightarrow{\sim}j_{!,B}\rho H$, and its $\gamma$ is the canonical open tensor identification at each level. Under these isomorphisms both the source and target of the desired identity are in the essential image of $j_{!,B}$. The lemma gives invertible open units and full faithfulness of extension by zero; hence restriction to the open is faithful between these objects. After restriction, its normalized $\beta$ and $\gamma$ become identities. The remaining tensor and pullback identifications are the canonical coherent ones of [lem-fix-operation-reduction], so both routes are the same tensor/pullback comparison, including $Lj^*Lp^*=Lf^*$. Faithfulness gives
$$d_{K\otimes Lf_A^*L}\circ\rho\gamma_A=\gamma_B\circ(d_K\otimes1)$$
with $s,t$ inserted on source and target. Thus the open compatibility follows from a cited normalization theorem, rather than an unproved assertion that its construction commutes with reduction.

Cited existing statements: lem-sf-open-tensor-normalization, lem-fix-operation-reduction.

### Returned step 7 — parent assembly

Compose the proper-factor identity of step 5 with the image by $Rp_{*,B}$ of the open-factor identity of step 6. Substitute $\operatorname{PF}_R=Rp_{*,R}(\gamma_R)\circ\pi_R$ and the proper-mate/open-comparison factorization of $c_f$ from step 4. Naturality of $c$ moves $\rho Rp_{*,A}(\gamma_A)$ past $c$; the two middle tensor/pullback identifications cancel. The resulting source composite is $\operatorname{PF}_B\circ u$, and the target composite is $v\circ\rho(\operatorname{PF}_A)$, using exactly the definitions of $u,v$ in step 2. Therefore the required square commutes. This is an equality of specified morphisms, established before any stalk or generating-class argument.

Cited existing statements: def-exchange-projection, det-sp-reduction-direct-image.

### Returned step 8 — parent assembly

The commutative square and the inverses of $u,v$ show that $\rho(\operatorname{PF}_A)$ is invertible if and only if $\operatorname{PF}_B$ is invertible. This cancellation concerns the reduced map. For the asserted equivalence with the original map, apply [thm-sf-pf-finite] at $A$ and $B$ to the étale representatives from step 1: both $\operatorname{PF}_A$ and $\operatorname{PF}_B$ are isomorphisms, so the claimed equivalence holds. For the pro-étale realizations use the witnessed-realization clause of [lem-weil-finite-compact-projection-formula], which states precisely the same invertibility there. The representatives satisfy its bounded constructibility and finite-Tor hypotheses by step 1. This completes both the commutativity and the original-map invertibility assertion.

Cited existing statements: thm-sf-pf-finite, lem-weil-finite-compact-projection-formula.

