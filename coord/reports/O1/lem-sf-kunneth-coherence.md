# O1 repair: lem-sf-kunneth-coherence

Files written (all node paths are under dag/nodes/sec-six-functors/):

- lem-sf-kunneth-coherence.json: existing statement unchanged; six-step assembly, 2525 characters.
- lem-sf-proper-triple-counit-transpose.json: new statement, unsplit; no Mathlib match.
- lem-sf-triple-compactification-normal-form.json: new statement, unsplit; no Mathlib match.
- lem-sf-middle-exchange-projection-base-change.json: new statement, unsplit; no Mathlib match.

Three new nodes, zero Mathlib leaves. Each has proof=[], proof_deps=[], proof_origin=null, its own self-contained statement and coefficient hypotheses, current searches, and a precise blueprint.from place. citations.json records each cited node for each assembly step, with a verbatim excerpt of its statement. The new statements have 2563, 3538, and 2561 characters respectively: the work is distributed among comparable intermediate arguments.

Attachments: none. I searched lean/WeilConjectures/ for the blueprint tag and for the product, coherence, triple-counit and triple-compactification notions. Relative.lean's nonempty_iso_rightDerivedLowerShriek_externalProduct is sorry and asserts only existence of an isomorphism; its finite-coefficient assembly does not give the coherence of the specified map in all four coefficient stages. No declaration found states the item or any new node exactly.

WANTED: none. The sources needed for this repair are present.

The returned head is the shared read clone's item. At startup the sandbox had only dispatcher .brief files and no node, report, citations or search log, so there was no private earlier attempt to overwrite or discard. I copied the shared item, retaining its statement, imported metadata, searches, citations in the old proof, and maintainer-owned fields. The required initial dry run exited with the diagnostic that report.md was missing. No repository git command, local check_dag/review_split/preflight command, Lean write, compiler, Lake command, launcher modification, or agent launch was used.

The numbered return has one requirement: spread the 11302-character proof into at least three statement-only nodes and a <=3000-character assembly, preserving the old arguments rather than merely shortening their wording. This repair extracts the triple transpose (the old proper associativity calculation), the separate triple compactification normal forms (including all coefficient stages), and the middle exchange/PF base-change square. The elementary reversal of the canonical word, identity-factor cancellation, and rotations/adjacent swaps stay in the short assembly. The existing pair transpose and open/pair normalization nodes are reused. Nothing is moved wholesale into a new node and no new statement simply asserts clauses (i)--(iv) of the item. The exact eleven old arguments are preserved below as handoff material, with their destinations identified. No mathematical statement dispute was necessary.

## Not duplicates

lem-sf-proper-triple-counit-transpose vs lem-sf-proper-product-counit-transpose: the existing statement computes a single binary word and its intermediate q-transpose; the new statement computes the transposes of two nested words for three proper morphisms, with two different intermediate product schemes and counits.
lem-sf-proper-triple-counit-transpose vs lem-trf-relative-kunneth-counit: the existing statement is the binary transpose at finite coefficients; the new statement is the ternary nested calculation at all four stages.
lem-sf-proper-triple-counit-transpose vs lem-pur-finite-proper-product-transpose: the existing statement gives finite ordinary binary transposes and swap, including larger ambient inputs; it does not compute either ternary composite or handle the completed and field stages of the new node.
lem-sf-proper-triple-counit-transpose vs lem-coef-evaluation-transpose-coherence: the existing statement concerns internal Hom evaluation comparison for a strong monoidal functor, not the exchange/PF word on different scheme categories or its geometric triple counits.
lem-sf-triple-compactification-normal-form vs lem-sf-product-compactification-identity: the existing statement is a single pair at finite coefficients; the new statement identifies both nested triple composites separately with their proper counterparts followed by specified ternary open maps.
lem-sf-triple-compactification-normal-form vs lem-sf-integral-open-product-diagram-normalization: the existing statement gives the integral pair identity and associativity of e; the new statement also expands the two nested lambda composites, with naturality transporting the inner e, at finite, integral and field stages.
lem-sf-triple-compactification-normal-form vs lem-sf-open-external-tensor-normalization: the existing statement concerns only the open tensor comparison, not its interaction with nested proper pushforward product words.
lem-sf-triple-compactification-normal-form vs lem-pur-finite-product-compactification: the existing statement is a finite binary formula under witnessed ambient hypotheses; it has no triple formula or integral strict-diagram comparison.
lem-sf-middle-exchange-projection-base-change vs prop-sf-pf-coherence: the existing base-change square transports one PF; the new middle square also transports the exchange for (f,g) along a second square, requiring the two horizontal pastings and their pullback-composition comparisons. It excludes the outer PF_g and compositor, so it is not the item's base-change clause renamed.
lem-sf-middle-exchange-projection-base-change vs lem-sf-pf-compactification-pasting: the existing statement pastes proper and open PF factors within a chosen compactification, conditional on two factor identities; the new statement transports Ex_{f,g} followed by PF_q across the product cube over B'.
lem-sf-middle-exchange-projection-base-change vs lem-kun-proj-formula-natural: the existing statement transports an ordinary direct-image PF on etale module complexes; it has no preceding compact-support exchange for the product and no integral or field stages.
lem-sf-middle-exchange-projection-base-change vs lem-kun-bc-base-change: the existing cube transports ordinary abelian inverse-image exchange, with no PF or coefficient-stage passage; the new middle square has both the compact-support exchange and PF_q.

I searched the entire DAG by these concepts and the whole blueprint using blueprint_refs.py ancestor and search (three-counit, triple compactification, transpose, compactification identity, projection transformation, exchange-projection). Broad hits include the item's own coherence clauses and package statements, which depend on the item and cannot be used below it. The relevant smaller statements were read above and reused or distinguished. No Stacks tag is assigned as an exact source theorem to a newly invented result: these are explicit intermediate comparisons extracted from the blueprint argument. The Stacks tags below support the calculation and its existing component nodes; the blueprint remains the source of the extracted statements. same_as is [] for the three new intermediate statements.

## Review by O1

I read the chapter and the sk-thm-sf-kunneth-relative unit record, GOAL.md, the three blueprint levels in SETUP.md, the standing worker brief, stages/1-dag.md and delivery-errors B--E. The unit route is the composition/exchange/PF route; all three extractions remain in that unit. I read the current main-20261015 coherence statement and proof in full. Its last sentence identifies the proper two-counit transpose, its proper-reduction sentence is the source of the compactification calculation, and its clause (iii) explicitly calls for PF_q, PF_g and the three exchange squares. These are the precise places recorded for the new nodes. I also read the relevant Stacks source text: sites-cohomology.tex, remark-base-change (07A7), equation-projection-formula-map (0B56), remark-compatible-with-diagram (0E48), remark-compose-base-change and remark-compose-base-change-horizontal (0E46/0E47); sites-modules.tex lemma-extension-by-zero (03DI), lemma-extension-by-zero-exact (03DJ); more-etale.tex lemma-shriek-proper-and-open-base-change (0F7F), lemma-shriek-composition (0F7J). No SGA source is used. The diagram verifications Stacks omits are retained as arguments below and as the new intermediate statements, not treated as established by their references alone.

For the first new node I checked both outer two-counit transposes. On the left, pulling lambda_{f,g} into the first outer counit gives epsilon_t followed by Lt*lambda_{f,g}, the binary transpose c_{f,g}. On the right, naturality of epsilon_z at lambda_{g,h} gives c_{g,h}. Pullback to V identifies their factors, so both give the same tensor of epsilon_f, epsilon_g, epsilon_h. This is more than a statement that two abstract isomorphisms exist: the explicit word fixes every map. Proper products and projections remain proper by the existing permanence node. The pair-transpose node, adjunction-compatible composition, and monoidal pullback comparisons are available at every coefficient stage, so no completed Hom faithfulness is inserted. I checked the all-identity case, one identity factor, a zero complex and an empty product: the displayed counit morphisms reduce to the appropriate identity or zero morphisms with matching source and target.

For the second new node I checked the types of both ternary open composites: e_{j1,j2} first changes the first two extended factors to j12! of their product, then e_{j12,j3} has exactly that source; the other order uses e_{j2,j3} then e_{j1,j23}. Product opens are intersections of inverse-image opens. Product proper maps remain proper. Expanding the inner and outer pair compactification identities and using naturality of the outer proper word moves each inner e to the output. This yields the two distinct identities asserted in the new statement, rather than assuming their equality in order to prove it. The two e maps agree because they are the normalized ternary open comparisons of the existing open/integral node, whereas equality of the proper iterates is supplied separately by the first new node. Extension by zero and the proper compact-support images stay on the stipulated finite-Tor operation domain of def-sf-datum. The all-open and all-proper cases give the expected open map and proper map; if one input is zero or empty every formula still has the zero source and target.

I checked the integral hypotheses used in that argument, not just the names of the operations. The statement of lem-weil-l-adic-extension-integers-dvr makes O_E a PID with finite residue field; one generator for every ideal implies Noetherianity. lem-weil-valued-dvr-finite-quotients gives finiteness of O_E/(varpi^m). The finite-type schemes and their product compactifications are Noetherian by lem-weil-pbc-finite-type-over-noetherian over the field k. The finite reductions lie in the bounded constructible domain and lem-sf-proetale-constructible-origin(ii) supplies bounded etale-origin witnesses. These are the hypotheses used by lem-sf-integral-open-product-diagram-normalization and its proper/open diagram comparison, whose statement I read. Only the actual reduction diagrams have transition maps. All equalities are established in their derived diagram category before applying functorial Rlim. Rationalization and common finite coefficient fields transport those equalities; no conclusion is inferred merely from equality of all finite reductions of an integral morphism. This preserves every precaution of the old step 8.

For the third new node I checked the two routes from LbY*(Lg*F tensor L) to Rq'!D'. The PF_q square moves LbY* through PF_q. The horizontal-pasting equation identifies the old exchange followed by exchange for q along bY with exchange for f along b followed by the new (f',g') exchange. The canonical equality gbY=bg' and the pullback tensor isomorphism give exactly delta and chi as written. This square stops before the outer Rg!, Psi_g and alpha, so assembly still has work to do. With b the identity all comparisons become identities and the equation is beta=beta. With f or g an identity it reduces to the PF/exchange identity laws. No properness of b is used; B' is separated finite type over k exactly as in the item. I retained all witnessed, completed, lattice and common-stage domain conventions from fix-lem-exchanges, rather than using arbitrary pro-etale unbounded inputs.

For each assembly step I opened each cited node's statement and checked the actual assertion used:

1. thm-sf-kunneth-relative defines precisely the six-arrow composite; reversing it gives the explicit word in the new nodes. This is an elementary inversion of composites, and uses no coherence assertion from the parent theorem (whose proof is above this coherence lemma in the dependency graph).
2. lem-sf-proper-product-counit-transpose states the exact two-counit transpose for all stages; lem-pur-derived-pullback-tensor-iso states symmetry, associativity and composition compatibility of the pullback comparison; fix-prop-adjunctions(1),(3) supplies the ordinary Hom bijections and composition normalization. The new triple lemma states both transposes. Thus naturality of signed symmetry and injectivity of the Hom bijection give proper symmetry and associativity. No arbitrary unsigned flip is substituted.
3. lem-sf-product-compactification-identity states the exact finite pair equality; lem-sf-integral-open-product-diagram-normalization states its completed equality and field transports; lem-sf-open-external-tensor-normalization explicitly states signed symmetry. The new triple normal-form node states both separate triple formulas and e_L=e_R. Applying equality under Rc* and composing with the proper equality from step 2 proves the general clauses. This uses statements, not hidden constructions from the cited proofs.
4. The new middle-square statement gives precisely the PF_q/exchange equation. prop-sf-pf-coherence explicitly displays the PF base-change square, and its naturality transports the outer symmetries through lem-pur-derived-pullback-tensor-iso. fix-lem-exchanges(2) explicitly gives vertical pasting including the compact-support composition comparisons. Substitution leaves exactly the word for the base-changed lambda. Every non-elementary compatibility is therefore a cited statement.
5. thm-sf-comp-composition states identity normalization at finite coefficients; fix-lem-exchanges(2) states its completed and transported forms as well as identity-square exchange; prop-sf-pf-coherence states identity PF. The only remaining cancellation is sigma squared equals identity, leaving PF_f. I checked the ordering p=identity, q=f, so the surviving PF is indeed PF_{f,K,L}.
6. def-sf-datum supplies the symmetric monoidal coefficient-category structure and canonical finite-Tor operation domains. The rotation/adjacent-swap reduction is an elementary induction using the already proved binary and triple clauses: orient rotations towards the left-associated tree and insert adjacent swaps; symmetry involution, disjoint commutation and the hexagon give the permutation relations. thm-sf-kunneth-relative states the compact-support product of the restrictions to the closed subschemes, and lem-pur-derived-pullback-tensor-iso states that its pullback identifications respect the tensor constraints. Applying the clauses to their structure maps proves the closed-subscheme case. This is not cohomology with supports, and r=1 remains the identity.

I checked the B--E checklist against the files: the new statements introduce every object and comparison, cite their notion definitions, contain no proof sketches or proof steps, and have genuine Mathlib searches rather than invented ones. Every search was run by the required msearch.py and its full returned hits are in search-results/; searches.jsonl was read and preserved. Each node had two different semantic phrasings before a no-match conclusion, plus Loogle, grep and LeanSearch. I read Monoidal/Functor.lean:1036--1039: its monoidal-adjunction counit identity is a potential proof tool, but identifying two scheme-dependent exchange/PF words is not a one-line specialization. ExponentiableMorphism.lean:40--49 concerns Over categories, and ExternalProduct/Basic.lean:29--46 defines tensor of diagrams. Neither states these geometric comparisons. Scalar-completion and topological compactification hits likewise do not identify the required maps. No new Mathlib leaf was claimed.

The statement of the item, chapter/unit route, all import flags and blueprint metadata, and maintainer-owned fields remain unchanged. New node proof dependencies are empty, and none has a dependency on the item; the inline word avoids such a cycle. New statement dependencies are only the notions/comparison maps needed to state them. The one off-unit assembly tool is the already accepted monoidal-pullback comparison, declared in split_report.tool_uses. The old longer steps are now handed off below instead of erased. The six assembly steps have no non-elementary step over 2000 characters and total 2525 characters. No unfinished repair point remains in the written split; the three new arguments are intentionally unsplit work for subsequent workers, as the return requires.

## Preservation and allocation of every old argument

The text below is the returned proof verbatim, not a proof hidden inside a new unsplit statement. It is the handoff to the workers who will split the three independent new nodes. The allocation keeps already-existing sublemmas in place rather than duplicating them.

### Returned step 1

Destination: Canonical word retained verbatim in the statements of the proper-triple and triple-compactification nodes; its middle factor is also explicit in the middle-square node. Assembly step 1 identifies it with kappa inverse.

Write $F=Rf_!K$, $G=Rg_!L$, and $D=Lp^*K\otimes^LLq^*L$. All maps below are on the finite-Tor domains of the supplied datum [def-sf-datum]; in particular its pullback, tensor, and compact-support functors can be iterated on these inputs. By the actual definition of the canonical map in [thm-sf-kunneth-relative], its inverse $\lambda_{f,g}=\kappa_{f,g}^{-1}$ is
$$\lambda_{f,g}=\alpha_{g,q}\circ Rg_!\bigl(\operatorname{PF}_{q,Lp^*K,L}\circ(\operatorname{Ex}_{f,g}(K)\otimes1_L)\bigr)\circ\Psi_g(F,L),$$
where $\Psi_g(F,L):F\otimes G\to Rg_!(Lg^*F\otimes L)$ is $\operatorname{PF}_{g,L,F}$ preceded by the source symmetry and followed by $Rg_!$ of the target symmetry. Here $\operatorname{Ex}_{f,g}:Lg^*Rf_!\to Rq_!Lp^*$ has exactly the direction in (A2), and $\alpha_{g,q}:Rg_!Rq_!\to Rt_!$ is (A4). This follows by reversing, in order, the six arrows defining $\kappa$, not by choosing an arbitrary product isomorphism.

Cited nodes: def-sf-datum, thm-sf-kunneth-relative, def-sf-pf.

### Returned step 2

Destination: Existing lem-sf-proper-product-counit-transpose is retained as the binary ingredient of the new proper-triple argument and assembly step 2; it is not duplicated by a new binary node.

Suppose $f,g$ proper; their product $t$ and both projections are proper by [lem-weil-pbc-proper-fp-permanence]. Apply [lem-sf-proper-product-counit-transpose] to the precise formula of step 1, with $F=Rf_*K$, $G=Rg_*L$. It identifies its transpose under $Lt^*\dashv Rt_*$ with
$$c_{f,g}:Lt^*(F\otimes G)\cong Lp^*Lf^*F\otimes Lq^*Lg^*G\xrightarrow{Lp^*\varepsilon_f\otimes Lq^*\varepsilon_g}D.$$
The same lemma supplies the intermediate $q$-transpose and the canonical proper normalization; thus this computation applies to the specified $\lambda$, with its completed and field interpretations, rather than an arbitrary isomorphism.

Cited nodes: lem-weil-pbc-proper-fp-permanence, lem-sf-proper-product-counit-transpose.

### Returned step 3

Destination: The signed two-counit naturality calculation remains assembly step 2, using the existing binary transpose; the triple node fixes the same signed comparisons for its three factors.

For proper $f,g$, naturality of the derived symmetry gives
$$\sigma_D\circ(Lp^*\varepsilon_f\otimes Lq^*\varepsilon_g)=(Lq^*\varepsilon_g\otimes Lp^*\varepsilon_f)\circ\sigma_{Lt^*(F\otimes G)},$$
where the source symmetry is read through the symmetric monoidal pullback comparisons [lem-pur-derived-pullback-tensor-iso] and the product swap. Hence step 2 gives equal transposes for the two swapped versions of $\lambda$. The adjunction bijection in [fix-prop-adjunctions] makes the original maps equal. Taking inverses proves (i) in the proper case. This retains the signed symmetry; it does not replace it by an unsigned flip.

Cited nodes: lem-pur-derived-pullback-tensor-iso, fix-prop-adjunctions.

### Returned step 4

Destination: Entire calculation belongs to lem-sf-proper-triple-counit-transpose; its two explicit transpose conclusions are stated there. This is the first new independent argument.

For proper $f,g,h$, put $H=Rh_*M$, $V=X\times_BY\times_BW$, $v:V\to B$, with projections $r_X,r_Y,r_W$; write $t_{g,h}:Y\times_BW\to B$ for the other two-factor structure map. The two inverse iterates are $\lambda_{t,h}\circ(\lambda_{f,g}\otimes1)$ and $\lambda_{f,t_{g,h}}\circ(1\otimes\lambda_{g,h})$, with the appropriate fibre-product identifications. Apply the formula of step 2 to the outer pair. In the first iterate, naturality of the tensor comparison and of the outer counit moves $L(r_{XY})^*\lambda_{f,g}$ next to $L(r_{XY})^*\varepsilon_t$; their composite is $L(r_{XY})^*c_{f,g}$ by the transpose equation for $\lambda_{f,g}$. It follows that the transpose under $Lv^*\dashv Rv_*$ is
$$Lv^*(F\otimes G\otimes H)\longrightarrow Lr_X^*K\otimes Lr_Y^*L\otimes Lr_W^*M,$$
namely $Lr_X^*\varepsilon_f\otimes Lr_Y^*\varepsilon_g\otimes Lr_W^*\varepsilon_h$. For the second iterate, put $z:Y\times_BW\to B$ and $r_{YW}:V\to Y\times_BW$. Its transpose first applies the outer two-counit map to $F\otimes Rz_*(L\boxtimes M)$ after $1\otimes\lambda_{g,h}$. Naturality of $\varepsilon_z$ replaces $\varepsilon_{z,L\boxtimes M}\circ Lz^*\lambda_{g,h}$ by $c_{g,h}$. Pulling this equation back by $r_{YW}$ gives $Lr_Y^*\varepsilon_g\otimes Lr_W^*\varepsilon_h$ in the last two factors; the first factor is $Lr_X^*\varepsilon_f$. Thus this transpose is also the displayed three-counit map. The pasted counits and mate pasting are [fix-prop-adjunctions] and [lem-weil-pbc-mate-pasting]; [lem-pur-derived-pullback-tensor-iso] identifies the two tensor bracketings. Injectivity of the adjunction bijection and then inversion prove (ii) for proper morphisms.

Cited nodes: fix-prop-adjunctions, lem-weil-pbc-mate-pasting, lem-pur-derived-pullback-tensor-iso.

### Returned step 5

Destination: Open comparison construction and normalization remain the existing lem-sf-open-external-tensor-normalization. They are inputs to the new triple-compactification node, which fixes both ternary e composites.

Work first at finite coefficients. The bounded constructible inputs have bounded etale-origin witnesses by clause (ii) of [lem-sf-proetale-constructible-origin], as required for the exchanges. Choose the supplied compactifications $f=aj$, $g=bk$ of [def-sf-datum], put $\bar T=\bar X\times_B\bar Y$, $u=j\times_Bk$, and let $c:\bar T\to B$. The product $u$ is open: its image is the intersection of the two inverse-image opens; $c$ is proper by [lem-weil-pbc-proper-fp-permanence]. Apply [lem-sf-open-external-tensor-normalization] to obtain the specific comparison
$$e_{j,k}:(j_!K)\boxtimes(k_!L)\xrightarrow{\sim}u_!(K\boxtimes L).$$
It restricts to the identity and satisfies both signed symmetry and three-factor associativity. This is the open tensor comparison used below; its construction and normalization have been extracted as a separate statement rather than inferred from compactification independence.

Cited nodes: lem-sf-proetale-constructible-origin, def-sf-datum, lem-weil-pbc-proper-fp-permanence, lem-sf-open-external-tensor-normalization.

### Returned step 6

Destination: Exact pair identity remains the existing lem-sf-product-compactification-identity. It is the pair input to the new triple-compactification argument and to assembly symmetry.

For these finite-coefficient compactifications, [lem-sf-product-compactification-identity] gives the equality of specified composites
$$\lambda_{aj,bk}(K,L)=Rc_*(e_{j,k})\circ\lambda_{a,b}(j_!K,k_!L).$$
Read its source as $Rf_!K\otimes Rg_!L=Ra_*j_!K\otimes Rb_*k_!L$, and its target as $Rt_!D=Rc_*u_!D$. Its $\lambda$ is exactly the formula of step 1. Its $e$ is the normalized map of step 5, and the equality respects refinement comparisons. Thus it permits reducing the actual canonical map, including its open factors, to the proper map.

Cited nodes: lem-sf-product-compactification-identity.

### Returned step 7

Destination: Entire expansion of the two iterates and movement of inner e belongs to lem-sf-triple-compactification-normal-form. Its conclusion is the two separate formulas, before the proper transposes are equated.

Apply step 6 also to the swapped pair and, for three inputs, to the compactification $j\times k\times l$ obtained from compactifications of $f,g,h$. At finite coefficients the proper symmetry of step 3 and the symmetry of $e_{j,k}$ in step 5 give (i). For (ii), expand both iterates by step 6. Naturality of the proper pair map moves the inner $e$ through it. Both results have the proper triple comparison of step 4 followed by the extension comparison
$$(j_!K)\boxtimes(k_!L)\boxtimes(l_!M)\longrightarrow(j\times k\times l)_!(K\boxtimes L\boxtimes M).$$
The two such extension comparisons agree by step 5; (A4)'s associativity in [def-sf-datum] identifies the final direct images. Thus both original iterates agree. All coefficients in the proper comparisons remain constructible finite Tor: this is the stipulated finite-Tor operation domain of the datum, including extension by zero as the compact-support image of an open immersion.

Cited nodes: def-sf-datum.

### Returned step 8

Destination: Entire coefficient-hypothesis verification and strict-diagram passage belongs to the new triple-compactification argument, using the existing integral node; the statement explicitly retains strict diagrams, witness scope, Rlim and field transport. The proper-triple node separately retains the all-stage proper interpretation.

At integral coefficients set $A=\mathcal O_E$, $I=(\varpi_E)$. The ring is a principal ideal domain with finite residue field by [lem-weil-l-adic-extension-integers-dvr]; hence it is Noetherian since every ideal has one generator. Every $A/I^m$ is finite by [lem-weil-valued-dvr-finite-quotients]. All schemes in the compactification diagrams are Noetherian by [lem-weil-pbc-finite-type-over-noetherian] over the Noetherian field $k$. The datum [def-sf-datum] supplies bounded constructible finite reductions, with bounded etale-origin witnesses by [lem-sf-proetale-constructible-origin] (ii). These check the hypotheses of [lem-sf-integral-open-product-diagram-normalization]. That lemma gives the completed open comparison, its symmetry and associativity, and precisely the compactification identity used in steps 5--7, by equalities in the strict diagram category before functorial derived inverse limit. The proper transpose calculation of step 2 already applies to completed operations by its cited lemma; therefore steps 3,4,7 prove (i),(ii) integrally. The same normalization lemma gives the rationalized and common-finite-field versions of the open comparisons and compactification identity. Applying the same proper and compactification arguments proves (i),(ii) for $E$ and $\overline{\mathbf Q}_\ell$. Equality of integral morphisms is never inferred merely from equality of their finite reductions.

Cited nodes: lem-weil-l-adic-extension-integers-dvr, lem-weil-valued-dvr-finite-quotients, lem-weil-pbc-finite-type-over-noetherian, def-sf-datum, lem-sf-proetale-constructible-origin, lem-sf-integral-open-product-diagram-normalization.

### Returned step 9

Destination: Middle PF_q square, cube and horizontal exchange-pasting calculation belongs to lem-sf-middle-exchange-projection-base-change. Outer PF_g, signed pullback and vertical pasting remain assembly step 4. Thus every factor of this calculation has a destination.

For (iii), use the base-changed data and exchange identifications of [thm-sf-kunneth-relative]: form $X',Y',T'$ over $B'$ and write $b_X,b_Y,b_T$ for their projections. Let $\chi:Lb_T^*D\xrightarrow{\sim}Lb_X^*K\boxtimes Lb_Y^*L$ be the monoidal pullback comparison of [lem-pur-derived-pullback-tensor-iso]. It suffices to check the inverse-map equation
$$Rt'_!(\chi)\circ\operatorname{Ex}_{t,b}\circ Lb^*\lambda_{f,g}=\lambda_{f',g'}\circ(\operatorname{Ex}_{f,b}\otimes\operatorname{Ex}_{g,b})\circ\mu_b.$$
Insert the expression in step 1. Move $Lb^*$ through each symmetry by its symmetric monoidality. Apply the displayed base-change square of [prop-sf-pf-coherence] to PF for $g$ along $b$, and to PF for $q$ along $b_Y$. Replace the two successive exchanges for $f$ along $g$ and $b_Y$ by those along $b$ and $g'$ using horizontal pasting in [fix-lem-exchanges], clause (2); replace the successive exchanges for $g,q$ by that for $t$ using its vertical-pasting equation. Their compatibility with composition is the same clause with its $\alpha$ comparisons. The factors remaining on the lower route are, in order, $\Psi_{g'}$, the exchange for $(f',g')$, PF for $q'$, and $\alpha_{g',q'}$, hence $\lambda_{f',g'}$. This gives the written equation, and inversion gives (iii). These are exactly the base-change maps and domains in the parent theorem, which already states compatibility for such $b$; its hypotheses, and the coefficient-domain conventions of the cited exchange and PF nodes, are retained.

Cited nodes: lem-pur-derived-pullback-tensor-iso, prop-sf-pf-coherence, fix-lem-exchanges, thm-sf-kunneth-relative.

### Returned step 10

Destination: Identity substitutions and the two-symmetry cancellation remain assembly step 5. They are routine from the cited identity laws and do not justify a new node.

For (iv), identify $X\times_BB$ with $X$, so $p=\mathrm{id}_X$ and $q=f$. In step 1, $\alpha_{\mathrm{id},f}$ is the identity: the composition law (A4) of [def-sf-datum] is the one of [thm-sf-comp-composition], which states that $\alpha_{g,f}$ is the identity when $f$ or $g$ is an identity, and the integral and field forms are obtained from it by the same functorial coefficient passage as in step 8, which carries identities to identities. $\operatorname{Ex}_{f,\mathrm{id}}$ is the identity by clause (2) of [fix-lem-exchanges], and $\operatorname{PF}_{\mathrm{id}}$ is the identity by [prop-sf-pf-coherence]. The source symmetry in $\Psi_{\mathrm{id}}$ is canceled by its target symmetry, so $\Psi_{\mathrm{id}}=1$. The only remaining factor is $\operatorname{PF}_{f,K,L}$; thus $\lambda_{f,\mathrm{id}}=\operatorname{PF}_{f,K,L}$ and $\kappa_{f,\mathrm{id}}=\operatorname{PF}_{f,K,L}^{-1}$.

Cited nodes: def-sf-datum, fix-lem-exchanges, prop-sf-pf-coherence, thm-sf-comp-composition.

### Returned step 11

Destination: Parenthesization induction, permutation relations and the application to closed subscheme structure morphisms remain assembly step 6, using established clauses and canonical pullback constraints. No new node simply restates the consequence.

For $r=1$ use the identity. For $r\geq2$ define a left-associated iteration of the binary map. Any other binary bracketing can be changed to this one by repeatedly replacing $A(B C)$ by $(A B)C$; clause (ii) preserves the resulting morphism at every replacement. For permutations, use adjacent swaps and clause (i). The symmetric monoidal constraints already present in the datum [def-sf-datum] ensure that two words for the same permutation induce the same signed tensor identification: the symmetry squared is the identity, disjoint swaps commute, and the hexagon gives the three-factor braid relation. Equivalently the same two- and three-counit and open-restriction calculations of steps 3--8 verify these relations on the product maps. This proves independence after the stated canonical constraints. Finally apply the result to the structure morphisms of the closed subschemes and the restricted objects in the compact-support clause of [thm-sf-kunneth-relative]. The pullback comparisons used there are symmetric and associative by [lem-pur-derived-pullback-tensor-iso], so the same identifications and base changes commute. This proves the asserted closed-subscheme compact-support compatibility; no cohomology-with-supports identification is involved.

Cited nodes: def-sf-datum, thm-sf-kunneth-relative, lem-pur-derived-pullback-tensor-iso.

