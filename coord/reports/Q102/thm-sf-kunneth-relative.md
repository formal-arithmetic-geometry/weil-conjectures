# Q102 repair: thm-sf-kunneth-relative

## Files written

- `dag/nodes/sec-six-functors/thm-sf-kunneth-relative.json`: existing statement unchanged; six assembly steps, 2400 proof-text characters, status split.
- `dag/nodes/sec-six-functors/lem-sf-relative-product-input-domains.json`: statement, unsplit; no Mathlib match for the combined geometric, finite-Tor and witnessed coefficient domains.
- `dag/nodes/sec-six-functors/lem-sf-relative-product-coefficient-factor-squares.json`: statement, unsplit; no Mathlib match for the individual coefficient/proper-normalization squares.
- `dag/nodes/sec-six-functors/lem-sf-relative-product-base-change-factor-squares.json`: statement, unsplit; no Mathlib match for the individual Cartesian base-change squares.
- `citations.json`: a literal statement quote for every node used by every parent step.

No unit file was changed: the key statement for this unit is the distinct existing node `sk-thm-sf-kunneth-relative`. The assigned child theorem's statement and split do not authorize changing that other node's realization.

## Attachments

None. The project declaration `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` in `lean/WeilConjectures/SixFunctors/Etale/Derived/Kunneth/Relative.lean` has `sorry`. Its proved `_of_iso` helper only assembles an isomorphism from supplied comparison hypotheses; it does not give the hypotheses, any higher coefficient stage, or the required coherence. Thus neither is an attachment for this item or any new task.

## WANTED

None. All sources used were already present; no literature was downloaded.

## Returned defect and repair

The only numbered return was the human's request to spread the 7294-character argument across at least two comparable statement-only tasks, retaining every argument and reducing the parent assembly to at most 3000 characters. The sandbox initially contained only dispatcher markers, no node files or report, so I copied the current shared node, whose nine steps have exactly the returned lengths. This is a mathematical re-split, not an unchanged re-push. The complete returned argument is retained below for the future workers, including all source citations. There are three new independent tasks, with statement lengths 2268, 2793 and 2985 characters. Each has a complete statement, hypotheses and source, empty proof and proof_deps, null proof_origin, status unsplit and logged Mathlib searches. None depends on the item or on another new task.

The domains task carries old step 1, including the affine-cover/generator composition argument, the diagonal factorization, the finite-Tor second variable and the finite etale-origin witnesses at the proper coefficient stages. It makes no assertion of the relative product isomorphism. The coefficient/proper task carries old step 6 at the level of its SIX individual factors; it does not assert the relative product theorem. The Cartesian-square task carries old step 7 at the level of SIX individual factor squares, including both projection squares, the exchange cube, composition, and signed monoidal comparisons. It does not assume or cite the downstream Kunneth-coherence theorem. These are separate proof obligations, rather than moving the whole parent into one node.

Parent step 2 retains the four-arrow construction in its original order (six arrows when the two symmetries are counted). Parent steps 5 and 6 retain old steps 8 and 9, so the application to closed subschemes, the restriction identity and the point-fibre tensor conversion are still proved in the parent. Parent steps 3 and 4 assemble the individual factor squares, rather than naming the desired composite compatibility as an unexplained lemma.

## Argument allocation (no part discarded)

| Returned step | Its argument now belongs to |
|---|---|
| 1 (1974 characters) | New input-domains task; the exact original argument and its existing dependencies are reproduced below for its future worker. |
| 2 (379 characters) | Parent step 2, first arrow, inverse composition. |
| 3 (395 characters) | Parent step 2, inverse projection at the projection to Y. |
| 4 (363 characters) | Parent step 2, inverse exchange followed by the first symmetry. |
| 5 (371 characters) | Parent step 2, final inverse projection and symmetry. |
| 6 (1173 characters) | New coefficient/proper factor-squares task; parent step 3 composes its squares. |
| 7 (1177 characters) | New base-change factor-squares task; parent step 4 composes its squares. |
| 8 (849 characters) | Parent step 5, including geometric typing, ordinary restrictions and pullback composition. |
| 9 (613 characters) | Parent step 6, inverse specialized map, point-fibre tensor and the distinction from extraordinary restriction. |

## Sources read

For the item I read both `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/thm-sf-kunneth-relative.md` and `_section.md`, the node's blueprint_update, and the master `_section.md` proof (1)--(4), finite-Tor paragraph, coherence (iii), and final specialization. The current node has already repaired the base-change quantifier to separated finite-type B'; I preserved it. The main snapshot's unit includes additional supported-direct-image assertions; those are not silently added to this child's statement. The current child keeps ordinary restrictions and explicitly excludes cohomology with supports from this relative assertion. The return requires keeping this child's statement.

For the input-domains task I read that source's finite-Tor paragraph together with the complete statements of `thm-sf-ctf-stability`, `lem-sf-proetale-constructible-origin`, `lem-pod-separated-finite-type-base-change`, `thm-sf-comp-composition`, `fix-lem-exchanges`, the finite-type and separated definitions, and closed-immersion permanence. Finite stability clauses (i), (ii), (iv), not the later exceptional/duality clauses, give the required domains. The datum supplies higher-stage operations; a finite origin witness is asserted for the finite reductions, never for discrete integral or rational etale objects.

For the coefficient/proper task I read the source's naturality and compatibility sentence, `def-sf-datum` (A4)--(A5), `def-sf-pf`, `fix-prop-projection-formula`, `prop-sf-pf-coherence`, and `cor-cbc-proper-coincidence`. The last statement gives the identity-open normalization and actual proper-base-change exchange at finite coefficients. At higher stages the coefficient comparisons are the supplied completed/transported ones. Replacement by R_* is made only for an actually proper morphism; the statement does not pretend that h is proper when only g is proper.

For the base-change task I read the source's displayed composite and coherence (iii), `fix-lem-exchanges` (its identity, pasting and composition clauses on witnessed finite and completed/transported domains), `prop-sf-pf-coherence` (its displayed base-change square), and `lem-pur-derived-pullback-tensor-iso` (monoidal and pullback-composition compatibility). The two projection squares have different base changes: v along y and g along b. The new statement specifies every intermediate beta map, including exchanging g before v; the exact two projection-square applications are retained in the old argument below. The unsplit statement defines the comparisons and asserts their equations, without including a proof sketch. No SGA source was used, including those listed in the fixed chapter record.

These sources are the blueprint's actual argument and the existing DAG's public interfaces. Since the blueprint is agent-written, the parent's proof_origin remains by agent. The new tasks are statement-only; their source locates the problem, not a claim that their proof is complete.

## Not duplicates

lem-sf-relative-product-input-domains vs lem-pur-relative-product-geometric-factors: the existing node concerns the finite concrete composition/exchange factors and their invertibility; the new task covers every intermediate finite-Tor input/output, second projection variable and the completed/rational/common-field domain certificates, and asserts no geometric-factor invertibility.
lem-sf-relative-product-input-domains vs thm-sf-ctf-stability: the stability theorem supplies finite operation preservation, but does not state the fibre-product geometry or the etale-origin witnesses of this product diagram and its higher-stage presentations.
lem-sf-relative-product-input-domains vs lem-sf-proetale-constructible-origin: origin equivalence alone has no finite-Tor intermediate-domain or geometric assertion.
lem-sf-relative-product-coefficient-factor-squares vs prop-sf-pf-coherence: projection coherence concerns PF, not the six-factor diagram, composition and inverse-exchange proper normalizations together.
lem-sf-relative-product-coefficient-factor-squares vs cor-cbc-proper-coincidence: proper coincidence is the finite exchange component, not the naturality and coefficient comparisons of every factor and higher coefficient presentations.
lem-sf-relative-product-base-change-factor-squares vs prop-sf-pf-coherence: the new task includes composition/exchange pasting and the intermediate cube, beyond the two PF squares supplied by projection coherence.
lem-sf-relative-product-base-change-factor-squares vs lem-sf-pf-compactification-pasting: the existing lemma is a conditional proper/open compactification-pasting identity for one PF; it does not state the six intermediate relative-product squares over a changed base.
lem-sf-relative-product-base-change-factor-squares vs lem-sf-kunneth-coherence: the existing node is a downstream statement about the composite, with a statement dependency on this item. The new task states the individual-factor identities without depending on this item, thereby avoiding a cycle.
lem-sf-relative-product-coefficient-factor-squares vs thm-sf-kunneth-relative: individual factor comparisons contain no assertion of the full product isomorphism or closed-subscheme formula.
lem-sf-relative-product-base-change-factor-squares vs thm-sf-kunneth-relative: six intermediate squares are more specific proof obligations, not a renamed statement of the parent or an assumption that its base-change conclusion already holds.

I searched the whole DAG by titles and statement concepts, including relative-product, Kunneth, input-domain, factor squares, etale-origin, proper identification and coefficient comparison, and used tools/blueprint_refs.py ancestor and search across the full imported blueprint. The potentially close nodes listed above were opened, as were sk-thm-sf-kunneth-relative and the downstream coherence node. No existing statement gives the three new assertions as written. The upstream project searches found the sorried relative theorem and its formal partial helper described above, not these new assertions. No new source uses a Stacks tag directly; the underlying Stacks inputs (09AK for origin and 07A4 for tensor pullback) remain their existing nodes, so no tag-level duplicate is introduced.

## Mathlib searches and verdicts

Each new task has two different semantic phrasings, a LeanSearch query, a Loogle pattern and a source grep made only through msearch.py. Their exact queries, original outputs and log digests are retained in searches.jsonl and search-results/0.txt through 14.txt. I read the returned declaration names/types. Domain searches found geometric base-change instances and ordinary sheaf pullbacks, not the combined finite-Tor/witnessed derived assertion. Coefficient/proper searches found condensed/locally-constant naturality and compactly supported function lemmas, unrelated to R_!. Base-change searches found ordinary pullback projection identities and LinearMap/IsBaseChange composition, not the six derived-operation squares. Thus all three are unsplit, and there are zero new Mathlib leaves. The item's old searches were retained verbatim, not claimed to have run today.

## Review by Q102

I checked this repair against B--E with the source and the node statements open. New nodes introduce all field, coefficient, scheme and input objects before using them; the factor chain is written out independently in each factor task. There are no proof sketches hidden inside their statements and no proof dependencies on unsplit nodes. The equations specify maps in the derived categories, not just degreewise identifications. Axiom (A5) comparisons are asserted only where they are defined: finite reductions at finite/integral stages and rationalization/common-field scalar extension at field stages. No new assumption was added to the parent.

For parent step 1, the input-domains statement explicitly lists P, Q, H, the intermediate Y-objects, the finite-Tor second variables, and witnessed coefficient domains. Step 2 uses the literal (A4), (A2) and (A3) clauses of def-sf-datum and the formula in def-sf-pf. The first projection uses (P,L), the second (L,Q); the two symmetries occur only after exchange and after the final projection, exactly as in the source's displayed definition. Step 3 uses the naturality and individual coefficient/proper factor equations in the new coefficient task and only composes them. Step 4 uses the explicit beta_{i+1} Lb*(d_i) = d_i' beta_i equation; its intermediate beta maps cancel by ordinary associativity and the endpoint maps are the specified exchanges. Neither step cites the proof of a node instead of its statement.

For parent step 5, closed-immersion-proper says explicitly that closed immersions are separated finite type. The finite affine-cover/generator composition and composite diagonal arguments are kept in the text, with the closed-immersion base-change and composition statements explicitly cited. The stability citation is used only for finite pullbacks, with higher domains supplied by the datum. The pullback-tensor lemma explicitly gives monoidality and pullback composition: its actual statement gives the claimed r-pullback identification. Thus the restriction is Li^*, not Ri^!. For step 6, the compact-cohomology definition explicitly says RΓ_c = Fib_s Ra_!, and the point-fibre lemma explicitly supplies Fib_s(M tensor N) ≅ Fib_s(M) tensor Fib_s(N). Its finite-Tor hypothesis follows from step 1 on the specialized data. These are the clauses copied literally in citations.json.

I tested empty X or Y, zero K or L, identity morphisms, n=1, and the point base. The constructions reduce respectively to zero diagrams, the identity normalized comparison factors, valid residue-ring operations, and exactly the displayed coefficient complexes. No proper replacement is used for a nonproper map. At B'=B the cube uses identity exchange normalizations; the signed symmetry is not treated as an unsigned swap. The domains task never identifies an arbitrary bounded constructible finite-coefficient complex with a perfect site complex: finite Tor suffices. The coefficient tasks do not replace completed integral coefficients by discrete etale coefficients. No new false statement, ill-typed clause, or change of proof route was found, so no STATEMENT-DISPUTED correction was needed.

I checked that the three new tasks are independent rather than one large replacement theorem. Their proof workloads are the returned 1974-character domain argument and the two separate 1173/1177-character factor comparisons. I preserved those arguments below for later workers, instead of discarding detail to meet the parent bound. All parent proof steps are below 2000 characters (the longest is below 800); no long step hides an additional comparison lemma. The remaining parent work is direct composition of supplied factors and the elementary specialization from existing pullback/fibre interfaces. Off-unit generic tool uses for finite-Tor pullback stability and monoidal pullback remain declared in split_report.tool_uses, with their purposes; no new maintainer-owned tool-use field was set.

## Unfinished work

The three new nodes intentionally have no proof: they are the parallel work requested by the return. Nothing else in the stage-1 repair is left unfinished. Lean formalization and compilation are outside this brief.

## Original returned arguments retained for the new workers

The following is a verbatim copy of the nine returned proof texts and their uses. This is a handoff of the existing arguments, not proof steps added to the unsplit task files.

### Returned step 1

Work in the axiomatized six-functor datum of [def-sf-datum]; this proof uses its explicitly supplied (A2)--(A5), not a claim that defining concrete operations proves those axioms. Put $T=X\times_BY$ and $h=g\pi_Y=f\pi_X$. The base-change theorem [lem-pod-separated-finite-type-base-change] gives that $\pi_X,\pi_Y$ are separated of finite type. For composition, the finite affine covers in the finite-type definition compose, and generators for $C$ over $A$ are the images of generators for $B/A$ together with generators for $C/B$. Separatedness of a composite follows because its diagonal is the composite of the diagonal of the first map and a base change of the diagonal of the second; both are closed immersions by the cited closed-immersion base-change and composition statements. Thus $h=g\pi_Y$ is also separated of finite type. The finite-Tor typing needed below is $L\pi_X^*K,L\pi_Y^*L\in D^b_{ctf}(T,\Lambda)$ and $Rf_!K\in D^b_{ctf}(B,\Lambda)$: at finite coefficients these are precisely clauses (i), (iv) of [thm-sf-ctf-stability]; at the integral and field stages the datum supplies the operations on the stated finite-Tor categories, with the coefficient-passage conventions of that stability statement. No exceptional-image or duality clause of stability is used. Clause (ii) of [thm-sf-ctf-stability] also puts the exterior tensor input in the finite-Tor category. For the finite witnessed composition and the concrete exchange-pasting statements used below, [lem-sf-proetale-constructible-origin](ii) supplies an etale-origin witness for each bounded constructible finite-coefficient input. At the integral stage apply this to every constructible finite reduction in the specified derived-complete construction; at the rational and algebraically closed stages use the integral presentation and a common finite coefficient stage. These are the completed and transported domains of [fix-lem-exchanges], not discrete non-torsion etale coefficient categories.

Existing nodes used: `def-sf-datum`, `thm-sf-ctf-stability`, `lem-pod-separated-finite-type-base-change`, `def-weil-finite-type-morphism`, `def-weil-proper-morphism`, `lem-weil-pbc-closed-immersion-base-change`, `lem-weil-pbc-closed-immersion-comp`, `lem-sf-proetale-constructible-origin`, `fix-lem-exchanges`.

Source: `literature/blueprint/master/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/_section.md`, Proof, typing before (1) and the explanation after (4).

### Returned step 2

Apply the inverse composition isomorphism of (A4) at $L\pi_X^*K\otimes^L_\Lambda L\pi_Y^*L$. Its source is $Rh_!(K\boxtimes L)$ and its target is $Rg_!R\pi_{Y!}(L\pi_X^*K\otimes^L_\Lambda L\pi_Y^*L)$. At the finite witnessed pro-etale level this is the canonical $\alpha_{g,\pi_Y}^{-1}$ of [thm-sf-comp-composition]; at other stages use its supplied composition isomorphism (A4).

Existing nodes used: `def-sf-datum`, `thm-sf-comp-composition`.

Source: `literature/blueprint/master/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/_section.md`, Proof, (1).

### Returned step 3

The inverse projection transformation $\operatorname{PF}_{\pi_Y,L\pi_X^*K,L}^{-1}$ sends $R\pi_{Y!}(L\pi_X^*K\otimes^L_\Lambda L\pi_Y^*L)$ to $R\pi_{Y!}L\pi_X^*K\otimes^L_\Lambda L$. Its type is exactly [def-sf-pf], and its invertibility is (A3), concretely the all-coefficient projection formula [fix-prop-projection-formula]. Apply $Rg_!$ to this inverse. No symmetry is inserted at this step.

Existing nodes used: `def-sf-pf`, `def-sf-datum`, `fix-prop-projection-formula`.

Source: `literature/blueprint/master/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/_section.md`, Proof, (2).

### Returned step 4

The Cartesian square $T\xrightarrow{\pi_X}X$, $T\xrightarrow{\pi_Y}Y$, $X\xrightarrow{f}B$, $Y\xrightarrow{g}B$ has exchange $\operatorname{Ex}_!:Lg^*Rf_!K\xrightarrow{\sim}R\pi_{Y!}L\pi_X^*K$ by (A2). Tensor its inverse with $1_L$ and apply $Rg_!$. This gives $Rg_!(Lg^*Rf_!K\otimes^L_\Lambda L)$. Tensor symmetry then gives $Rg_!(L\otimes^L_\Lambda Lg^*Rf_!K)$.

Existing nodes used: `def-sf-datum`.

Source: `literature/blueprint/master/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/_section.md`, Proof, (3).

### Returned step 5

Apply $\operatorname{PF}_{g,L,Rf_!K}^{-1}$ to the preceding object. Step 1 checked its second variable is in the finite-Tor domain. This gives $Rg_!L\otimes^L_\Lambda Rf_!K$, and tensor symmetry gives $Rf_!K\otimes^L_\Lambda Rg_!L$. We have used exactly the arrows defining the canonical map in the statement. Each is an isomorphism, so their composite is an isomorphism.

Existing nodes used: `def-sf-pf`, `def-sf-datum`, `fix-prop-projection-formula`.

Source: `literature/blueprint/master/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/_section.md`, Proof, (4).

### Returned step 6

Each factor is natural in both inputs: the composition and exchange are natural transformations and the two projection maps are natural by [fix-prop-projection-formula] and [prop-sf-pf-coherence]. The inverse of an invertible natural transformation is natural, and tensoring and applying a functor preserve naturality, so their composite is natural. The coefficient comparison squares for its factors commute by (A5) and projection coherence; composing these squares proves finite-reduction and scalar-extension compatibility. For proper morphisms replace $R(-)_!$ by $R(-)_*$ through the (A4) identification; projection coherence identifies the projection factor with the direct-image factor and (A5) identifies the remaining coefficient comparisons, giving the asserted proper identification. At finite coefficients [cor-cbc-proper-coincidence] says exactly that the compact-support exchange under the canonical proper identification is the proper-base-change exchange; at higher stages use its coefficient-passage compatibility supplied by (A5). Thus the proper comparison is also the specified exchange comparison, not an arbitrary isomorphism between the two functors.

Existing nodes used: `def-sf-datum`, `fix-prop-projection-formula`, `prop-sf-pf-coherence`, `cor-cbc-proper-coincidence`.

Source: `literature/blueprint/master/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/_section.md`, Proof, naturality and coefficient/proper compatibility.

### Returned step 7

Let $b:B'\to B$ be a morphism of separated finite-type $k$-schemes, and use primes for all its base changes, with $v:Y'\to Y$, $u:X'\to X$, and $w:T'\to T$. Use the monoidal pullback comparison to identify $Lw^*(K\boxtimes L)$ with $Lu^*K\boxtimes Lv^*L$. The exchange pasting equations of [fix-lem-exchanges] identify the square for $Lb^*\alpha_{g,\pi_Y}^{-1}$ with that for $\alpha_{g',\pi_Y'}^{-1}$. The base-change square of [prop-sf-pf-coherence] for $\pi_Y$ along $v$, read backwards, identifies the inverse first projection factors. The exchange pasting equations identify the exchanged $R\pi_{Y!}L\pi_X^*K$ factors. The same projection-coherence square for $g$ along $b$, again read backwards, identifies the final inverse projection factors. Naturality of tensor symmetry and the monoidal pullback comparison identifies the two symmetry factors. Compose these commuting squares in the order of steps 2--5: the result is exactly the square comparing $Lb^*$ of the stated composite to the composite for $(f',g',Lu^*K,Lv^*L)$ through the exchanges for $f,g,h$. This proves the claimed base-change compatibility without invoking the later relative-product coherence lemma.

Existing nodes used: `fix-lem-exchanges`, `prop-sf-pf-coherence`, `lem-pur-derived-pullback-tensor-iso`.

Source: `literature/blueprint/master/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/_section.md`, Proof, coherence (iii), explicitly described after (4).

### Returned step 8

Put $B=s=\operatorname{Spec}k$ and let $i_Z:Z\hookrightarrow X$, $i_W:W\hookrightarrow Y$ be closed immersions. The closed-immersion properness statement makes $i_Z,i_W$ separated of finite type, and the composition argument of step 1 makes their structure maps separated of finite type, and pullback stability puts $Li_Z^*K,Li_W^*L$ in the finite-Tor domains. Apply the construction of steps 1--5 to these two schemes. If $r:Z\times_kW\to X\times_kY$ is the product immersion, with projections $\pi'_X,\pi'_Y$, monoidality and pullback composition give
$$Lr^*(L\pi_X^*K\otimes^L L\pi_Y^*L)\cong L(\pi_X r)^*K\otimes^L L(\pi_Y r)^*L
\cong L\pi'_X^*Li_Z^*K\otimes^L L\pi'_Y^*Li_W^*L,$$
since $\pi_X r=i_Z\pi'_X$ and $\pi_Y r=i_W\pi'_Y$. Thus the input is precisely $r^*(K\boxtimes L)$, rather than an extraordinary restriction or a supported complex.

Existing nodes used: `thm-sf-ctf-stability`, `def-weil-closed-immersion`, `lem-pur-derived-pullback-tensor-iso`, `lem-weil-pbc-closed-immersion-proper`.

Source: `literature/blueprint/master/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/_section.md`, Proof, compact-support specialization.

### Returned step 9

Invert that specialized isomorphism and apply $\operatorname{Fib}_s$. By [def-weil-ordinary-compact-cohomology], the three compact-support direct images become the corresponding $R\Gamma_c$ complexes. The canonical tensor comparison of [lem-sf-point-fibre-derived-tensor] identifies the fibre of the tensor product with the tensor product of the two fibres. The resulting isomorphism is exactly the displayed closed-subscheme compact-support product formula. This argument uses restrictions $Li_Z^*,Li_W^*$; it makes no assertion about the distinct cohomology-with-support functor of [def-pur-support-cohomology].

Existing nodes used: `def-weil-ordinary-compact-cohomology`, `lem-sf-point-fibre-derived-tensor`, `def-pur-support-cohomology`.

Source: `literature/blueprint/master/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/_section.md`, Proof, final compact-support display.

