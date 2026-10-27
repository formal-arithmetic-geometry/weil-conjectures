# Repair report for lem-trf-point-transport-cone-comparison-descent

## Files written

- dag/nodes/sec-trace-formula/lem-trf-point-transport-cone-comparison-descent.json: item, split; statement unchanged; short assembly.
- dag/nodes/sec-trace-formula/lem-trf-point-cone-lifts-chain-naturality.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-point-transport-resolution-cancellation.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-point-pullback-cone-localization.json: statement, unsplit; no Mathlib match.
- citations.json: one verbatim statement quotation per node used in each assembly step.

## Attachments

None. The exact blueprint-tag and notion search in lean/WeilConjectures found no finished project declaration. Read lean/Sheaf/Paper/PointTransportConeComparisonDescent.lean: augmentation_condition (line 136), pointTransportConeComparison (line 209), pullbackRoof_isIso (line 245), and pointTransportConeComparisonDescent (line 280) all contain sorry. They cannot justify ATTACH. No Lean was changed and no compiler was run.

## WANTED

None. The source blueprint, Stacks source and pinned Mathlib source are available locally.

## What was wrong and what changed

The return requests distribution of a 5849-character proof into at least two new statement-only jobs with a parent assembly of at most 3000 characters. The sandbox initially held only dispatcher marker files: no node, report, citations or earlier searches. I copied the current repository item rather than inventing a lost sandbox head; its eight proof texts have exactly the lengths in the return. The current main copy is therefore the repair baseline, including all its source, Lean and review metadata and prior Mathlib searches, retained unchanged. No git command was used in the shared repository.

Three new nodes separate the chain construction, resolution comparison, and localization arguments. The second deliberately uses the resolution-indexed comparison iota_(N,q), so it does not presume the independence that the third node and the assembly establish. The statement of the parent remains byte-for-byte equal as a parsed string to the repository statement. New nodes have no proof, proof dependencies or proof sketch; the arguments for their future workers are retained below.

## What remains

The three new statements are unsplit jobs for parallel future workers; their proofs are not claimed finished. This delivery repairs only stage 1.

## Allocation of the returned proof

- Old steps 1 and 6 belong to lem-trf-point-cone-lifts-chain-naturality: strict reduction and theta compatibility, chain-map lifts, and both chain naturality equations.
- Old step 2 belongs to lem-trf-point-cone-lifts-chain-naturality: diagonal strict-tower cone action and the natural two-coordinate c_X comparison. Its c_X object is reused from def-trf-point-sections-roos-comparison, not newly defined.
- Old step 3 is kept explicitly in assembly step 2. The chain maps and coordinates it uses are supplied by lem-trf-point-cone-lifts-chain-naturality.
- Old step 4 and the comparison/cancellation argument of old step 5 belong to lem-trf-point-transport-resolution-cancellation. The substitution of the strict equality is the short assembly step 3.
- Old steps 7 and 8 belong to lem-trf-point-pullback-cone-localization: both functors factor through homotopy and invert good quasi-isomorphisms, localization extends a natural family, the roof algebra is valid, and all representatives give the same component under b_q. Identification of this descended component with the actual point transport is assembly step 5 using lem-trf-point-transport-resolution-cancellation.

The three proof responsibilities contain respectively 2021, 1317 and 2000 characters of the old argument before overlap/assembly (the exact texts below are authoritative). They are separate arguments of comparable scale; none states the whole item.

## Not duplicates

lem-trf-point-cone-lifts-chain-naturality vs lem-trf-point-sections-completion-cone: the latter gives c_X and completeness isomorphisms; the new node gives the simultaneous reduction/theta lifts and their chain naturality with arbitrary chain-natural u, without completeness. Its c_X clause is ancillary reuse, not a new standalone product-comparison node.
lem-trf-point-cone-lifts-chain-naturality vs def-trf-point-sections-roos-comparison: the existing node defines the normalized c_X; the new statement supplies naturality with strict maps together with the reduction and theta lift identities.
lem-trf-point-cone-lifts-chain-naturality vs lem-trf-completion-unit-strict-quotient-model: that identifies a completion adjunction unit, but does not give the point-section theta lift and its simultaneous chain-map identities.
lem-trf-point-cone-lifts-chain-naturality vs lem-trf-point-transport-strict-quotient: that constructs one particular u(P); the new statement concerns the cone lifts and their naturality for any strict chain-natural family u.
lem-trf-point-transport-resolution-cancellation vs def-weil-inverse-image-pullback-comparison: comparison (b) specifies a sheaf-derived map using fixed resolutions; the new statement calculates its point-section representative with sigma and exact sections, indexed by the resolution, without asserting independence.
lem-trf-point-transport-resolution-cancellation vs lem-weil-frobenius-point-transport-natural: clause (1) gives sigma naturality, but not its combination with the normalized completed-pullback cone and b_q. Clause (2) is restricted to constructible objects, whereas the new calculation is ambient.
lem-trf-point-pullback-cone-localization vs lem-weil-pbc-site-derived-tensor-descent: that gives the generic resolving-class localization equivalence and tensor descent, not invariance and the specified representative comparison for point sections of completed-pullback cones.
lem-trf-point-pullback-cone-localization vs lem-weil-pbc-localization-universal-property: that generic Mathlib leaf assumes a localization and lifted functors; the new result verifies the particular S,T functors and identifies the descent under b_q on arbitrary resolutions.
lem-trf-point-pullback-cone-localization vs lem-pur-integral-operations-well-defined: that descends completed sheaf operations, not an arbitrary point-section natural family with its explicit roof and resolution formulas.
lem-trf-point-pullback-cone-localization vs lem-trf-isomorphism-multiplication-cone-descent: that identifies completed pullback with inverse image of a completion by multiplication; the new result descends arbitrary S-to-T families and never introduces the multiplication comparison.
lem-trf-point-pullback-cone-localization vs lem-trf-point-system-roos-transport: that works on the derived category of strict coefficient systems and a specified point-system transport; the new result starts from the resolving class of ambient R-module complexes and an arbitrary natural family.
All three vs lem-trf-point-transport-cone-comparison-descent: strict chain infrastructure, resolution-indexed cancellation without u, and localization of arbitrary eta are each strictly smaller; none asserts both the actual comparison with H(u)a and its derived independence.

## Searches and sources read

Searched the whole DAG and lean/WeilConjectures by blueprint tag, point/cone, reduction-unit, theta, naturality and localization concepts. Searched the entire blueprint with tools/blueprint_refs.py (ancestor plus point transport, cone, comparison, K-flat, cone comparison, Roos, zero shifted, quasi-isomorphism roofs). Read the close existing statements listed in Not duplicates and the original parent realization. No blueprint node states one of the new statements. The ancestor is prop-trf-rational-frobenius-integral-model with via [this item, lem-trf-integral-point-transport-tower-realization].

All new-node Mathlib queries were run with the required msearch.py and read, including second phrasings; searches.jsonl is the actual tool log. The unavailable first LeanSearch call was retained as unavailable, and a later retry succeeded. Read MappingCocone.lean lines 275-307: lift gives the generic cone constructor and component rules, not the simultaneous quotient/theta naturality. Read Localization/Predicate.lean lines 300-360: liftNatTrans is the generic localization tool already present as lem-weil-pbc-localization-universal-property. It does not establish that these particular completed-pullback cone functors invert good quasi-isomorphisms. No new node is a one-line specialization of those hits.

For the item and all three children read blueprint main-20261015 prop-trf-rational-frobenius-integral-model.proof.md clause (3): realization of the whole reduction tower is the integral map. The actual explicit supplemental argument is agent-written, as recorded already by the parent, not falsely attributed verbatim to the blueprint. For the chain-construction child also read the full statement of comparison (b), which specifies theta, strict quotient transitions, the signed cone differential and its zero shifted lift, and the point-sections Roos definition. For the cancellation child read sigma clause (1) of lem-weil-frobenius-point-transport-natural, exact point sections, comparison (b), and ambient completed operations; these support exactness and the cancellation without invoking constructible-only naturality clause (2). For the localization child read the full statements of site-derived-tensor-descent, operations-well-defined (1),(2), and localization-universal-property (2),(3). Read Stacks Tags 06YS (sites-cohomology lemma-K-flat-resolution), 0G7D (lemma-factor-through-K-flat), and 06YU (definition-derived-tor) in sites-cohomology.tex for the resolving-class background; these do not individually assert the new specialized result. No SGA source is used.

## Review by Q134

I checked the three new statements in their written forms, and compared each assembly citation with its actual statement, not its proof. Step 1 uses the first child's strict transition equalities, chain-map lifts, diagonal H(f) action and natural c_X; all are explicitly conclusions there. Step 2 uses only these already established formulas and the parent's given augmentation equality, and writes both coordinates. Step 3 uses exactly the second child's displayed b_q iota_(N,q) formula and its preceding sigma/quasi-isomorphism conclusions; substituting the chain equality gives both requested identities by right-composition with the invertible Gamma(q). Step 4 takes exactly the final sentence of the first child, with the assumed naturality of u; no chain lift between arbitrary chosen resolutions is assumed. Step 5 uses the third child's quantified natural-family extension, every-q component formula and roof equation, and uses the second child to identify the component on chosen resolutions with the actual defining iota. The second child's equation then identifies its recipe on every other resolution with the same expression from the third child. This repairs the ordering advisory in the old review: representative independence is established by localization before claiming all recipes agree. citations.json quotes are literal substrings of these statements.

Hypotheses: k is algebraically closed, so exact point sections apply to all R-module complexes; the sites use the fixed small skeleton/module universes required by site-derived-tensor-descent. g is an isomorphism and completed scalars are transported through its structure isomorphism, so g^(-1) is exact. P, Q and P' are flat-term K-flat whenever operation invariance is invoked. Arbitrary N is allowed by the ambient completed pullback, rather than a constructible-only restriction. The natural family in the third child consists of derived morphisms natural for every chain map, so passage to the homotopy quotient is justified and does not demand strict chain choices for arbitrary derived maps.

Small cases: P=0 gives zero lifts and zero eta; q an identity makes the cancellation formula the strict comparison after localization; P=R in degree zero retains an exactly zero shifted-product augmentation. For P=R[1/varpi] in degree zero every quotient P_n is zero, so the augmentation into its cone is zero and need not be invertible. This checks that neither the cancellation child nor the localization child accidentally assumes derived completeness. For an identity roof the displayed square reduces to eta=eta; for b=0 it reduces to zero=zero. Strict maps with nonzero shifted input are sent diagonally, so the claims do not silently ignore that coordinate.

Reviewed B1-B10: children are self-contained statement-only, notions have their actual defining nodes or inline formulas, TeX is written once, sources specify the blueprint passage and actual Stacks labels when discussed, searches are real with unavailable recorded accurately, normalized blueprint ancestry is complete, and all located Lean theorem candidates remain sorried. Reviewed C1-C8: assembly has exactly three cited arguments, verbatim quotes, no hidden non-elementary step, proof_deps is their union, no new off-unit proof edge, and the new nodes do not depend on the item. Reviewed D1-D5 against the explicit re-split direction: separate strict, representative, and localization jobs retain every old argument below, with the coordinate substitution still visible in the assembly. Reviewed E1-E7: hypothesis and variance checks above; statement unchanged; no new source dispute found. No proof step exceeds 2000 characters; total parent proof is 1980 characters.

## Original returned proof retained verbatim

### Original step 1

Write $r=(r_n)_n$ and $\theta=(\theta_n)_n$. The reductions satisfy $t_nr_{n+1}=r_n$: on a tensor generator this says that reducing $x\otimes1$ once more gives $x\otimes1$. Part (b) of [def-weil-inverse-image-pullback-comparison] gives $v_n\theta_{n+1}=\theta_n$ and that every $\theta_n$ is a chain map over the completed coefficient sheaf. Thus $(1-s_D)\Gamma(r)=0$ and $(1-s_C)\theta=0$. With the displayed differential, $d(0,\theta(w))=(0,\theta(dw))$ and $d(0,\Gamma(r)z)=(0,\Gamma(r)dz)$. Consequently both specified zero-first-component lifts are chain maps; this uses equality in the strict towers before localization.

Uses: def-weil-inverse-image-pullback-comparison.

### Original step 2

For a strict tower map $f:X_\bullet\to Y_\bullet$ define $U_f((x_n))=(f_nx_n)$. Strictness gives $(1-s_Y)U_f=U_f(1-s_X)$, so $H(f)(b,a)=(U_fb,U_fa)$ commutes with $d(b,a)=(-db-(1-s_X)a,da)$. In particular this specifies $H(u)$ on both products. By [lem-weil-proetale-countable-products-exact], evaluation of the sheaf products is the product of the evaluations. Sections are additive and exact by [lem-weil-point-proetale-sections-exact], so they identify the finite direct sum and both differentials as well. Hence $c_C$ is a chain isomorphism, identity on the two products, and for every strict map of sheaf towers $f$ it satisfies $c_{C'}\Gamma H(f)=H(\Gamma f)c_C$.

Uses: lem-weil-proetale-countable-products-exact, lem-weil-point-proetale-sections-exact.

### Original step 3

Evaluate the left side of the claimed strict equality on $z\in\Gamma(P)^i$. By the definitions of the lifts and of $c_C$, it is $(0,(\Gamma(\theta_n)\sigma_Pz)_n)$. The assumed augmentation equations identify this with $(0,(u_n\Gamma(r_n)z)_n)$. The diagonal formula in step 2 identifies the latter with $H(u)a_P(z)$. The first product component in degree $i-1$ is zero on both sides, not merely invisible under projection to a finite level. Equality degree by degree proves the asserted equality of chain maps.

Uses: .

### Original step 4

Clause (1) of [lem-weil-frobenius-point-transport-natural] applies to every complex of integral coefficient modules, without constructibility or completeness. For the chain map $q:P\to N$ it gives $\sigma_N\Gamma(q)=\Gamma(g^{-1}q)\sigma_P$. By [lem-weil-point-proetale-sections-exact], $\Gamma(q)$ is a quasi-isomorphism. The transported module inverse image in [def-weil-inverse-image-pullback-comparison] preserves quasi-isomorphisms, so $\Gamma(g^{-1}q)$ is one too. Their classes are therefore invertible in the derived category.

Uses: lem-weil-frobenius-point-transport-natural, lem-weil-point-proetale-sections-exact, def-weil-inverse-image-pullback-comparison.

### Original step 5

The ambient operation of [def-pur-integral-derived-operations] is represented on $q:P\to N$ by $H(C_\bullet)$. Its functorial representative comparisons and their independence are supplied by [lem-pur-integral-operations-well-defined](2). Composing that comparison with $c_C$ defines the asserted $b_q$. Under it, part (b) of [def-weil-inverse-image-pullback-comparison] gives $\Gamma(\kappa_N)=[\Gamma\widetilde\theta_P][\Gamma(g^{-1}q)]^{-1}$. Combine this formula with step 4 and then step 3:
$$b_q\iota_N[\Gamma(q)]=[c_C\Gamma\widetilde\theta_P][\Gamma(g^{-1}q)]^{-1}\sigma_N[\Gamma(q)]=[c_C\Gamma\widetilde\theta_P]\sigma_P=[H(u)a_P].$$
Right-compose with $[\Gamma(q)]^{-1}$ for the second displayed identity. At this point only the resolution maps and $c_C$ have been inverted.

Uses: def-pur-integral-derived-operations, lem-pur-integral-operations-well-defined, def-weil-inverse-image-pullback-comparison.

### Original step 6

Assume now the stated chain naturality of $u(P)$. For a chain map $h:P\to P'$ in the resolving class write $h_D,h_B,h_C$ for its induced tower maps. Reduction gives $\Gamma(h_n)\Gamma(r_n)=\Gamma(r'_n)\Gamma(h)$, since both maps send $x$ to $h(x)\otimes1$. Similarly, the finite comparison $x\mapsto x\otimes1$ in [def-weil-inverse-image-pullback-comparison](a) gives $h_{C,n}\theta_n=\theta'_ng^{-1}h$. Thus $H(h_D)a_P=a_{P'}\Gamma(h)$, and $H(h_C)\widetilde\theta_P=\widetilde\theta_{P'}g^{-1}h$, including zero first components. By the assumption $h_Bu(P)=u(P')h_D$ and the diagonal formula, putting $\eta_P=[H(u(P))a_P]$ gives $[H(h_B)]\eta_P=\eta_{P'}[\Gamma(h)]$. The maps $c_C$ commute with these comparisons by step 2.

Uses: def-weil-inverse-image-pullback-comparison.

### Original step 7

Use the small-site and module-universe convention of [def-weil-pbc-proetale-site]. By [lem-weil-pbc-site-derived-tensor-descent], localization of the homotopy category of flat-term K-flat module complexes at its quasi-isomorphisms is equivalent to the ambient $D(R)$. The source functor on this class is $P\mapsto\Gamma P$; its homotopy and quasi-isomorphism invariance follows from exact sections [lem-weil-point-proetale-sections-exact]. The target functor is $P\mapsto\Gamma H(C(P))$, identified with $H(B(P))$ by $c_C$. Its factorization through the derived category, quasi-isomorphism invariance and specified natural representative comparisons are exactly [lem-pur-integral-operations-well-defined](1),(2), followed by exact sections. Therefore the chain naturality equations of step 6 are also equations in the homotopy category. Apply [lem-weil-pbc-localization-universal-property](2),(3), with these two functors and the resolving-class localization, to extend $\eta$ uniquely to a natural transformation of the ambient derived functors. This uses the equivalence for all flat-term K-flat objects, rather than assuming a chain lift between two arbitrarily chosen resolutions.

Uses: def-weil-pbc-proetale-site, lem-weil-pbc-site-derived-tensor-descent, lem-weil-point-proetale-sections-exact, lem-pur-integral-operations-well-defined, lem-weil-pbc-localization-universal-property.

### Original step 8

Explicitly, for the stated roof put $S(h)=[\Gamma(h)]$ and $T(h)=[H(h_B)]$. Both $S(a)$ and $T(a)$ are invertible by step 7. Naturality for $a:Q\to P$ gives $T(a)^{-1}\eta_P=\eta_QS(a)^{-1}$. Hence
$$T(b)T(a)^{-1}\eta_P=T(b)\eta_QS(a)^{-1}=\eta_{P'}S(b)S(a)^{-1}.$$
This is the required square for $[b][a]^{-1}$, and step 7 ensures independence of its presentation. For a representative $q:P\to N$, the descended component, expressed using $b_q$, is $\eta_P[\Gamma(q)]^{-1}$ by naturality. Step 5 identifies this with the specified $\iota_N$. Uniqueness of the descent and the specified target comparisons then identify the expressions from any two representatives. The strict equality in step 3 and its derived versions therefore describe the same natural map. No step inverted $a_P$ or invoked completeness of $N$.

Uses: .
