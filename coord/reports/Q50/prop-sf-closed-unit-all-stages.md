# Stage-1 repair: prop-sf-closed-unit-all-stages

## Files written

- `dag/nodes/sec-smooth-purity/prop-sf-closed-unit-all-stages.json`: existing statement unchanged, six-step assembly of 2474 characters, replacing the returned 13172-character proof.
- `lem-sf-direct-image-reduction-hom-square`: statement, unsplit; no Mathlib match. Separates normalization of the reduction-unit/Hom square from any full-faithfulness conclusion.
- `lem-sf-roos-hom-bijection-lifting`: statement, unsplit; no Mathlib match. An abstract Hom comparison for a specified Roos triangle; no coefficient category or closed-immersion conclusion in its statement.
- `lem-sf-strict-direct-image-scalar-comparison`: statement, unsplit; no Mathlib match. Linearity and coherent scalar comparisons of the actual strict-tower functor, without a full-faithfulness assertion.
- `lem-sf-common-stage-full-faithfulness`: statement, unsplit; no Mathlib match. Coherent families with fully faithful components, without an essential-surjectivity assumption, induce a fully faithful functor on literal common-stage categories.

All four new files lie in the same `dag/nodes/sec-smooth-purity/` directory. They carry source, complete standalone statements, empty proof/proof_deps, null proof_origin, status unsplit, chapter/unit, blueprint.from and same_as. They are separate work packets for subsequent workers, not proofs relabelled as one replacement proposition. Their statement sizes are 2238, 1603, 2888 and 1870 characters. Mathlib leaves added: 0. Neither Lean nor any repository/launcher file was written. Sandbox-only search transcripts and the unchanged old proof are retained.

## Attachments

None. I searched `lean/WeilConjectures/` for the item id and the closed/full-faithfulness notions. `WeilConjectures/SixFunctors/ClosedImmersionStages.lean` contains partial results, but its integral model is the ordinary etale constant-coefficient derived-complete model, and its algebraically closed model is the ordinary pro-etale module category over WeilCoefficients. Its bounded rational variant also adds a Karoubi envelope. These do not state every clause for the specified completed pro-etale integral category, raw rationalization, and common-stage pair category of this item, including preservation. The item’s recorded `Sheaf/SecSmoothPurity/ClosedUnitAllStages.lean` theorem itself ends in sorry. New-node source searches found no finished project declaration of the normalized Hom square, the abstract Roos comparison, or the specified direct-image/scalar package. StageSystem/Restrict proves only the full-subcategory inclusion case, not the arbitrary coherent family of the common-stage node.

## WANTED

None for this repair. All four extracted statements have the current blueprint proof as their agent-written source. No unavailable source or SGA route is substituted.

## What was wrong and what changed

The return is about work distribution: eleven individually reasonable arguments left 13172 characters in a single node. I replaced this with four independently statable intermediate arguments and reused existing statements for finite exactness/constructibility and normalized completed reconstruction. The item statement, coefficient categories, geometric hypotheses, chapter/unit, existing Lean record and imported metadata stay unchanged.

A fourth new node is not manufactured from finite constructibility: `lem-sf-finite-immersion-constructibility-interval` already states the exact stratification and unchanged-amplitude argument. Likewise `lem-pur-completed-coefficient-pushforward-comparison` already states the strict-diagram normalized comparison and every projection, so creating another reconstruction-specialization node would duplicate it. These existing nodes retain the relevant arguments and are cited directly. The four new nodes instead expose the remaining Hom normalization, triangle-to-Hom lifting, strict/ambient scalar comparison, and coherent common-stage inversion. The report below preserves the old proof verbatim and maps every argument to its owner; no argument is replaced by “standard”, “transport”, or “colimits preserve bijections” without its precise statement.

## Not duplicates

lem-sf-direct-image-reduction-hom-square vs lem-weil-derived-scalar-extension-restriction-adjunction: the existing statement supplies the two separate scalar adjunctions and units, but not their direct-image comparison square or compatibility with quotient transition maps.

lem-sf-direct-image-reduction-hom-square vs lem-pur-completed-coefficient-pushforward-comparison: the existing statement gives the canonical coefficient comparison and reconstruction projections, but not the scalar-adjunction transpose equation with the actual finite-reduction mate.

lem-sf-direct-image-reduction-hom-square vs lem-sf-generator-reduction-coherence: that system-generator theorem requires normalized etale-origin systems with uniform finite Tor bounds. The new external-Hom square allows an arbitrary target finite derived complex and requires no finite Tor amplitude on P or Q.

lem-sf-direct-image-reduction-hom-square vs def-sf-integral-hom-reduction-comparison: that node defines a derived internal-Hom comparison on one site, not the external-Hom map between two sites under direct image.

lem-sf-roos-hom-bijection-lifting vs prop-weil-pbc-roos-triangle: the existing statement constructs a Roos triangle and Milnor cohomology sequence, not the relative Hom-bijection criterion for an exact functor.

lem-sf-roos-hom-bijection-lifting vs lem-weil-pbc-hom-into-triangle-exact: this gives exactness of one Hom row; the new statement compares rows in two categories using all shifted tower-term bijections and the canonical product comparison.

lem-sf-roos-hom-bijection-lifting vs lem-sf-integral-hom-roos-transport: that theorem proves completeness of a derived internal Hom on a single ringed site; it does not compare external Hom groups under a functor between categories.

lem-sf-strict-direct-image-scalar-comparison vs prop-weil-pbc-scalar-extension: the ambient comparison in the existing statement is for ordinary completed-ring direct image and its constructible restriction; the new node fixes its comparison to the specified strict-reduction-tower I_E functor, completed scalar extension, and the actual rational associator cocycle. This is the model/normalization comparison, not a second ambient projection formula.

lem-sf-strict-direct-image-scalar-comparison vs lem-pur-integral-operations-scalar-extension: that node covers pullback, completed tensor, and internal Hom, not the specified strict-tower direct image.

lem-sf-strict-direct-image-scalar-comparison vs lem-sf-rational-direct-image-coefficient-compatibility: despite its title, the latter fixes the rational PULLBACK family and asserts invertibility of its right-adjoint mates; it does not identify the prescribed strict direct-image family with ordinary completed-ring direct image.

lem-sf-common-stage-full-faithfulness vs prop-weil-pbc-descent-functors: the existing node constructs descent of exact coherent families and transformations; it does not prove full faithfulness from fully faithful components.

lem-sf-common-stage-full-faithfulness vs lem-fd-common-stage-comparison-descent: that theorem assumes stagewise equivalences between two coefficient frameworks and constructs equivalences. Our components need only be fully faithful, not essentially surjective, and both systems are the original common-stage categories on two schemes.

lem-sf-common-stage-full-faithfulness vs prop-sf-closed-unit-all-stages: the new statement is conditional on an arbitrary coherent family already being fully faithful stagewise, and contains no assertion about any direct image or exceptional adjoint. It proves only the categorical passage needed after the integral/rational geometric arguments.

These comparisons followed whole-DAG key-word searches, blueprint_refs searches for Roos, Hom comparison, full faithfulness, closed immersion, scalar extension, reduction adjunction, scalar direct image and common-stage, and source searches. No new source carries a Stacks tag already used by an existing node: the sources are explicitly extracted arguments of the current blueprint proof, not mislabeled single Stacks lemmas.

## Review by Q50

I read the current main-20261015 item statement and its full finite/integral/rational/algebraically-closed/unit proof, the chapter and unit records, the old eleven-step DAG proof, and the B–E delivery errors in both copies. The global unit route remains finite closed full faithfulness followed by the exceptional adjunction unit. Its historical SGA pointer is not used. I also read Stacks proetale.tex lemma-closed-immersion (09AA) and lemma-closed-immersion-complement-retrocompact-exact (09BM), sites-cohomology.tex lemma-derived-pushforward-composition (0D6E) and lemma-Rf-commutes-with-Rlim (0A07), and proetale.tex lemma-pushforward-Noetherian-case (099N), checking their actual hypotheses and the distinction between constant and completed coefficients. The generic comparison nodes, not the constant-coefficient Stacks assertion alone, are what give the completed version.

For the Hom-square node I used the integral paragraph and old step 6 as source. Its normalization is an equality of actual maps: the transpose of u is Res(u)c_P, and the projection-formula mate is characterized by the scalar unit equation. Applying F, then the coefficient-composition comparison, gives Res(F_n(u) beta_P)c_FP. Naturality in the finite target and the strict quotient compatibility of alpha supply transition compatibility. This does not assert that restriction of scalars is fully faithful. The objects, ring sheaves, projections, derived categories, units, beta and alpha are all introduced in its statement. The old step 4 coefficient comparison and step 5 actual projections are retained in the existing completed-comparison statement; the new lemma asks for the additional Hom/transpose normalization, not an arbitrary reduction isomorphism.

For the Roos node I used the same integral paragraph and old step 7, and checked the 0A07 product argument. All countable products involved are assumed to exist, the product comparison is specifically characterized by projections, and the entire image triangle including the connecting arrow is specified. The map on Hom into B is the coordinatewise bijection. With A_m=Hom(P[m],B), Hom exactness for the triangle and its rotations gives 0 -> coker(1-s on A_1) -> Hom(P,Q) -> ker(1-s on A_0) -> 0. The two rows commute because F and its actual triangle comparison induce them. Injectivity and surjectivity on the outside give the middle bijection by the diagram chase preserved below. The original coker index 1 is correct: Hom(P,B[-1])=Hom(P[1],B). This lemma is not an ordinary categorical-limit preservation claim; it imposes no unjustified lim^1 vanishing.

For the scalar node I used the rational paragraph and the first half of the algebraically closed paragraph, together with old steps 4–5, 8 and 9. The schemes here are finite type over a field, hence Noetherian and finite-dimensional (lem-kun-dimension-finite-type); the prime is invertible. The identity case of the finite-free comparison gives the actual completion unit, and the constant/completed equivalence is unit-compatible, so the ambient completeness premise in prop-weil-pbc-scalar-extension is satisfied. The existing integral-constructibility theorem gives I_E and its finite reductions in the stated categories. Normalize psi by the strict reduction projections; compose its two occurrences with chi and the inverse ambient scalar mate. This comparison has direction I_L T_Z -> T_X I_E. The scalar equation in the statement starts at I_M T^Z_{M/L} T^Z_{L/E} K and ends at T^X_{M/E} I_E K on both sides. Its proof task includes checking the completion/finite-free normalizations in the identity and successive-extension cases; mere unrelated objectwise isomorphisms would not suffice. Constant R_E scalars commute with finite direct image, strict tower maps and derived inverse limit, so I_E is linear and psi respects scalars. Neither full faithfulness nor a choice of replacement functor is in this node's hypotheses or conclusion.

For the common-stage node I used the algebraically closed paragraph and the second half of old step 9. I checked the literal definition of pair objects and common-stage representative equality and the associator transport, rather than identifying this with ordinary sheaves of Omega-modules. The new statement explicitly introduces its arbitrary family Phi_E and its comparisons; none is presumed to be a direct image. Its coherence equation is typed in the same orientation as the scalar node. Conjugation by theta and stagewise full faithfulness give b_L; the cocycle makes it commute with further extension. For a target representative v at L choose b_L inverse at that same stage. Equality after extension to M gives equality of inverse representatives by injectivity of b_M. Both composites are identities on a representative. This is also why no full-faithfulness assumption on extension of scalars is needed. Functoriality follows by composing at one common stage and cancelling the middle theta pair; normalization handles identities.

I checked each assembly citation by reading its statement, and put verbatim passages in citations.json:

1. Finite-type-over-Noetherian and the Noetherian-open lemma give exactly the two scheme and complement checks. The closed-immersion-properties lemma gives finite, separated, universally closed. The two compact-support definitions give the identity compactification at finite level and the same specified tower/rational/common-stage formulas thereafter. Finite implies finite type here directly from a finite module generating set (for a quotient algebra, 1 generates it). A field is Noetherian by its two ideals and its spectrum is quasi-compact.
2. The recollement node gives the ambient counit, and the counit criterion gives ambient full faithfulness. The finite-immersion-interval statement gives precisely the strata and cohomology formula, not just a definition of constructibility. I additionally cited the closed exactness and exact-functor factorization statements so that identification of termwise i_* with the ambient derived functor is supported on every ambient object, not inferred from the bounded restriction. A resolution stays quasi-isomorphic after an exact functor. The closed-support node explicitly gives the right adjoint to termwise i_* for Noetherian X and finite A, with no boundedness assumption.
3. The coefficient-extension datum gives the DVR and finite quotients; the displayed two-term free resolution checks perfection. Its residue characteristic ell gives additive torsion. The normalized completed-comparison statement gives the strict-diagram comparison, actual projections and psi, and integral constructibility gives the actual reduction isomorphisms and codomain membership. The identity case of finite-free completed comparison gives the completion unit; the direct-image/limits node explicitly compares the Roos product terms and 1-s as a strict-derived comparison, so its map on the connecting arrow is the one induced by the exact F (the operations definition supplies exactness and shifts). This is not an arbitrary completion of 1-s to a triangle.
4. The new Hom node supplies exactly the normalized Hom square needed to turn finite full faithfulness into tower-term Hom bijections. The new Roos node applies because step 3 supplies the specified product and whole-triangle comparisons. The formula I(u)=psi_Q F(u) psi_P inverse follows from naturality, so it compares the specified direct image, not just some fully faithful functor.
5. The new scalar node supplies linearity and coherent scalar comparison for I, not an assertion about unrelated ambient objects. The raw rationalization definition identifies its Hom map as tensoring the integral map; its inverse is linear since the original bijection is linear, and the two tensor composites are identities without a flatness argument. Applying the new common-stage node to the resulting rational family proves exactly the common-stage claim.
6. The exceptional-inverse-image definition supplies only the adjunction notation and Hom characterization. The inverse argument for its actual unit is elementary and written in full; it does not depend on a Yoneda citation that only says full faithfulness of representables. The finite closed-unit statement records exactly the ambient unit already obtained from step 2; the conclusion is not restricted to bounded constructible Q. No ambient right-adjoint existence is assumed at the other stages.

Small-case checks: for i=id every psi, beta, scalar comparison and unit has the identity normalization; a nontrivial scalar automorphism would violate the displayed unit square, so the map is pinned. For empty Z or X the categories/values are zero and no dimension maximum is taken. Nonreduced closed Z is allowed by the finite-stratum lemma. For n=1 all reductions and units are defined. The two-term resolution uses t^n nonzero in the DVR, not a zero-divisor assertion in A_n. No finite Tor bound was silently added: the Hom node allows arbitrary finite targets, and the reconstruction uses all degrees m, preserving possible lim^1 terms. For E=L the scalar cocycle reduces to its unit; for three extensions its domain and codomain agree as checked above. Common-stage transition maps need not be injective: equality is only tested after a further extension, and that is enough for inverse representatives. Uniform cohomology bounds, not a chosen bounded model with unproved Tor finiteness, remain the definition of the integral category.

Mathlib searches ran only through msearch.py and are stored unchanged in searches.jsonl and the per-query transcripts. I read all returned names/types and inspected the relevant module-source candidates: the module adjunction formula in ChangeOfRings.lean (905ff), pushforwardPushforwardAdj in Sheaf/PushforwardContinuous.lean (298ff), and homological-triangle exactness. The hits concern underived modules, generic adjunctions, triangle exactness, Ind inclusions, filtered finality or algebraic adic completion; none states a new node or a one-line specialization. Each new node has two semantic phrasings, LeanSearch, Loogle, and source grep. The first Roos Loogle query has an unknown identifier; it is recorded as invalid, not absence, and replaced by a successful IsTriangulated search. No service failure was recorded as a negative answer.

No item statement dispute was discovered. I kept the old proof's rigorous distinctions between strict diagrams and evaluated arrows, completed and constant coefficients, raw rationalization and Karoubi completion, and common-stage objects and ordinary Omega-module sheaves. The only correction beyond work distribution was making ambient exactness support explicit in assembly step 2. There is no long non-elementary assembly step over 2000 characters. All four new proof arrays are empty so their proof work is available to other workers.

## Ownership of every old argument

| Old step | Argument retained in | Where the detailed argument remains |
|---|---|---|
| 1 | Assembly 1; existing finite-type, Noetherian-open, closed-immersion and compact-support definitions | Verbatim old step below; no new geometric lemma duplicates them |
| 2 | Assembly 2; recollement and counit criterion | Verbatim old step below |
| 3 | Assembly 2; existing finite-immersion-constructibility-interval, exactness and factorization | Existing statement explicitly records strata plus U, cohomology and unchanged interval; verbatim old step below |
| 4 | Existing completed-coefficient-pushforward-comparison; Hom node normalization; scalar node model transport | Derived-composition/quotient coherence is already in the existing statement; verbatim old step below |
| 5 | Assembly 3; existing completed comparison, integral preservation, identity finite-free comparison and direct-image/limits; scalar-node psi | Actual projections and whole Roos triangle are already in those statements; verbatim old step below |
| 6 | New reduction Hom-square node | Full old argument below is its independent proof packet |
| 7 | New Roos Hom-bijection node; assembly 4 natural conjugation | Full old product/1-s/kernel/cokernel/diagram-chase argument below is its independent proof packet |
| 8 | New scalar node (linearity), assembly 5, raw rationalization definition | Tensor inverse calculation kept here and in the old proof below |
| 9 first paragraph | New strict direct-image scalar-comparison node | Noetherian/dimension/completeness checks and normalized comparison argument below are its independent proof packet |
| 9 second paragraph | New common-stage full-faithfulness node | Conjugation, transition compatibility, well-defined inverse and both composites are all stated and preserved below |
| 10 | Assembly 6 | Explicit two-sided inverse retained, no new elementary-unit node |
| 11 | Assembly 2 and 6, existing closed-support and finite closed-unit statements | Full ambient existence scope and conditional higher-stage scope retained below |

## Preserved returned proof, verbatim

The following archive is part of this report so that every future worker receives the original argument together with its new self-contained statement. It is not a proof array in any new node.

### Old step 1

Keep the coefficient datum of [def-weil-l-adic-coefficient-extension], with $\ell\ne\operatorname{char}(k)$ and $n\ge1$. A field is Noetherian because its only ideals are $0$ and itself, and its one-point spectrum is quasi-compact; applying [lem-weil-pbc-finite-type-over-noetherian] to the structural maps makes $X,Z$ Noetherian. For every affine open $V\subset X$, the open subscheme $U\cap V$ is quasi-compact by [lem-weil-pbc-noetherian-open-subscheme-noetherian], first to $V\subset X$ and then to $U\cap V\subset V$. Hence the complementary open immersion $j:U\hookrightarrow X$ is quasi-compact as a morphism, as required below. By [lem-weil-pbc-closed-immersion-integral-separated-uc], $i$ is finite, separated and universally closed, hence proper (on affine charts a quotient algebra is generated by $1$ as a module and is of finite type). At finite level the compactification $Z\xrightarrow{\mathrm{id}}Z\xrightarrow{i}X$ in [def-compact-support-direct-image-detailed] computes $Ri_!=Ri_*$. For the higher stages, [def-weil-integral-rational-qbar-compact-support] uses the same compactification at every finite level: its integral tower is therefore exactly the direct-image tower, and its rationalization and common-stage functors are those of direct image as well. The symbol $i_*$ below denotes this derived direct image; the finite-level underived direct image computes it by step 3.

Cited nodes: `def-weil-l-adic-coefficient-extension`, `lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-closed-immersion-integral-separated-uc`, `def-compact-support-direct-image-detailed`, `lem-weil-pbc-noetherian-open-subscheme-noetherian`, `def-weil-integral-rational-qbar-compact-support`.

### Old step 2

For $A=A_{E,n}$, [prop-weil-open-closed-recollement-adjunctions] supplies $i^*\dashv Ri_{*,n}$ on the ordinary ambient pro-etale derived categories and an invertible counit $i^*Ri_{*,n}\to\mathrm{id}$. Apply [lem-weil-pbc-adjunction-counit-iso-right-fully-faithful] to this very adjunction: $Ri_{*,n}$ is fully faithful on the entire ambient category. In particular its maps on Hom groups of any two bounded constructible objects are bijections.

Cited nodes: `prop-weil-open-closed-recollement-adjunctions`, `lem-weil-pbc-adjunction-counit-iso-right-fully-faithful`.

### Old step 3

The quasi-compact-complement hypothesis of [lem-exc-proetale-closed-exact] holds by step 1, so finite-coefficient $i_*$ is exact. [lem-weil-pbc-exact-functor-derived-factorization] realizes it termwise on derived categories. In particular a resolution $K\to I$ remains a quasi-isomorphism under $i_*$, so termwise $i_*K$ computes $Ri_{*,n}K$, and exactness gives $\mathcal H^r(Ri_{*,n}K)=i_*\mathcal H^r(K)$. To check constructibility directly, take the finite stratification of $Z$ for each constructible cohomology sheaf in [def-weil-finite-torsion-constructibility] and adjoin the open stratum $U$. On a stratum lying in $Z$, restriction of $i_*G$ is restriction of $G$ by the module counit of [lem-exc-proetale-closed-fully-faithful]; on $U$ it is zero by [lem-exc-proetale-closed-essential-image]. Thus the same finite locally constant modules, and the zero module on $U$, provide a constructible stratification on $X$. For a stratum $S=V\cap C$ in $Z$, write $V=Z\cap W$ with $W$ open in $X$; $C$ is closed in $X$ since $Z$ is closed, so $S=W\cap C$ is locally closed in $X$. It is constructible by the Noetherian clause of [def-weil-constructible-subset]; that clause also makes $U$ constructible. The cohomological interval is unchanged. Therefore the ambient fully faithful functor of step 2 restricts to the stated finite bounded constructible categories.

Cited nodes: `lem-exc-proetale-closed-exact`, `lem-weil-pbc-exact-functor-derived-factorization`, `def-weil-finite-torsion-constructibility`, `lem-exc-proetale-closed-fully-faithful`, `lem-exc-proetale-closed-essential-image`, `def-weil-constructible-subset`.

### Old step 4

Put $R=\mathcal O_E$, $I=(\varpi_E)$ and $A_n=R/\varpi_E^n$. The datum [def-weil-pbc-adic-coefficient-datum] agrees here with the completed integral coefficient sheaf in [def-weil-derived-complete-integral-detailed]: at $T=X,Z$ both are $R_T=\varprojlim_n(A_n)_T$, and all finite levels are regarded as $R_T$-modules by the projection $R_T\to(A_n)_T$. The DVR and finite-quotient assertions in [def-weil-l-adic-coefficient-extension] check the Noetherian, finite and additive-torsion assumptions of the adic datum; perfection of $A_n$ over $R$ follows from the two-term free resolution $0\to R\xrightarrow{\varpi_E^n}R\to A_n\to0$. Write $F$ for ordinary total derived ringed direct image over these completed sheaves, and $F_n=Ri_{*,n}$. The coefficient identification and the derived operations, including exactness and shift comparison, are [lem-weil-pbc-profinite-coefficient-inverse-image] and [def-weil-pbc-proetale-operations]. For a finite-coefficient complex $M$, there is a canonical comparison $F\operatorname{Res}_nM\cong\operatorname{Res}_nF_nM$: both are derived direct image for the same composite ringed-topos morphism. Specifically, reducing the structural coefficient morphism before or after $i$ gives the same ring map, since its $n$-th projection commutes with inverse image. Applying [lem-weil-pbc-ringed-topoi-derived-pushforward-composition] to these two factorizations supplies the comparison; restriction is exact and so is its own derived functor. Its naturality for quotient transitions follows from the same commutative ring maps. The strict coefficient-tower coherence is supplied by [lem-pur-completed-coefficient-pushforward-comparison].

Cited nodes: `def-weil-pbc-adic-coefficient-datum`, `def-weil-derived-complete-integral-detailed`, `def-weil-l-adic-coefficient-extension`, `lem-weil-pbc-profinite-coefficient-inverse-image`, `def-weil-pbc-proetale-operations`, `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, `lem-weil-restriction-of-scalars-exact`, `lem-pur-completed-coefficient-pushforward-comparison`.

### Old step 5

Let $I$ denote the strict-tower integral functor of [def-weil-derived-direct-image], with functorial realization fixed by [lem-weil-derived-direct-image-composition]. For $K\in D^b_c(Z,R)$, [lem-pur-completed-coefficient-pushforward-comparison] gives a natural isomorphism
$$\psi_K:FK\xrightarrow{\sim}IK=R\varprojlim_n\operatorname{Res}_nF_nK_n.$$
Its $n$-th projection is $F(c_{K,n})$ followed by the coefficient comparison of step 4, coherently on strict towers. By [lem-sf-integral-direct-image-constructible], $IK\in D^b_c(X,R)$ and its actual projection-adjoint reduction maps are isomorphisms. Transport through $\psi_K$ gives $FK\in D^b_c(X,R)$ and $(FK)_n\cong F_nK_n$, with those same projection-adjoint maps.
For the triangle comparison, let $\chi_K:K\xrightarrow{\sim}R\varprojlim_n\operatorname{Res}_nK_n$ be the natural completion map supplied by the identity-extension case of [lem-weil-finite-free-completed-scalar-comparison]. Use the strict Roos triangle transported through $\chi_K$. Apply the canonical strict-tower comparison of [prop-weil-pbc-direct-image-limits] and step 4's coherent coefficient comparison. They identify its image under $F$ with the image-tower Roos triangle, including its connecting arrow. The first-object comparison is the canonical $\psi_K$ above: both are the derived comparison of the same composite direct image on the strict reduction tower, precomposed with $F(\chi_K)$. Thus no arbitrary completion of $1-s$ to a triangle is used.

Cited nodes: `def-weil-derived-direct-image`, `lem-weil-derived-direct-image-composition`, `lem-pur-completed-coefficient-pushforward-comparison`, `lem-sf-integral-direct-image-constructible`, `lem-weil-finite-free-completed-scalar-comparison`, `prop-weil-pbc-direct-image-limits`.

### Old step 6

Fix $P,Q\in D^b_c(Z,R)$ and $m\in\mathbf Z$. The derived change-of-coefficients adjunction [lem-weil-derived-scalar-extension-restriction-adjunction], at $Z$ and $X$, gives
$$\Hom_Z(P[m],\operatorname{Res}_nQ_n)\cong\Hom_{Z,A_n}(P_n[m],Q_n),$$
$$\Hom_X(FP[m],\operatorname{Res}_nF_nQ_n)\cong\Hom_{X,A_n}(F_nP_n[m],F_nQ_n).$$
In the second line use the actual reduction isomorphism $(FP)_n\cong F_nP_n$ of step 5. The map on these Hom groups induced by $F$ is precisely $u\mapsto F_nu$ under these adjunctions. Indeed, the transpose of $u:P_n[m]\to Q_n$ is $P[m]\xrightarrow{c_{P,n}}\operatorname{Res}_nP_n[m]\xrightarrow{\operatorname{Res}_nu}\operatorname{Res}_nQ_n$. Applying $F$, and using step 4's coefficient comparison, gives the same formula on $X$ because the reduction comparison of [def-weil-derived-direct-image] is adjoint to the tower projection. Step 5's comparison therefore identifies $F(c_{P,n})$ with $c_{FP,n}$ followed by the reduction comparison. The finite full faithfulness of step 2 now makes the two displayed Hom groups bijective. Naturality in $Q_n$ makes these bijections commute with the quotient transition maps; no assertion that restriction of scalars is fully faithful is being used.

Cited nodes: `lem-weil-derived-scalar-extension-restriction-adjunction`, `def-weil-derived-direct-image`.

### Old step 7

Set $B=\prod_n\operatorname{Res}_nQ_n$ and $B'=\prod_n\operatorname{Res}_nF_nQ_n$. The product comparison $FB\cong B'$ of [prop-weil-pbc-direct-image-limits] has $n$-th projection $F$ of the original projection. By the product universal property, for every $m$ the map
$$\Hom_Z(P[m],B)\longrightarrow\Hom_X(FP[m],B')$$
is the product of the bijections in step 6, and hence bijective (the inverse applies their inverses coordinatewise). The transition compatibility in step 6 says it commutes with $1-s$. Apply [lem-weil-pbc-hom-into-triangle-exact] to the Roos triangle of [prop-weil-pbc-roos-triangle] and its rotations, and to the corresponding image triangle supplied by [prop-weil-pbc-direct-image-limits]. Writing $A_m=\Hom_Z(P[m],B)$, their five-term exact rows give
$$0\to\operatorname{coker}(1-s:A_1\to A_1)\to\Hom_Z(P,Q)\to\ker(1-s:A_0\to A_0)\to0,$$
and the analogous row on $X$. The maps on both outside terms are isomorphisms by the product bijections. The middle map is $F$ on Hom, because the triangle comparison is the one induced by $F$. For injectivity, a middle element mapping to zero has zero image on the right, hence comes from the left; injectivity on the left then kills it. For surjectivity, lift the right image of a desired middle element through the right isomorphism, lift that to the source middle by exactness, and correct the difference by the left isomorphism. Thus $\Hom_Z(P,Q)\to\Hom_X(FP,FQ)$ is bijective. Naturality of $\psi$ from step 5 gives $I(u)=\psi_QF(u)\psi_P^{-1}$ for the specified integral direct image $I$; conjugation by these isomorphisms is bijective on Hom groups. Together with step 5's codomain check this proves integral full faithfulness for that specified functor.

Cited nodes: `prop-weil-pbc-direct-image-limits`, `lem-weil-pbc-hom-into-triangle-exact`, `prop-weil-pbc-roos-triangle`.

### Old step 8

At the rational stage use the raw scalar localization of [def-weil-rationalization-karoubi], which has the same objects and $\Hom_E(P,Q)=\Hom_R(P,Q)\otimes_RE$; no Karoubi envelope is present. The integral direct image is $R$-linear: it carries multiplication by a constant scalar to multiplication by the same scalar on sections and on the complexes computing derived direct image and inverse limit. The ambient and full-subcategory scalar action is [lem-weil-integral-constructible-linear]. By [def-weil-derived-direct-image], rational direct image is its scalar localization. Therefore its Hom map is the integral Hom bijection of step 7 tensored with $1_E$, with inverse the integral inverse tensored with $1_E$. This proves full faithfulness at $E$ without any flatness inference.

Cited nodes: `def-weil-rationalization-karoubi`, `lem-weil-integral-constructible-linear`, `def-weil-derived-direct-image`.

### Old step 9

The schemes are Noetherian by step 1 and finite-dimensional by [lem-kun-dimension-finite-type]. The identity completion unit in step 5 and the unit-compatible Koszul/quotient comparison of [lem-weil-pbc-constant-completion-equivalence] verify ambient derived completeness. Thus [prop-weil-pbc-scalar-extension] applies. Steps 3 and 5 verify preservation of the constructible categories; [lem-weil-finite-free-completed-scalar-comparison] identifies ordinary completed-ring scalar extension with the specified strict-tower extension, including the identity case. After raw rationalization [def-weil-rationalization-karoubi], the ambient comparison gives coherent natural isomorphisms
$$\theta_{L/E,P}:F_L(P\otimes_E L)\xrightarrow{\sim}(F_EP)\otimes_E L,$$
where $F_E$ is the specified rational direct image, identified with the ordinary completed direct image by $\psi$. These are the inverses of the comparisons in [prop-weil-pbc-scalar-extension].
For $(E,P),(E',Q)$ in [def-weil-algebraically-closed-coefficients], write $P_L=P\otimes_E L$, $Q_L=Q\otimes_{E'}L$ for each common finite extension $L$. Step 8 gives bijections
$$b_L(u)=\theta_{L/E',Q}F_L(u)\theta_{L/E,P}^{-1}$$
onto the $L$-stage Hom group of the two original direct images. Coherence makes $b_L$ commute with the transition maps. Explicitly, invert a target representative $v$ at stage $L$ by $b_L^{-1}(v)$. If representatives agree at a larger common stage $M$, their inverse images agree there by transition compatibility and injectivity of $b_M$. The rule therefore defines an inverse on the common-stage Hom colimits; both composites are identities already at a representing stage. This proves full faithfulness at $\Qlb$.

Cited nodes: `def-weil-algebraically-closed-coefficients`, `prop-weil-pbc-scalar-extension`, `def-weil-rationalization-karoubi`, `lem-weil-finite-free-completed-scalar-comparison`, `lem-kun-dimension-finite-type`, `lem-weil-pbc-constant-completion-equivalence`.

### Old step 10

At a stage with an adjunction $F=i_*\dashv G=Ri^!$, as specified in [def-weil-exceptional-inverse-image], let $\eta$ be its unit. For every $P,Q$ the adjunction sends $F(g)$ to $\eta_Qg$ by naturality of the unit, so full faithfulness just proved implies that $\eta_Q\circ-:\Hom(P,Q)\to\Hom(P,GFQ)$ is bijective. Taking $P=GFQ$ gives $r:GFQ\to Q$ with $\eta_Qr=1$. Taking $P=Q$ and using injectivity gives $r\eta_Q=1$, since postcomposition by $\eta_Q$ sends both $r\eta_Q$ and $1_Q$ to $\eta_Q$. Thus $r$ is a two-sided inverse of the specified adjunction unit $Q\to Ri^!i_*Q$. This spells out the Yoneda argument and needs no new categorical lemma.

Cited nodes: `def-weil-exceptional-inverse-image`.

### Old step 11

Finally, the finite-stage existence clause holds on the entire ordinary ambient derived category: [lem-exc-proetale-closed-support] supplies a right adjoint to termwise $i_*$ for a Noetherian $X$ and a finite constant ring. By step 3 this termwise functor is $Ri_{*,n}$. The finite ambient fully faithful assertion of step 2 and step 10 therefore give the invertible ambient unit for all $Q$, with no boundedness or constructibility assumption. This is exactly the adjunction and unit asserted in [prop-sf-closed-immersion-unit]; its constructible specialization uses the identity compactification in step 1. No existence of a right adjoint at the other coefficient stages is assumed or claimed here beyond the conditional assertion of the item.

Cited nodes: `lem-exc-proetale-closed-support`, `prop-sf-closed-immersion-unit`.

## What could not be finished

No mathematical repair remains beyond the deliberately statement-only new nodes. Delivery validation and push results are recorded by the delivery tool; no Lean proof or compilation is part of this stage.
