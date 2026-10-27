## Worker report

This retains the completed repair of the human's 2026-10-21/22 re-split order and now repairs the landing return about completion in the side DAG not being promoted to the live DAG. The sandbox initially contained only the dispatcher brief markers, with no node, report or search log. I therefore recovered the current repository's reviewed 15-step argument, including the maintainer's Step 11 localization correction, into the sandbox before changing it. The node's statement and statement dependencies are unchanged. There is no attachment: the project-source search by blueprint id, declaration and semilinear/Galois concepts found only the item's `Sheaf.AlgebraicGeometry.SemilinearGaloisAlterationDomination` declaration, whose body is `sorry`; no exact sorry-free declaration occurs under `WeilConjectures/`.

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-semilinear-galois-alteration-domination.json`: item, split into a short assembly; four steps, 1452 characters in proof text.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-semilinear-field-envelope.json`: statement, unsplit; field enlargement, compatible-pair group and invariant field. No exact Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-semilinear-finite-normalization-model.json`: statement, unsplit; finite normalization and semilinear action. No exact Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-conjugate-projective-generic-closure.json`: statement, unsplit; projective birational Chow model, conjugate product, equivariant generic graph and its reduced closure. No exact Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-projective-model-normalization.json`: statement, unsplit; normalization, action lifting, generic fibre preservation and projective alteration. No exact Mathlib match.
- `report.md`, and sandbox-only `citations.json`, actual `searches.jsonl`, raw search outputs, scripts and the recovered `returned-proof.json`. Only node files and this report enter the delivery.

## Attachments

None. No Lean file was written or compiled.

## Wanted literature

WANTED: A. J. de Jong, *Families of curves and alterations*, Ann. Inst. Fourier 47 (1997), §§3.2, 3.8, Situation 5.3, pp.605,608,613, for the item's inherited comparison with equivariant alterations. There is no local PDF. This repair uses the local ILO PDF and Stacks sources and preserves `proof_origin.by = agent`; it does not pretend the general semilinear construction is a verbatim theorem of ILO. The previous source's publisher URL remains in the item as inherited metadata; I did not claim a fresh online reading of that missing paper.

## Landing return repaired against the current DAG (2026-10-22)

The current return is: L approved the reading but refused the landing because completion in the side DAG had not been promoted to the live DAG read by the queue. I retained the existing four-node split, all 25 logged searches and their raw results, citations.json, and the full 15-step proof below. The retained dry-run marker identifies the earlier prepared head as `663d187d7d1`; I did not run git in the shared read clone. The required delivery tool constructs the new commit against the current server DAG.

I compared every sandbox node with the current read clone. None of the four new helper ids exists there. For the item, all fields except `proof`, `proof_deps`, and `split_report` agree exactly with the current DAG, including the statement, statement dependencies, blueprint metadata, Lean records and prior review metadata. The recovered `returned-proof.json` equals the current item's entire 15-step proof, including the reader's localization fix. Thus no mathematical base change needs transplanting; the delivery replaces that current long proof with the retained four-step assembly and its four statement-only helpers. The released stage-1 repair note still explicitly requires at least three new helpers and an assembly of at most 3000 characters, with the statement fixed; this delivery has four helpers and 1452 characters.

The first required dry run on this retry exited with three newly introduced same-tag candidates. I opened and read their complete current statements: `lem-sfb-common-normal-compatible-groups`, `lem-sfb-cover-nested-cartier-preparation`, and `lem-sfb-finite-normal-cover-normalization`. They are not cited by the assembly and none states a retained helper; the precise differences are recorded under Not duplicates. This is an update to the delivery's current-DAG audit, not an unchanged re-push. The new candidate nodes do not change any of the five exact statement quotations in citations.json.

The renewed dry run for this repair found one additional live same-tag candidate, `lem-wf-henselian-residue-lift-diagram` (09DT). I read its full statement: it constructs the finite etale lift diagram over a henselian local ring and proves Galois-subdiagram cofinality. It does not construct a semilinear normal envelope over a moving fixed field or its compatible-pair group. The required explicit pair distinction is added under Not duplicates. I again checked the four helper statements cited by the assembly: all five citation quotes remain exact, and the recovered 15-step proof still equals the current read-clone proof. The parent assembly remains 1452 characters. No node statement or Mathlib search question changed on this retry.

## Current-DAG repair (2026-10-23)

This retry retains the returned delivery rather than starting a second split. The retained successful dry-run marker names prepared head `07830b52352`. I ran the required dry run first; it exited before pushing because a new current-DAG node, `lem-sfb-normalization-generic-residue-affine-charts`, also cites Stacks 035H. I opened its entire current statement. It computes the normalization of T in the product of T's own generic residue fields, with affine restriction maps, allowing nonreduced T and no finiteness hypothesis. Our finite-normalization-model node instead normalizes integral S in a prescribed larger finite field M, proves finiteness and absolute projectivity, and lifts compatible semilinear actions on S and M. These assertions are neither supplied by nor a specialization of the new candidate. The explicit pair comparison is added below.

I compared all five retained node files with the current shared DAG. The four helper ids remain absent; the parent differs only in proof, proof_deps and split_report. Its statement, statement dependencies, Lean record, review metadata, source and blueprint metadata are unchanged. The recovered returned-proof.json still equals all fifteen current proof steps exactly, including the localization correction. I re-read the current statements of every dependency cited by those old steps, as well as all four helpers cited by the assembly. No changed dependency requires a mathematical transplant. The earlier prepared branch is not reused as a base: deliver.py constructs this repaired delivery against the fetched current server DAG.

I repaired stale text in split_report.blueprint that described an intermediate five-step assembly with Chow left in the parent. It now describes the actual four-step assembly: field envelope, finite normalization, Chow plus conjugate generic closure, and final normalization. This changes neither the route nor a statement. All 25 recorded searches and raw outputs are retained, since none of their search questions changed. Five citation entries still quote the exact helper statements, and every cited helper is present in the sandbox. The four statement-only helpers retain every old construction through the complete redistribution below; the assembly is 1452 characters, with no step above 2000 characters.

## Repair and scope

The original mathematical return required that 11128 characters of construction be distributed across at least three genuine subproblems, each left statement-only for parallel proof work, with a parent assembly of at most 3000 characters. This delivery adds FOUR unsplit statements, each with empty `proof`, empty `proof_deps` and null `proof_origin`. Each has its own objects, hypotheses and definitions, and at least five actually executed Mathlib searches: LeanFinder twice in different wording, LeanSearch, Loogle, and source grep. None restates the whole alteration domination theorem. The first is entirely field theory; the second only realizes an already specified field action on a finite model; the third starts with the finite model B and proper T, constructs a projective birational Chow model Y of T, and then constructs their conjugate generic graph; the fourth starts with an already supplied equivariant projective generic model and normalizes it. In particular no single new statement chooses all the data of the item.

All substantive construction arguments have moved to the four new nodes. Old step 6 (the integral Chow construction, closing its projective-space immersion and checking the generic fibre) is included in the graph node alongside old steps 7--10. Old step 14 is the elementary projection equation in the final assembly, and is also an explicit assertion in the graph statement. Every old proof paragraph is preserved verbatim below, with its original citations and sources, and assigned to the new node responsible for it. The first dry run passed, after which I made this stricter redistribution and renewed the graph node's searches because its search question changed. The final dry run is for this four-step version.

The only clarification during the self-review was to say explicitly that the two supplied maps B to S and Y to S in the new graph statement are k-morphisms. The original construction already has these hypotheses; the diagonal argument in the product over k needs them. This does not change the item's statement. No statement dispute or source error was found. There is no unfinished authorized operation beyond the required dry run and push; the four new statements intentionally await other workers' proofs.

## Route, blueprint and search audit

I read GOAL.md, the chapter and unit records, SETUP's three levels and the current main-20261015 direct-images proof (3). The four nodes preserve the inherited alteration prerequisite of that route, with no SGA source. The inherited `blueprint.from.node` is null; `tools/blueprint_refs.py ancestor` reports that the creation chain has no blueprint ancestor. I retained that value, prepended this item to each new node's `from.via`, and made each `from.place` identify its exact old proof steps as well as the inherited direct-image/ILO prerequisite. No invented blueprint ancestor or change to a unit's proof is needed.

I searched all imported blueprint nodes with `blueprint_refs.py search` for normal extension, conjugate, equivariant normalization, projective generic, normalization, semilinear field, normalization model, generic graph and equivariant projective. No exact blueprint statement exists. The broad normalization/conjugate results concern other statements; all same-Stacks-tag candidates were read and are distinguished below. Whole-DAG searches by the four new ids, compatible lifts, normal envelopes, equivariant normalization, conjugate products and generic graph closure found no exact existing statement. Source searches in `lean/WeilConjectures/` and `lean/Sheaf/` by the item id, full declaration and these concepts also found no exact finished helper. Existing integral Chow, normalization, Segre and normal-field results remain ingredients rather than copies.

All 25 new Mathlib queries were executed through the required msearch.py. The raw outputs are retained as `<field|normal|graph|final>-<tool>-<round>.txt`; the exact query, tool and result digest are copied from the actual log into each node. All services answered on this attempt. Field hits include `IsGalois.of_fixed_field`, `FixedPoints.normal`, `IsGaloisGroup.fixedPoints`, normal closure and `AlgEquiv.restrictNormalHom_surjective`. I read `Mathlib/FieldTheory/Normal/Basic.lean` around lines 213--235, normal closure finite dimensionality and the fixed-field instance; these do not state the compatible-pair envelope retaining a nonfaithful H with the required inseparable branch. The construction requires choosing the fixed base, a normal closure, a pullback group, proving its kernel description, and applying the fixed-field theorem; it is not a one-line specialization of a Mathlib declaration. For the three geometric nodes the nearest hits were `Scheme.Hom.normalization`, `normalizationDesc`, integral-normalization instances and `integralClosure.coe_smul`. I read the normalization module, including its integral-closure charts, gluing, and universal property: these are not the whole equivariant projective constructions. Projective-spectrum and unrelated module/projective hits do not provide the graph construction. There are zero new Mathlib leaves.

## Review by Q141

For this 2026-10-23 repair I read the new affine-chart candidate in full and the current statements behind every old proof citation. In particular def-fin-normalization-extension still supplies localization, lem-fin-finite-over-projective only supplies global embeddings over affine bases (used over Spec k), and lem-sbc-normalization-dominant-lift requires the normal integral source supplied by the final normalization. I re-read local fields.tex normal closure, fixed-field and lifting statements, morphisms.tex normalization, finite normalization and dense-open finiteness, and varieties.tex projective normalization. They preserve the finite-type, normality and projectivity hypotheses used here. Step 1 retains H even if its field action has a kernel; step 2 uses inverse pullback on K; step 3 supplies proper integral T and no action on it; step 4 preserves the actual generic action so its invariant field is for the same N. The newly shared 035H tag does not supply any of those missing semilinear conclusions. I corrected only the current-DAG audit and the stale intermediate assembly map, leaving the approved mathematics and logged searches intact.

On this landing repair I re-read the current statement of every node cited by the four assembly steps, namely the four retained helper statements, and checked the five verbatim quotes against them. Step 1's finite L/K is obtained on the finite dense open containing the generic point, where the source's integral finite generic algebra is a field and is its function field. Step 2 has exactly the inverse-pullback restriction required by the normalization-model statement. Step 3 has proper finite-type T over k, a finite k-morphism B to S, and the specified L into M; no action on T has been added. Step 4 uses the supplied generic-fibre identification, so its lifted action is the field-envelope action and the invariant-field conclusions concern the same kernel. I also compared all current statements cited by the recovered 15-step argument, read the local Stacks normal-closure, fixed-field, normalization, projective-normalization and dense-open-finiteness passages, and re-read local ILO X Theorem 3.4 Step 4. The old proof is byte-equal to the current proof, so none of those arguments was silently replaced on rebase. The newly found same-tag candidates concern simultaneous constants, boundary preparation, and recognition of an already finite normal cover respectively; they cannot supply the missing prescribed field enlargement with separable choice or the semilinear normalization action. No statement or search question changed, so the completed searches were reused rather than rerun.

I read the local ILO X Remark 3.3.2, p.158, and Theorem 3.4 Step 4, pp.160--161. The remark expressly allows a purely inseparable step beneath a separable Galois step; the theorem's proof enlarges by a projective Galois alteration dominating the supplied alteration. I checked the old agent construction and all four new statements against that intended use, rather than imposing separability or a faithful group action not in the item.

For the field node I read Stacks fields.tex Tags 09I3 (`lemma-galois-over-fixed-field`), 09DT (`lemma-normal-closure`), 0EXM (`lemma-normal-closure-galois`), 0BME (`lemma-lift-maps`, part 2) and 030M (`lemma-normal-case`). The faithful-image passage applies Artin to the image of H while the compatible-pair group keeps H itself. The normal closure is over F = K^H, so every A_h extends; it need not be separable. The kernel is all Aut_K(M), not merely the lifts of a faithful quotient. Normality over K and the fixed-field purely-inseparable result give the claimed invariant field. In the separable branch K/F and L/K separable give L/F separable, so a finite Galois normal closure supplies both M/K separable and the fixed-field equality. This statement absorbs old steps 1--3 and 15, not their scheme-level conclusion.

For the finite-normalization node I read morphisms.tex Tags 035H (`definition-normalization-X-in-Y`), 035I (`lemma-characterize-normalization`), 0AVK (`lemma-nagata-normalization-finite-general`), and varieties.tex 0GK4 (`lemma-normalize-projective`), together with the exact existing nodes used in old steps 4--5. Finite type over a field is retained for finiteness of the integral closure; projectivity of the finite model is used only over the affine Noetherian base Spec k. The new statement does not assert that finiteness alone is a global projective embedding over arbitrary bases. On each chart the inverse field automorphism sends monic equations to monic equations; these isomorphisms commute with localization, so glue and obey the group law. The inverse-pullback convention is explicit in the new statement. On the generic fibre the integral closure of K in finite M is M. No action on T is introduced.

For the graph node I read coherent.tex Tag 0201 (`remark-chow-Noetherian` (2),(3)), morphisms.tex proper-over-separated (`lemma-image-proper-scheme-closed`, part 2) and schemes.tex `lemma-immersion-when-closed`, as well as constructions.tex Tag 01WD (`lemma-segre-embedding`) and schemes.tex Tag 01J3 (`lemma-reduced-closed-subscheme`), including the radical-ideal description and uniqueness, and the statements of all original step 6--10 dependencies. The properness of r and S/k gives T/k proper; integral Chow gives Y and its immersion into projective space. Proper-over-separated makes this immersion proper, hence closed. Its nonempty birational open contains the sole point of T_K, so Y_K = Spec L. This construction is part of the new graph node, with no action on T or Y required. The S-diagonal is closed because S is projective and separated over k. The k-morphism hypotheses ensure the conjugate factors have precisely the intended scalar twists and the fibre product is a closed subscheme of their product over k. I checked the indices directly: the new gj coordinate equals the old j coordinate, f_j = f d_(j^-1), and f_(gj) d_g = f_j. The kernel of the affine generic-point map is prime and localizes to the maximal ideal of the chosen point of P_K; its residue field is M because of the identity M-factor. This proves the exact generic fibre, not just dominance or the existence of an unspecified component. Reduction and closure do not introduce another field. Uniqueness of the reduced induced structure restricts the action. The projection to the identity factor is over S, with no equivariance imposed on Y.

For the final-normalization node I read varieties.tex Tags 0BXR (`lemma-normalization-locally-algebraic`) and 0GK4 (`lemma-normalize-projective`), morphisms.tex Tag 035Q (`lemma-normalization-normal`, especially part 4) and 0BAI (`lemma-finite-over-dense-open`), and the exact old step 11--13 node statements. The source of the lifting map is normal integral, so the universal dominant lift applies; uniqueness proves identities, multiplication and inverses. I retained the earlier maintainer's Step 11 repair: normalization commutes with localization because `def-fin-normalization-extension` explicitly says it, and over the generic fibre the already normal field M is unchanged. An absolute projective embedding of W followed by the closed graph into S times W gives the global closed embedding into P^n_S; no relative projective-bundle convention is substituted. Properness makes the image closed, and the supplied generic fibre makes it contain the generic point, so it is surjective. S is Noetherian by finite type over k, and the projective generically finite lemma makes b finite on a nonempty open. This is strictly the normalizing/alteration step for already supplied C, not the original theorem's construction of C or its field envelope.

I checked the four assembly steps against every statement actually cited. Step 1 uses the new field-envelope statement for all of M,J,rho,N and the optional separable choice; finite L/K follows from the alteration's dense-open finiteness. Step 2 uses the new finite-normalization statement with the J-action pulled back through rho; its compatibility equation is exactly the restriction equation from step 1. Step 3 applies the new graph statement with the supplied finite k-morphism B to S, proper k-morphism r:T to S and the inclusion L into M. The graph statement itself now supplies Y, pi, C, p and c, including r pi c = p and the equivariant generic-field identification. Step 4 uses the new final-normalization statement with p and C. The elementary equality r pi c nu = p nu holds as morphisms, and the field-envelope statement supplies all invariant and separable clauses for this same action. `citations.json` quotes the full exact statement of every node cited by every assembly step.

For the deferred graph construction I checked the precise existing statements behind old step 6, rather than treating a definition as a theorem: `lem-kun-projective-implies-proper` gives S/k proper, `lem-weil-pbc-proper-composition` gives T/k and Y/k proper, and `def-weil-proper-morphism` supplies separation and finite type. `lem-weil-pbc-integral-chow-relatively-ample` gives integral Y, proper surjection pi, a projective-space immersion and an isomorphism on nonempty U. `lem-weil-pbc-projective-space-proj-separated` gives the separated target, `lem-weil-pbc-proper-over-separated` makes the immersion proper, and `lem-weil-pbc-proper-immersion-closed` makes it closed. Each has exactly the needed hypotheses. The future proof plan below retains these citations and the generic-fibre argument in full, as well as every other original dependency; they are not prematurely written as proof_deps on the unsplit new graph node.

I tested H trivial, H with a nontrivial kernel, identity alteration, dim S = 0, characteristic zero, and K = F_p(t), L = K(t^(1/p)). In the last case M = L is a possible normal purely inseparable envelope with trivial field automorphism group; the invariant extension is allowed to be purely inseparable, rather than falsely asserting equality. A nonfaithful H survives in the pairs even when all its field actions are trivial. The identity element of any group guarantees a nonempty index set of conjugates. The graph ambient product may be nonreduced (inseparable tensor products), so the reduced closure is essential. The final node assumes integral nonempty S and C, rather than trying to take a function field of an empty or reducible scheme. No step longer than 2000 characters remains in the parent; all four deferred construction statements have empty proof lists as requested.

## Complete redistribution of the returned proof

The following is the full recovered argument, without shortening. These paragraphs are proof plans for the future workers in this report, not proof steps on the new unsplit nodes. Original citations remain exact existing node ids; the eventual workers still must split their own nodes and search any further helpers.

### Old step 1 → lem-sfb-finite-semilinear-field-envelope

Put $K=k(S)$ and $L=k(T)$, with the inclusion induced by $r$. Since $r$ is finite over a dense open, $L/K$ is finite. Write $A_h=(h^{-1})^*$ for the induced left action of $H$ on $K$, and let $H_0$ be its image in $\operatorname{Aut}(K)$. This is a finite faithful group of field automorphisms. Put $F=K^{H_0}=K^H$. Apply the finite-field-action theorem to $H_0$: $K/F$ is finite Galois. Hence $L/F$ is finite: if $(u_i)$ spans $K/F$ and $(v_j)$ spans $L/K$, then $(u_iv_j)$ spans $L/F$. Passing to $H_0$ here does not replace the original group $H$ in the conclusion.

Uses: lem-wf-finite-field-action-fixed-degree.

Source: literature/stacks-project/fields.tex, Tag 09I3, lemma-galois-over-fixed-field; finite tower expanded by products of bases.

### Old step 2 → lem-sfb-finite-semilinear-field-envelope

Choose a finite normal extension $M/F$ containing $L$ by finite normal closure. If $L/K$ is separable, make the following more specific choice instead: separability in the tower $F\subseteq K\subseteq L$ gives $L/F$ separable, and the finite-Galois-receiving lemma for the single extension $L/F$ gives a finite Galois $M/F$ containing a copy of $L$. Identify $L$ with that copy. In either choice $M/K$ is finite, since an $F$-spanning set also spans over $K$, and it is normal by normality over intermediate fields. No separability is assumed for the first choice.

Uses: lem-weil-pbc-finite-extension-in-finite-normal-extension, lem-zl-separable-permanence, lem-weil-pbc-finite-galois-receiving-separable-extensions, lem-weil-pbc-normal-extension-normal-over-intermediate.

Source: literature/stacks-project/fields.tex, Tags 09DT (lemma-normal-closure), 09HB (lemma-separable-permanence), 0EXM (lemma-normal-closure-galois), 09HN (normal over intermediate fields).

### Old step 3 → lem-sfb-finite-semilinear-field-envelope

Define $J=\{(h,\sigma)\in H\times\operatorname{Aut}_F(M):\sigma|_K=A_h\}$ with componentwise multiplication, and let $\rho(h,\sigma)=h$. The defining condition is preserved by multiplication and inverses. For each $h$, apply normal-intermediate-isomorphism lifting to the normal extension $M/F$ and the $F$-isomorphism $A_h:K\to K$. This supplies $\sigma$, so $\rho$ is surjective. The automorphisms of $M/F$ form a subset of the finite set of $F$-embeddings $M\to M$, so $J$ is finite. Finally $N=\ker\rho$ identifies with the whole group $\operatorname{Aut}_K(M)$, by $\sigma\mapsto(1,\sigma)$. Keeping pairs, rather than only their second coordinates, retains every element of a possibly nonfaithful $H$.

Uses: lem-sfb-normal-intermediate-isomorphism-lifts, lem-weil-pbc-finite-extension-finitely-many-embeddings.

Source: literature/stacks-project/fields.tex, Tag 0BME, lemma-lift-maps (2); Tag 09H8, lemma-count-embeddings-explicitly. Compare de Jong (1997) §3.2, p.605.

### Old step 4 → lem-sfb-semilinear-finite-normalization-model

Let $u:B\to S$ be the normalization of $S$ in $M$. The normalization-in-residue-field-extension theorem, applied to the generic point of $S$ and $M/K$, gives that $B$ is normal integral and $k(B)=M$, with the canonical $\operatorname{Spec}M\to B$ its generic-point inclusion. It is the affine integral-closure construction of the cited definition. Finiteness of normalization in a finite function-field extension applies because $S$ is integral of finite type over the field $k$; hence $u$ is finite. The scheme $\operatorname{Spec}k$ is Noetherian (a field has only the ideals $0$ and $k$). Thus finite-over-projective over this affine base makes $B$ H-projective over $k$. In particular $B$ is of finite type over $k$.

Uses: def-fin-normalization-extension, lem-weil-pbc-normalization-in-residue-field-extension, lem-fin-normalization-extension-finite, lem-fin-finite-over-projective, lem-kun-projective-implies-proper, def-weil-proper-morphism.

Source: literature/stacks-project/morphisms.tex, Tags 035H/035I (relative normalization) and 0AVK (lemma-nagata-normalization-finite-general), applied to Spec M over the finite-type field scheme S; varieties.tex Tag 0GK4, with finite-over-projective used only over Spec k.

### Old step 5 → lem-sfb-semilinear-finite-normalization-model

The $J$-action on the generic point $\operatorname{Spec}M$ is $a_j=\operatorname{Spec}(\sigma_j^{-1})$; it lies over the geometric action $h_j=\rho(j)$ on $S$. It extends to $B$ directly on integral-closure charts: the isomorphism on the base rings and $\sigma_j^{-1}$ carry integral elements to integral elements, since applying them to a monic equation again gives a monic equation. The same assertion for the inverse gives a ring isomorphism. These isomorphisms commute with localization, so glue by the normalization construction. Their composites agree on each chart with the specified field composites, hence give the group law. We have $u\circ a_j=h_j\circ u$, and on $k$ this is precisely the prescribed action through $\rho$. This argument needs no action on $T$.

Uses: def-fin-normalization-extension.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, Agent expansion of de Jong (1997) §§2.9 and 3.2: functoriality on integral-closure charts; ILO X Theorem 3.4 Step 4.

### Old step 6 → lem-sfb-conjugate-projective-generic-closure

The scheme $T$ is integral, separated and of finite type over $k$: properness of $r$ and projectivity of $S/k$ give properness of $T/k$. Apply integral Chow over $k$ to obtain an integral finite-type $Y$, a proper surjection $\pi:Y\to T$ which is an isomorphism over a nonempty open $U\subseteq T$, and an immersion $i:Y\to\mathbf P^n_k$. The composite $Y\to T\to\operatorname{Spec}k$ is proper. The target $\mathbf P^n_k$ is separated; proper-over-separated makes $i$ proper. Proper-immersion-closed then makes $i$ a closed immersion. Thus $Y$ is H-projective over $k$. Set $v=r\pi:Y\to S$. The generic fibre $T_K$ is $\operatorname{Spec}L$, because $r$ is finite over a dense open and $T$ is integral. Its only point is the generic point of $T$ and lies in $U$. Consequently $Y_K\cong\operatorname{Spec}L$ as well. Let $f:\operatorname{Spec}M\to Y$ be the map induced by $L\hookrightarrow M$.

Uses: lem-kun-projective-implies-proper, lem-weil-pbc-proper-composition, def-weil-proper-morphism, lem-weil-pbc-integral-chow-relatively-ample, lem-weil-pbc-projective-space-proj-separated, lem-weil-pbc-proper-over-separated, lem-weil-pbc-proper-immersion-closed.

Source: literature/stacks-project/coherent.tex, Tag 0201, remark-chow-Noetherian (2),(3); morphisms.tex Tag 01W6, lemma-image-proper-scheme-closed (2), and schemes.tex Tag 01IQ, lemma-immersion-when-closed.

### Old step 7 → lem-sfb-conjugate-projective-generic-closure

For $j\in J$ let $Y_j$ be the same abstract scheme $Y$ with structural map $h_jv:Y_j\to S$, and with $k$-structure induced from this map. This $k$-structure is the corresponding scalar twist of $Y/k$ along the automorphism of $k$ induced by $h_j$. Hence $Y_j/k$ is H-projective, by base change of its projective embedding along that automorphism. Form $P=B\times_S\prod_{j\in J}Y_j$. It is projective over $k$: first take the product over $k$ of the closed projective embeddings of $B$ and the $Y_j$, and iterate Segre. The equalities of their maps to $S$ cut out $P$ as a closed subscheme of this product. Indeed each equality is a pullback of the closed diagonal of the separated $k$-scheme $S$, and their finite intersection is an iterated closed immersion. Closed immersions are stable under base change and composition. Thus $P$ has an absolute closed projective embedding, whether or not $P$ is integral.

Uses: lem-pc-projective-base-change, def-pc-fibre-product, lem-chow-segre, def-weil-proper-morphism, lem-weil-pbc-proper-fp-permanence, lem-weil-pbc-closed-immersion-products.

Source: literature/stacks-project/morphisms.tex, Agent conjugate-product expansion; Tag 01WD, Segre embedding, in constructions.tex; diagonal and closed-immersion base change. Compare de Jong (1997) §§2.10,3.8.

### Old step 8 → lem-sfb-conjugate-projective-generic-closure

For $g\in J$ define the action on $P$ by $b\mapsto a_g(b)$ and $y_j\mapsto y'_{gj}=y_j$. This is a morphism of schemes: $h_{gj}v(y_j)=h_g(h_jv(y_j))=h_gu(b)=u(a_gb)$ is exactly the common-base equality required by the fibre product. On $k$ it is semilinear through $h_g$. Reindexing twice gives $(gg')j$, so the identity, product and inverse laws follow on all projections from the fibre-product universal property. Define $q:\operatorname{Spec}M\to P$ by the generic inclusion into $B$ and components $f_j=f\circ a_{j^{-1}}$ into $Y_j$. Since $vf$ is the generic map to $S$, $h_jvf_j$ equals this generic map. Moreover $f_{gj}\circ a_g=f\circ a_{j^{-1}g^{-1}}\circ a_g=f_j$, and the $B$-component is equivariant. Thus $q$ is $J$-equivariant.

Uses: def-pc-fibre-product.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, Agent expansion of the averaging over conjugates in de Jong (1997) §§2.10,3.8; group laws and equivariance checked on all projections.

### Old step 9 → lem-sfb-conjugate-projective-generic-closure

Let $C$ be the reduced induced closed subscheme on $\overline{\{q(*)\}}\subseteq P$. It exists by the reduced-closed-subscheme theorem. This closure is irreducible, so $C$ is integral. Its function field and generic fibre can be read without choosing a component: over $K$ the $B$-factor is $\operatorname{Spec}M$ and each $Y_j$-factor is a spectrum of a finite field extension of $K$ (the twist of $L/K$). Thus the coordinate ring of $P_K$ is a tensor product of finitely many finite-dimensional $K$-algebras and is finite-dimensional. The map to $M$ induced by $q$ is surjective because its $M$-factor is the identity. Its kernel is maximal, and the corresponding closed point has residue field exactly $M$. Closure and reduction restrict to this closed point on the generic fibre: on an affine chart the closure ideal is the kernel of the map to $M$, and localization at $K$ localizes this kernel. Hence $C_K=\operatorname{Spec}M$ and $k(C)=M$. As a closed subscheme of $P$, $C$ is H-projective over $k$.

Uses: lem-weil-pbc-reduced-induced-closed-subscheme, def-pc-integral-scheme, def-weil-closed-immersion, def-sc-function-field.

Source: literature/stacks-project/schemes.tex, Tag 01J3 (reduced induced structure); elementary affine kernel/localization calculation for the generic graph closure.

### Old step 10 → lem-sfb-conjugate-projective-generic-closure

The action on $P$ preserves $q(*)$ as a point, by equivariance of $q$, and therefore preserves its closure. Each ambient automorphism restricts uniquely to $C$, by uniqueness of the reduced induced closed structure. Uniqueness also shows that these restrictions obey the group law. The projection $C\to B\to S$ is consequently equivariant. This does not assert that $Y$ or $T$ carries any action.

Uses: lem-weil-pbc-reduced-induced-closed-subscheme.

Source: literature/stacks-project/schemes.tex, Tag 01J3, uniqueness of the reduced induced closed subscheme.

### Old step 11 → lem-sfb-equivariant-projective-model-normalization

Let $\nu:W\to C$ be the normalization in $k(C)=M$. The normalization theorem gives a finite surjective birational map; thus $W$ is integral and $k(W)=M$. Its local rings are normal: on an affine domain chart $A$ of $C$, the normalization ring is the integral closure of $A$ in $\operatorname{Frac}(A)=M$, a normal domain by the integral-closure lemma, and its localizations are normal domains by localization of normal domains. Finite-over-projective, applied with affine Noetherian base $\operatorname{Spec}k$, makes $W/k$ H-projective. In particular $W$ is of finite type and proper over $k$. The finite map $\nu$ restricts on the generic fibre to the identity of $\operatorname{Spec}M$: over an affine open $\operatorname{Spec}A_0\subseteq S$, the generic fibre is the localization at $A_0\setminus\{0\}$, integral closure commutes with localization (the localization clause of the normalization-in-an-extension definition, whose case $L=K$ is this normalization), and on the generic fibre the chart ring is $M$, which is already integrally closed in $M$. Hence $W_K=\operatorname{Spec}M$.

Uses: def-sc-normalization, def-fin-normalization-extension, lem-sc-normalization-exists, lem-weil-pbc-integral-closure-finite-extension-normal, lem-weil-pbc-localization-normal-domain, lem-fin-finite-over-projective, lem-kun-projective-implies-proper, def-weil-proper-morphism.

Source: literature/stacks-project/varieties.tex, Tags 0BXR and 0GK4 (normalization of an algebraic/projective scheme); algebra.tex Tags 034L and 00GY; defining localization compatibility.

### Old step 12 → lem-sfb-equivariant-projective-model-normalization

For $g\in J$, apply dominant lifting through absolute normalization to the dominant map $W\xrightarrow{\nu}C\xrightarrow{g}C$. Its source $W$ is integral with integrally closed local rings, so it lifts uniquely to $\widetilde g:W\to W$. The identity lift is the identity; the composite of two lifts lies over the corresponding product on $C$, so uniqueness proves the product law. Lifting $g^{-1}$ gives its inverse. Therefore this is a $J$-action. The normalization map is equivariant, and so is $b:W\to C\to B\to S$. On generic fields this is precisely the original action on $M$ (normalization is birational), and its scalar action on $k$ is the one through $\rho$.

Uses: lem-sbc-normalization-dominant-lift.

Source: literature/stacks-project/morphisms.tex, Tag 035Q, lemma-normalization-normal, universal dominant lifting to normalization; action laws from uniqueness.

### Old step 13 → lem-sfb-equivariant-projective-model-normalization

Choose an absolute closed embedding $i_W:W\hookrightarrow\mathbf P^n_k$. The map $(b,i_W):W\to S\times_k\mathbf P^n_k=\mathbf P^n_S$ is a closed immersion: its graph $W\to S\times_k W$ is the pullback of the closed diagonal of the separated scheme $S/k$ along $(s,w)\mapsto(s,b(w))$; compose it with $\mathrm{id}_S\times i_W$. Both maps are closed immersions by base change and composition. This proves that $b$ is H-projective in the required global convention, and hence proper. Its image is closed and contains the generic point of $S$, so it is surjective. The scheme $S$ is Noetherian by finite type over the Noetherian scheme $\operatorname{Spec}k$. Thus on a nonempty affine open $\operatorname{Spec}A\subseteq S$, $A$ is a Noetherian domain. The base change of $b$ is projective with generic fibre $\operatorname{Spec}M$, of dimension zero. Projective-generically-finite therefore makes it finite over a nonempty open of $\operatorname{Spec}A$, a dense open of integral $S$. Thus $b$ is an alteration.

Uses: def-weil-proper-morphism, lem-weil-pbc-proper-fp-permanence, lem-weil-pbc-closed-immersion-products, lem-kun-projective-implies-proper, lem-weil-pbc-proper-closed-image, lem-weil-pbc-finite-type-over-noetherian, lem-pc-projective-base-change, lem-fin-projective-generically-finite.

Source: literature/stacks-project/morphisms.tex, Graph as pullback of the diagonal; projectivity by its closed embedding; Tag 0BAI (lemma-finite-over-dense-open) through the cited projective-generically-finite node.

### Old step 14 → parent step 4; graph statement identity projection

Let $t$ be $W\to C\hookrightarrow P\to Y_1=Y\xrightarrow{\pi}T$. The defining common-base equality of the fibre product gives $rt=b$ as morphisms, so $t$ is an $S$-morphism. The equality holds on the whole scheme, not merely on its points or its generic field. No equivariance of $t$ is requested or used.

Uses: def-pc-fibre-product.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf, Agent conjugate-product construction: projection to the identity factor.

### Old step 15 → lem-sfb-finite-semilinear-field-envelope

We identified $k(W)=M$ and $N=\operatorname{Aut}_K(M)$, with that actual action on the generic field. Since $M/K$ is normal algebraic, the fixed-field theorem gives $M^N/K$ purely inseparable. It is finite: a $K$-linearly independent subset of the subfield $M^N$ is still independent in the finite-dimensional space $M$. This proves the invariant clause, including characteristic zero, where purely inseparable means equality. Also $k(W)/k(S)=M/K$ is finite. In the separable case, $M/F$ was chosen Galois. Every element's minimal polynomial over $K$ divides its separable minimal polynomial over $F$, so $M/K$ is separable as well as normal and finite. The finite-Galois-fixed-field theorem then yields $M^{\operatorname{Aut}_K(M)}=K$, the required strengthened conclusion.

Uses: lem-weil-pbc-normal-extension-fixed-field-purely-inseparable, lem-weil-pbc-finite-galois-fixed-field.

Source: literature/stacks-project/fields.tex, Tag 030M (lemma-normal-case), fixed-field purely-inseparable part; Tag 09I1 (finite Galois fixed field). Compare ILO X Remark 3.3.2, p.158.

The finite-normalization statement also records surjectivity of B to S: the finite map is closed and its generic fibre is nonempty, so its image contains the generic point of integral S and therefore all of S. Uniqueness of its lifted action follows on integral-closure charts from the specified generic field maps. These are consequences needed to make the helper self-contained, not added hypotheses on the item.

## Not duplicates

lem-sfb-conjugate-projective-generic-closure vs lem-trf-etale-reduced-cartier-descent: It asserts etale descent of reduced Cartier divisors, not an equivariant conjugate generic graph or its residue field.

lem-sfb-conjugate-projective-generic-closure vs lem-weil-pbc-coherent-filtration-integral-subschemes: It filters coherent modules by ideal sheaves on integral closed subschemes; it constructs no projective graph model or group action.

lem-sfb-conjugate-projective-generic-closure vs lem-weil-pbc-coherent-generic-point-ideal-inclusion: It extends a generic-point inclusion of coherent modules; it contains no conjugate scheme product or prescribed generic field.

lem-sfb-conjugate-projective-generic-closure vs lem-weil-pbc-coherent-support-union-exact-sequence: It splits coherent sheaves by supports, rather than constructing an equivariant integral generic graph.

lem-sfb-conjugate-projective-generic-closure vs lem-weil-pbc-closed-subset-closed-subscheme: It only provides some closed subscheme on a closed subset; the new node constructs P and its action and determines C_K = Spec M.

lem-sfb-conjugate-projective-generic-closure vs lem-weil-pbc-reduced-induced-closed-subscheme: It supplies the reduced induced structure and uniqueness (an ingredient cited in stmt_deps), not projectivity, the conjugate action or the residue-field calculation.

lem-sfb-conjugate-projective-generic-closure vs lem-weil-pbc-reduction-universal-homeomorphism: It concerns reduction of an entire scheme and universal homeomorphisms, not the generic graph in a conjugate product.

lem-sfb-conjugate-projective-generic-closure vs lem-weil-pbc-coherent-integral-generic-lattice-extension: It extends a coherent generic lattice; the new node instead constructs a scheme with a specified finite generic field and group action.

lem-sfb-conjugate-projective-generic-closure vs def-weil-pbc-reduced-normalization: It defines componentwise normalization, whereas the new node constructs a reduced closure and does not normalize it.

lem-sfb-conjugate-projective-generic-closure vs def-weil-pbc-closed-subset-proper-over-base: It defines support proper over a base; it does not construct projective graph closures or actions.

lem-sfb-conjugate-projective-generic-closure vs lem-weil-pbc-affine-open-section-vanishing-prime: It identifies vanishing germs and basic-open coordinate rings; it does not assert the equivariant generic graph construction.

lem-sfb-conjugate-projective-generic-closure vs def-weil-pbc-scheme-reduction: It defines reduction of a scheme by its nilradical, with no graph product or field calculation.

lem-sfb-conjugate-projective-generic-closure vs lem-sc-closed-subset-qc-ideal: It produces a quasi-coherent ideal defining a given closed set; it does not give the conjugate product, its action or its generic fibre.

lem-sfb-conjugate-projective-generic-closure vs lem-sfb-semilinear-equivariant-chow-modification: It gives an equivariant birational modification of a scheme already carrying an action. Here Y carries no action, the supplied B can have an arbitrary finite generic extension M/K, and the graph has function field M.

lem-sfb-conjugate-projective-generic-closure vs lem-chow-segre: It embeds a product of projective spaces. The new node also constructs the conjugate action, q and the reduced graph with C_K = Spec M.

lem-sfb-conjugate-projective-generic-closure vs lem-per-equivariant-projective-envelope: It compactifies an existing action by automorphisms over an affine base. The new node starts with Y without an action and uses an additional finite generic model B and semilinear base action.

lem-sfb-equivariant-projective-model-normalization vs lem-sbc-normal-finite-stage-universal: It constructs a universal finite normal approximation stage, not an equivariant normalization of a projective C with finite generic fibre over S.

lem-sfb-equivariant-projective-model-normalization vs lem-sbc-normalization-dominant-lift: It gives one unique dominant lift to normalization. The new node additionally establishes the lifted group action, preserved generic fibre and global projective alteration over S.

lem-sfb-equivariant-projective-model-normalization vs lem-trf-normalized-blowup-calculus: It treats normalized blowups of ideals on Q-schemes and their universal property, not arbitrary projective generic models over any field.

lem-sfb-equivariant-projective-model-normalization vs lem-sfb-componentwise-normalization-generic-properties: It gives componentwise normality, integralness and generic-point fibres, not a finite equivariant projective alteration over another projective scheme.

lem-sfb-equivariant-projective-model-normalization vs lem-sfb-component-dominant-normalization-lift: It is a universal property for one component-dominant map to normalization; it does not assert group laws, finiteness or projective alteration properties.

lem-sfb-equivariant-projective-model-normalization vs lem-sfb-integral-normal-generic-recognition: It recognizes a supplied integral normal generic-field isomorphism as a normalization; the new node constructs normalization and its equivariant generically finite map.

lem-sfb-equivariant-projective-model-normalization vs lem-sfb-normalization-integral-birational-factor: It factors normalization through an integral birational intermediate scheme; it has no semilinear group action or relative projectivity/alteration conclusion.

lem-sfb-equivariant-projective-model-normalization vs lem-per-componentwise-normalization-properties: It supplies componentwise normalization properties and recognition. It does not state the action on normalization or the globally projective alteration over S with generic field M.

lem-sfb-equivariant-projective-model-normalization vs lem-per-integral-etale-chart-flatification: It flatifies finitely many proper covers of etale charts over a quasi-excellent base; no such chart family or flatification is required or asserted here.

lem-sfb-equivariant-projective-model-normalization vs lem-per-excellent-normalized-blowup-tower: It treats towers of normalized point blowups on excellent schemes and projectivity in the projective-bundle sense, whereas the new node treats an arbitrary supplied projective generic model with global projective embedding over S.

lem-sfb-equivariant-projective-model-normalization vs lem-per-excellent-normalization-preparation: It proves finite normalization and a good dense open for excellent schemes, without the lifted action, given finite extension over S or global relative embedding.

lem-sfb-equivariant-projective-model-normalization vs lem-per-finite-curve-normalization-regular: It deduces regularity in dimension one under finite normalization; the new node permits arbitrary dimension and claims only normality with an equivariant alteration.

lem-sfb-equivariant-projective-model-normalization vs lem-per-normal-projective-compactification: It compactifies schemes over a complete strictly henselian mixed-characteristic trait and may change the trait; the new node is over an arbitrary field and normalizes a supplied projective model.

lem-sfb-equivariant-projective-model-normalization vs lem-weil-pbc-reduced-normalization-over-normal-reduction: It compares normalization with a normal reduction on an open, without constructing the lifted group action or alteration over S.

lem-sfb-equivariant-projective-model-normalization vs lem-weil-pbc-reduced-algebraic-normalization-field-change: It gives normalization under separable changes of the ground field; it does not give the semilinear action and generically finite map over an independent projective S.

lem-sfb-equivariant-projective-model-normalization vs lem-trf-fibre-degree-ample-criterion: It tests ampleness by degrees on normalized curve components, not equivariant normalization of projective generic models.

lem-sfb-equivariant-projective-model-normalization vs lem-weil-pbc-field-curve-normalization-good-open: It gives a thickening on a dense open for a chosen family of component normalizations; the new node gives an action and a globally projective alteration to S.

lem-sfb-equivariant-projective-model-normalization vs lem-weil-pbc-reduced-curve-normalization: It gives a smooth normalization modification in dimension at most one over an algebraically closed field; here dimensions and ground fields are arbitrary and the essential conclusion concerns the map to S.

lem-sfb-equivariant-projective-model-normalization vs lem-weil-pbc-normalization-projective-components: It proves absolute projectivity of componentwise normalization (a useful ingredient), but not an equivariant action, preservation of a specified C_K or a globally projective alteration to S.

lem-sfb-finite-semilinear-field-envelope vs lem-coef-infinity-kan-mapping-restriction: It concerns Kan-extension mapping spaces, not fields or compatible automorphism groups; the source-tag text overlap has no mathematical relevance.

lem-sfb-finite-semilinear-field-envelope vs lem-coef-full-subcategory-kan-trivial-restriction: It concerns simplicial restriction of natural transformations, not field extensions or finite semilinear envelopes.

lem-sfb-finite-semilinear-field-envelope vs lem-weil-pbc-normal-extension-purely-inseparable-then-galois: It decomposes a supplied normal field extension using its fixed field. The new node first constructs a finite normal envelope over K^H containing arbitrary L and the compatible-pair group retaining H.

lem-sfb-finite-semilinear-field-envelope vs lem-weil-pbc-normal-extension-fixed-field-separable-normal: It proves the extension over the fixed field is separable and normal; it does not construct M or the group surjecting onto a possibly nonfaithful H.

lem-sfb-finite-semilinear-field-envelope vs lem-weil-pbc-normal-extension-fixed-field-purely-inseparable: It proves purely inseparable fixed fields for a given normal extension, an ingredient; the new node constructs the envelope and its surjective compatible-pair group.

lem-sfb-finite-semilinear-field-envelope vs lem-weil-pbc-finite-set-in-finite-galois-subextension: It places a finite subset inside a Galois subextension of an already Galois ambient field; it has neither a possibly inseparable L/K nor the extension of the given H.

lem-sfb-finite-semilinear-field-envelope vs lem-weil-pbc-separable-split-purely-inseparable-residue-fields: It splits residue-field extensions after separable base change; it does not construct a compatible group acting on a finite normal overfield of L.

lem-sfb-finite-semilinear-field-envelope vs lem-weil-pbc-finite-extension-in-finite-normal-extension: It supplies a finite normal overfield of L/K, without compatibility with all H, a surjective group of pairs or the strengthened separable branch.

lem-sfb-finite-semilinear-field-envelope vs lem-weil-pbc-finite-galois-receiving-separable-extensions: It supplies a common Galois receiving field for finite separable extensions. The new node also handles inseparable L/K and retains a given action through a surjective group.

lem-sfb-finite-semilinear-field-envelope vs lem-wf-finite-field-action-fixed-degree: It computes the degree and Galois property for a finite faithful action on an existing field. The new node extends a possibly nonfaithful action across prescribed L/K.

lem-sfb-finite-semilinear-field-envelope vs lem-sfb-invariant-separating-parameters: It constructs invariant separating transcendence parameters in a geometrically integral function field, not finite normal envelopes containing a prescribed extension.

lem-sfb-finite-semilinear-field-envelope vs lem-weil-pbc-distinct-linear-factors-separable: It proves polynomial separability from distinct linear factors; it constructs no field envelope or compatible automorphism group.

lem-sfb-finite-semilinear-field-envelope vs lem-sfb-normal-intermediate-isomorphism-lifts: It extends one intermediate-field isomorphism in an already normal ambient extension. The new node constructs that finite ambient extension over K^H and the group of all compatible pairs with its fixed-field conclusions.

lem-sfb-finite-semilinear-field-envelope vs lem-dl-a1-normal-finite-aut-separable-subfield: It proves finiteness of a separable subfield under finiteness of automorphisms, not construction of a finite envelope and a surjection to H.

lem-sfb-finite-semilinear-field-envelope vs lem-weil-pbc-normal-extension-conjugate-by-automorphism: It moves one root to another by an automorphism; it does not construct the envelope or retain all of a given H.

lem-sfb-finite-semilinear-field-envelope vs lem-weil-pbc-normal-subextension-automorphism-extends: It extends one automorphism of a normal subextension, not the envelope plus finite compatible-pair group and invariant field.

lem-sfb-semilinear-finite-normalization-model vs lem-sbc-dvr-galois-components-stalk-factor: It describes DVR normalization stalks of specified Galois components after a root base change, not a semilinear normalization model of an arbitrary projective S.

lem-sfb-semilinear-finite-normalization-model vs lem-sbc-normalization-algclosed-field: It normalizes an affine scheme in an algebraically closed field, without finite degree, projectivity or a compatible group action.

lem-sfb-semilinear-finite-normalization-model vs lem-sbc-reduced-artinian-tensor-normalization-charts: It supplies affine normalization charts for reduced Artinian tensor products, not finite semilinear projective models.

lem-sfb-semilinear-finite-normalization-model vs lem-sbc-reduced-artinian-affine-normalization-charts: It supplies charts in normalization of a reduced Artinian algebra, without a prescribed global semilinear action or projectivity.

lem-sfb-semilinear-finite-normalization-model vs def-sfb-moduli-chart-normalization: It defines a moduli-chart-normalization condition, not a theorem about finite normalization of projective integral schemes.

lem-sfb-semilinear-finite-normalization-model vs lem-weil-pbc-universally-closed-global-sections-integral: It proves a global-sections ring map integral under universal closedness, not a finite projective normalization with group action.

lem-sfb-semilinear-finite-normalization-model vs lem-weil-pbc-relative-normalization: It constructs general relative normalization and its affine charts, but does not state finiteness in M/K, normality/projectivity of B or a lifted semilinear action.

lem-sfb-semilinear-finite-normalization-model vs lem-weil-pbc-normalization-in-residue-field-extension: It gives a normal integral relative normalization with prescribed generic field; the new node adds finite type/projectivity, finiteness and the unique compatible semilinear group action on this model.

lem-sfb-semilinear-finite-normalization-model vs lem-sbc-finite-normal-dense-open-comparison: It compares an existing normal finite cover with an existing etale cover across a dense open; no etale cover is assumed in the new node, which allows purely inseparable M/K.

lem-sfb-semilinear-finite-normalization-model vs lem-sbc-normalization-dense-open: It says normalization of a normal base in a dense open is the base; the new node normalizes in an arbitrary finite M/K and carries its semilinear action.

lem-sfb-semilinear-finite-normalization-model vs lem-sbc-normalization-stalk-field-coproduct: It compares local relative normalization with a coproduct of integral closures; it neither proves the global finite projective model nor carries an action.

lem-sfb-semilinear-finite-normalization-model vs lem-sbc-punctured-dvr-normalization-stalk-domain: It proves only that a punctured-DVR normalization stalk is a domain, not the global semilinear model.

lem-sfb-semilinear-finite-normalization-model vs lem-sbc-punctured-dvr-normalization-stalk-torsion-free: It proves torsion freeness of specified normalization stalks over DVRs, without the global projective construction or action.

lem-sfb-semilinear-finite-normalization-model vs lem-sbc-stalk-normalization-formal-punctured-restriction: It studies normalization over a formal punctured neighborhood and constant etale covers, not a projective normalization in a prescribed finite function-field extension.

lem-sfb-semilinear-finite-normalization-model vs lem-sbc-normalization-stalk-base-change: It asserts normalization commutes with stalk base change, an ingredient for fibre computations; it does not give finiteness, projectivity or lifted group actions.

lem-sfb-semilinear-finite-normalization-model vs lem-sbc-relative-normalization-universal-property: It gives a universal property for relative normalization, without the finite-degree projective scheme and semilinear action conclusions.

lem-sfb-semilinear-finite-normalization-model vs lem-sbc-finite-affine-normalization-coproduct: It compares normalization with a finite coproduct of affine normalizations; it does not assert the semilinear projective normalization model.

lem-sfb-semilinear-finite-normalization-model vs lem-sbc-stalk-normalization-dense-part: It proves density of a normalized finite-etale cover on a local base change; the new node allows inseparable finite extensions and constructs a global projective model with action.

lem-sfb-semilinear-finite-normalization-model vs lem-sbc-stalk-normalization-generic-comparison: It compares normalization of a generic etale torsor with a stalkwise model near a DVR; it does not construct the arbitrary finite semilinear extension model over projective S.

lem-sfb-semilinear-finite-normalization-model vs lem-sbc-punctured-dvr-normalization-stalk-torsion-free-injective: It proves injectivity of a map to a normalization stalk over a DVR, not the global finite normalization/action statement.

lem-sfb-semilinear-finite-normalization-model vs lem-sbc-stalk-normalization-normal-dense: It proves normality and dense-open properties for a local base change of a finite-etale cover of a smooth scheme. The new node has neither a smooth scheme nor an etale restriction hypothesis and specifies finite M/K plus its group action.

lem-sfb-semilinear-finite-normalization-model vs lem-per-generic-finite-normal-trivialization: It trivializes a constructible sheaf by some finite normal cover of an excellent base; it does not realize a prescribed M/K or extend a supplied semilinear action.

lem-sfb-semilinear-finite-normalization-model vs lem-weil-pbc-normalization-projective-components: It concerns absolute componentwise normalization in the same function fields. The new node normalizes S in an arbitrary finite extension M/K and specifies a compatible action on M and B.

Additional close statements read: `lem-sfb-finite-normal-relative-curve-model` assumes relative curves and separable extensions E/K, unlike the arbitrary finite M/K in the new finite-normalization node; `lem-per-projective-galois-alteration-envelope` is an entire Galois-envelope theorem in a different setup, not any of the four strictly smaller construction stages here. The new graph statement cannot be replaced by equivariant Chow because its Y has no group action and its function field must be the separately prescribed M.

lem-sfb-conjugate-projective-generic-closure vs lem-weil-pbc-integral-chow-relatively-ample: Integral Chow supplies the birational projective-space immersion used to prepare Y. It does not construct the conjugate product with B, its semilinear action, or the reduced graph whose generic field is the prescribed M. The new node includes this preparation as the first part of that strictly smaller generic-graph construction.


lem-sfb-finite-semilinear-field-envelope vs lem-sfb-common-normal-compatible-groups: The current common-normal statement amalgamates a finite family of fields over a supplied fixed base and gives compatible subgroups of a product group. It does not supply an overfield containing a prescribed further extension L/K of the field carrying H, does not construct the fixed base F = K^H, and has no separable/Galois choice or fixed field of the kernel over K. The retained envelope requires all these for one compatible-pair group, so it is not a special case of the simultaneous-constants statement.

lem-sfb-semilinear-finite-normalization-model vs lem-sfb-cover-nested-cartier-preparation: Boundary preparation starts from a finite etale cover of one of two dense opens and chooses its generic residue field, then modifies its normalization to make two boundaries Cartier. It has no prescribed arbitrary finite extension M/K, projective normalization conclusion, group action, inverse-pullback compatibility, or unique semilinear lift. The retained node concerns the finite projective model and its action, not either boundary modification.

lem-sfb-semilinear-finite-normalization-model vs lem-sfb-finite-normal-cover-normalization: The current recognition statement starts with an already supplied finite surjective normal cover Z to X and identifies it with the normalization in its function field. It does not construct a finite normalization from an arbitrary finite extension, prove its projectivity, or extend a compatible semilinear group action uniquely. Those are the conclusions required by the retained model node.

lem-sfb-finite-semilinear-field-envelope vs lem-wf-henselian-residue-lift-diagram: the former constructs a finite normal field envelope of L/K with a possibly nonfaithful semilinear H-action, a surjective compatible-pair group and its purely inseparable invariant field; the latter constructs finite etale lifts over a henselian local ring of residue-field subextensions and proves cofinality of the Galois lift subdiagram. Normal closure (09DT) is only a shared ingredient, and neither statement specializes to the other.

lem-sfb-semilinear-finite-normalization-model vs lem-sfb-normalization-generic-residue-affine-charts: The existing node computes affine charts and their restriction maps for absolute componentwise normalization in the scheme's own generic residue fields, without finiteness assumptions; the new node normalizes an integral projective finite-type S in a prescribed finite extension M/k(S), proves it finite and projective, and uniquely lifts a compatible semilinear group action on S and M. Absolute affine charts do not assert the extension-field model, finiteness, projectivity or lifted action, so the new statement is not a specialization.
