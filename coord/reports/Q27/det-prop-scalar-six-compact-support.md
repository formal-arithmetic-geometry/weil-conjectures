## Worker report

Repair of the 2026-10-22 mandatory re-split of det-prop-scalar-six-compact-support. Only stage 1; no Lean writing, compiler, Lake, repository writes or agents. The dispatched sandbox initially contained only brief markers, so I copied the current repository item as the retained returned head. It contains exactly the seven steps described by the return, with their historical Mathlib searches, blueprint bindings, and earlier review metadata. Those historical fields are retained. No prior sandbox report or search log existed; the current searches.jsonl contains only searches actually run during this repair.

## Files written

- dag/nodes/sec-six-functors-basics/det-prop-scalar-six-compact-support.json: statement unchanged, five-step assembly, 2365 characters, three new obligations.
- dag/nodes/sec-six-functors-basics/lem-sfb-scalar-refinement-closure-square.json: statement-only, unsplit; no Mathlib match. Dense-refinement and schematic-closure coefficient identities, including the pushed square.
- dag/nodes/sec-six-functors-basics/lem-sfb-scalar-proper-open-interchange-square.json: statement-only, unsplit; no Mathlib match. Normalized proper/open coefficient square and its restricted value.
- dag/nodes/sec-six-functors-basics/lem-sfb-scalar-composite-model-pasting.json: statement-only, unsplit; no Mathlib match. Typed equation on specified composite compactification models, with the canonical model compositor.
- report.md and citations.json. returned-proof.json retains a sandbox-only verbatim copy of the seven returned proof steps. The argument is also reproduced below in this delivered report.

## Attachments

None. I searched WeilConjectures for the exact blueprint tag and for coefficient/refinement/interchange and compact-support names. CompactSupportCoefficientChange.lean supplies finite quotient coefficients on the small etale site; it does not cover the listed condensed coefficients or every independence/composition clause. Ordinary LowerShriekCoherence and LowerShriekComposition declarations likewise do not assert the coefficient squares. Thus these are not exact attachments. No Mathlib declaration is treated as a project attachment.

## WANTED

None. The current main-20261015 statement and proof, the chapter and unit records, and all cited node statements are locally available. No SGA source is used.

## Return repaired

The sole numbered requirement is to spread the returned 7751-character proof among at least two comparable independently claimable arguments, keeping the exact item statement and at most 3000 characters in its assembly. Three new nodes are delivered, all status unsplit, with no proof steps, empty proof_deps and null proof_origin. They have self-contained hypotheses and typed derived-category equations, not degreewise substitutes. Their common coefficient/category setup is repeated so that each can be assigned alone.

Returned step 1 remains assembly step 1: Dctf preservation for j_! comes from coherence-single on (j,id), followed by proper and open coefficient isomorphisms and the target-category checks. Returned step 2 remains assembly step 2: open-unit and identity-proper comparison normalizations are elementary triangle-identity calculations.

Returned step 3 becomes the refinement/closure node's dense-refinement equation and its proper pushforward equation. Returned step 4 becomes its schematic-closure case. These carry both the uniqueness-on-the-open argument and the naturality/proper-composition pasting, not just a renamed independence clause. Returned step 5 remains assembly step 4: normalize, take common refinements, verify inverse-image-of-X by the clopen-section statement and density, and use transitivity/cocycle. Returned step 6 becomes the separate proper/open interchange node. Returned step 7 becomes the separate fixed-model pasting node; the final passage from its constructed composite model to any chosen model stays in assembly step 5. Nothing in the old argument is omitted; the full original follows below as the future workers' proof plans.

The three nodes ask different tasks: compare an endomorphism of an open model under a proper map (including its closed normalization); compare a proper/open interchange with nonidentity restricted map gamma_p; and perform the ordered compositor paste using those equations. None restates the whole item. The fixed-model paste does not assert independence, and the refinement square does not assert general composition compatibility. Their returned argument sizes are about 2465, 1226 and 1291 characters; the first combines the two versions of one restriction argument, and none contains the whole proof.

## Searches and existing-node audit

I read the results of all msearch.py calls and selected actual queries verbatim into the nodes' mathlib_searches. For every new node the records contain LeanSearch, LeanFinder (two distinct natural-language phrasings), Loogle, and grep, with actual returned names and scope. All services answered; none is recorded as unavailable. The generic mate/conjugate/naturality declarations do not state the geometric equations in ordinary condensed module-object derived categories, so their use would still require the displayed geometric restriction and normalization arguments. The first scalar-model-isomorphism search was exploratory and is not used to create an unnecessary new node: that argument stays in the item. One shell command containing an unquoted apostrophe failed before running msearch; it is not recorded as a search. Its corrected natural-language query ran and is in searches.jsonl.

Whole-DAG searches inspected titles and statement fields, not just filenames. I searched blueprint_refs.py ancestor for the item and search for coefficient refinement, coefficient interchange, coefficient normalization, compactification coefficient, proper open coefficient, coefficient comparison compactly, composition coefficient, and open comparison identity. No existing blueprint node states one of the three extracted equations in this coefficient/category setting. The item already records det-sfb-coefficient-comparisons-compact-support as same_as: that node states the whole item, not one of these intermediate equations. The new from.node fields all name this imported item with via=[] and point precisely to Independence/Composition and the returned step numbers. No existing record is edited except the item.

## Not duplicates

lem-sfb-scalar-refinement-closure-square vs lem-sf-proper-open-coefficient-refinement: the latter treats finite-ring ordinary small-etale bounded-below complexes and a possibly noncartesian clopen refinement mate; the new node treats all listed condensed coefficients on small pro-etale sites and Dctf, with inverse-image-open equality, including schematic-closure normalization and the proper-pushed coefficient square. It is not a one-line specialization across those coefficient categories.

lem-sfb-scalar-refinement-closure-square vs det-sf-comp-coherence-refinement: that node constructs and characterizes the refinement map and its transitivity; it does not state compatibility with coefficient change. The same distinction holds against sk-lem-nagata-density-normalization, which supplies the coefficient-independent closure identification.

lem-sfb-scalar-refinement-closure-square vs lem-pur-compact-support-strict-scalar-refinement: that node concerns finite coefficient-field inclusions, strict integral reduction towers and their total-limit comparison; the new node uses ordinary pulled-back condensed coefficient module categories and all listed maps, including arbitrary nonflat finite maps.

lem-sfb-scalar-proper-open-interchange-square vs det-sf-comp-composition-interchange: the old node gives the geometry, uniqueness and invertibility of iota; the new equation compares its two coefficient-ring instances. Its statement was opened and it does not assert that equation.

lem-sfb-scalar-proper-open-interchange-square vs lem-sp-proper-open-coefficient-mate: that node gives finite-ring etale/pro-etale origin transport squares; it does not cover the arbitrary standing field and listed condensed integral, localized and algebraically closed coefficient maps here.

lem-sfb-scalar-proper-open-interchange-square vs lem-sf-proper-open-tensor-compatibility: that node concerns finite coefficients or strict semilinear systems over the algebraic closure of a finite field, and a tensor/projection formula equation with a second tensor argument. It is not the varying condensed-ring gamma/delta equation here.

lem-sfb-scalar-composite-model-pasting vs det-sfb-coefficient-comparisons-compact-support: the latter is a statement of the entire target including arbitrary model independence; the new node only gives the explicit paste on fixed f,g,ip models and deliberately makes no assertion comparing arbitrary gf models. It is the returned compositor calculation, not a replacement for the target.

lem-sfb-scalar-composite-model-pasting vs lem-pur-compact-support-strict-scalar-composition: the latter composes coefficient-field inclusions on strict derived towers; the new node composes scheme morphisms in ordinary condensed coefficient categories. The word composition has different arguments in these statements.

lem-sfb-scalar-refinement-closure-square vs lem-pur-finite-free-compact-scalar: that node assumes finite-free maps of finite rings and ordinary finite-coefficient sites; the new square includes nonflat finite-ring maps and all the listed topological condensed coefficient maps.

## Review by Q27

I read the current blueprint item statement and the full Isomorphism, Independence, Composition proof in literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-compact-support.md and .proof.md, and the unit's Compactly supported direct image paragraph. The item statement remains byte-for-byte the base statement. All three new statements are precise obligations in those paragraphs, with the refinements/closure details taken from the retained returned proof rather than from a new source route. No chapter/unit statement changes, extra flatness assumptions, completed tensor replacements, or weakening of coefficient scope occur.

Assembly step 1 cites coherence-single for the compactification of j with proper factor id; its statement explicitly sends Dctf to Dctf, so finite Tor amplitude is included. The direct-image statement explicitly makes gamma an isomorphism on those inputs; pullback (2) explicitly supplies the open comparison. Existence (2) and ctf (3) give the exact target category assertions. Both Lambda and Lambda' are admissible under the listed maps. I checked these clauses in the actual node statements, not in their proofs.

Assembly step 2 uses the open comparison's conjugate definition and the unit/pullback/counit definition of gamma. Pullback (1) supplies its canonical identity normalization. Expanding and cancelling adjunction triangles is elementary and is the only elementary step. It creates no separate lemma node merely to package that cancellation.

Assembly step 3 uses exactly the two cases and pushed coefficient square stated by lem-sfb-scalar-refinement-closure-square. The finite-type-over-Noetherian statement supplies Noetherianity (the field base is Noetherian); density-normalization explicitly supplies both j_! = i_*j_0! and the proper-pushforward identification. A closed schematic-closure immersion is not silently treated as a dense-to-dense refinement: case (b) states its own hypothesis and normalization. Inverse image of the open X under its closure inclusion is X.

Assembly step 4 cites the full cofiltered common-refinement statement, then the proper-open-section statement: the section is an open-and-closed immersion in the inverse image of X. The common model is normalized first, so X is dense in it and in that open inverse image; the clopen component is the whole inverse image. This verifies the exact extra hypothesis of the dense-refinement node, and equality is of open subschemes. Coherence-refinement (2),(3) states invertibility and transitivity of the actual maps, while coherence-cocycle explicitly states independence of the common refinement and the cocycle. Thus the coefficient squares from step 3 paste to the canonical comparison, including arbitrary nondense original models. No unproved coefficient compatibility is taken from a coefficient-independent coherence statement.

Assembly step 5 uses the newly stated interchange coefficient equation on A=j_!K. The new statement has precisely the proper p, open i, dense compactification ip=rj' hypotheses and the displayed source/target. Step 1 verifies its finite Tor input. The fixed-model pasting node states the compositor and its typed equation on those very same models. Applying it proves the equation on (j'j,qr); step 4 supplies the identification with the chosen gf model. These are sufficient for the item's composition assertion. The new nodes need not be proved now: each is a statement-only task for another worker, as the return expressly requests.

For the refinement/closure node I checked K, T_XK, j_!K and j'_!K lie in the finite-Tor categories where the proper coefficient comparisons apply. Its first equation has source T_Zj_!K and target Rh_*j'_!T_XK; its second has source T_YRp_*j_!K and target R(ph)_*j'_!T_XK. The schematic-closure case has the restriction-normalized e_i supplied by density-normalization and the open adjunction. For the interchange node the open restriction of gamma_r is gamma_p by the existing lem-sfb-proper-direct-image-coefficient-restriction; I read that equation, its properness and finite-Tor hypotheses, and its identity-square normalization. Both sides then restrict to gamma_p, and uniqueness applies after identifying the source via the invertible proper comparison. The object A need not be an extension by zero, so the new statement exposes a reusable argument.

For the paste node I checked the directions: alpha maps H_g H_f to H_gf; C maps T H to H T; the left side and all three factors on the right both run from T_S H_g H_f K to H_gf T_XK. Gamma_q naturality, proper composition and open-composition of delta are explicitly the pasting inputs; neither parent compactification independence nor the parent composition assertion is assumed. The report's retained step 7 gives that full argument for its future worker.

Small cases tested in words: K=0 or A=0 gives zero-object identities; empty X gives the zero comparison and closure of the empty open; h=id gives equality of the same open coefficient map; a nondense model with a disjoint proper component is removed by closure with extension by zero zero on that component; p=id or i=id makes interchange the open/proper unit normalization; f or g identity collapses the model paste to the corresponding proper/open identity. Arbitrary nonflat finite maps are allowed only on Dctf, so no false boundedness claim for F_l over Z/l^2 is inserted. No conclusion about arbitrary condensed coefficient maps is made: each new node repeats the full listed range. The new equations are derived-category morphism equalities and not a per-degree weakening.

The return required new independent tasks rather than shortening the existing argument. I corrected this by extracting three concrete equations and preserving the whole original proof below, including its restriction, uniqueness, density and pasting arguments. The remaining assembly is below 3000 characters and every step below 2000. No statement dispute or unrepairable mathematical point was found. Mathlib/DAG/blueprint duplicates were checked as described above; the new nodes carry statements only, complete source places, real search records and no proof sketch in their statement. All cited statements have been opened and their exact text is quoted in citations.json. Existing cross-unit tool uses are retained from the base and are still used for their original generic purposes; no new maintainer tool_uses field is introduced.

## Retained returned argument and assignment to future workers

The following seven steps are copied verbatim from the returned repository node. They are proof plans in this report, not proof steps on the new unsplit nodes. Steps 1,2,5 remain in the item assembly; 3,4 are assigned to the refinement/closure square, 6 to the interchange square, and 7 to the fixed-model pasting square (with its final arbitrary-model passage in the parent). This preserves every argument of the original delivery for the workers who will split the new tasks.

### Returned step 1

Write $T^V=(-)_{\Lambda'}$ and write $\delta_{a,M}:T(a_!M)\xrightarrow{\sim}a_!T(M)$ for [det-prop-scalar-six-pullback] (2). All schemes appearing in a compactification are standing schemes, hence qcqs ([sk-def-sfb-dc-setting]); its open immersion is quasi-compact by the definition of compactification [sk-def-nagata-sketch-data]. Apply [det-sf-comp-coherence-single] to the compactification $X\xrightarrow{j}\overline X\xrightarrow{\mathrm{id}}\overline X$ of $j$: it gives $j_!K\in\Dctf(\overline X,\Lambda)$, including finite Tor amplitude. Thus [det-prop-scalar-six-direct-image] (1) for $p$ makes $\gamma_{p,j_!K}$ an isomorphism. Composing with $Rp_*\delta_{j,K}$ gives the displayed $\gamma^!_{f,K}$. By [sk-thm-existence] (2), $Rf_!K\in\Dctf(Y,\Lambda)$; [det-prop-scalar-six-ctf] (3) gives both $T^Y Rf_!K\in\Dctf(Y,\Lambda')$ and $T^XK\in\Dctf(X,\Lambda')$. Applying existence again to $T^XK$ puts $Rf_!T^XK$ in the same target category.

Cited statements: sk-def-sfb-dc-setting, det-sf-comp-coherence-single, det-prop-scalar-six-direct-image, det-prop-scalar-six-pullback, sk-thm-existence, det-prop-scalar-six-ctf, sk-def-nagata-sketch-data.

### Returned step 2

We use the normalization of the open comparisons explicitly. Put $T^V=(-)_{\Lambda'}$ and $\delta_{a,M}:T(a_!M)\xrightarrow{\sim}a_!T(M)$. For an open $a$, [def-sfb-derived-open-immersion-shriek-iso] defines this as the conjugate of the restriction-of-scalars/pullback comparison. Expanding the conjugate and restricting by $a^*$, its unit and counit cancel by the triangle identities. Under the open-unit identifications $a^*a_!\simeq\mathrm{id}$, its restriction is therefore the coefficient comparison for the identity pullback, hence the identity under [det-prop-scalar-six-pullback] (1). Also $\gamma_{\mathrm{id},M}=\mathrm{id}$: in its unit/pullback/counit definition [det-prop-scalar-six-direct-image], the identity-pullback comparison and the adjunction triangle identities cancel all three factors.

Cited statements: def-sfb-derived-open-immersion-shriek-iso, det-prop-scalar-six-pullback, det-prop-scalar-six-direct-image.

### Returned step 3

Consider dense compactifications $c=(j:X\to Z,p:Z\to Y)$ and $c'=(j':X\to Z',p':Z'\to Y)$ and a proper refinement $h:Z'\to Z$ with $p'=ph$ and $h^{-1}(X)=X$. Let $e_{h,K}:j_!K\to Rh_*j'_!K$ be [det-sf-comp-coherence-refinement]. We prove
$$Rh_*\delta_{j',K}\circ\gamma_{h,j'_!K}\circ T_Z(e_{h,K})=e_{h,T_XK}\circ\delta_{j,K}.$$
The source is $T_Zj_!K\simeq j_!T_XK$, and the target restricts to $T_XK$. By the adjunction and uniqueness in [det-sf-comp-coherence-refinement] (1), it suffices to restrict to $X$. Apply [lem-sfb-proper-direct-image-coefficient-restriction] to $h$ and the open $X\subset Z$, with $M=j'_!K$, which is in $\Dctf$ by step 1 applied to $j'$. It identifies the restricted $\gamma_h$ with $\gamma_{\mathrm{id},K}=\mathrm{id}$. The restrictions of both $e$ maps are identities by the refinement lemma, and those of the $\delta$ maps are identities by step 2. Both sides restrict to $\mathrm{id}_{T_XK}$, proving the equation. Put $\phi_{h,K}=Rp_*e_{h,K}$. Naturality and the proper-composition equation in [det-prop-scalar-six-direct-image] (2), followed by the equation just proved, give
$$\phi_{h,T_XK}\circ\gamma^{!,c}_{f,K}=\gamma^{!,c'}_{f,K}\circ T_Y(\phi_{h,K}).$$

Cited statements: det-sf-comp-coherence-refinement, lem-sfb-proper-direct-image-coefficient-restriction, det-prop-scalar-six-direct-image.

### Returned step 4

An arbitrary compactification can first be replaced by its schematic closure of $X$. Its ambient scheme is Noetherian by [lem-weil-pbc-finite-type-over-noetherian], since it is finite type over the field $k$. For the closed inclusion $i:Z_0\to Z$ and induced dense open $j_0:X\to Z_0$, [sk-lem-nagata-density-normalization] identifies $j_!K\simeq Ri_*j_{0!}K$ and their proper pushforwards. Use the canonical identification normalized by its restriction to $X$; it is the map $e_i$ adjoint to the open identity under $j_!\dashv j^*$ of [def-sfb-derived-open-immersion-shriek-iso]. The restriction of its target is $K$ by the density-normalization identification. The calculation of step 3 uses density only to have the stated refinement map and its open identification; for this closed $i$, those are instead supplied by density normalization and this adjunction. Its coefficient equation follows by exactly the same restriction calculation: apply [lem-sfb-proper-direct-image-coefficient-restriction] to $i$ over $X$, where its base change is the identity, and use step 2 for $\delta_j,\delta_{j_0}$. Applying $Rp_*$ and the naturality/composition equation of [det-prop-scalar-six-direct-image] (2) gives the coefficient square for the normalization isomorphism as well.

Cited statements: lem-weil-pbc-finite-type-over-noetherian, sk-lem-nagata-density-normalization, def-sfb-derived-open-immersion-shriek-iso, lem-sfb-proper-direct-image-coefficient-restriction, det-prop-scalar-six-direct-image.

### Returned step 5

For two dense compactifications choose a common refinement by [prop-compactification-refinement], and normalize that refinement by step 4. All these schemes and maps satisfy the standing finite-type and separated hypotheses. For either proper map $h:Z_3\to Z_a$, [lem-weil-pbc-proper-open-section] says the copy of $X$ is open and closed in $h^{-1}(X)$. Density in $Z_3$ implies density in this open inverse image; closedness then implies $h^{-1}(X)=X$ as open subschemes. Thus step 3 applies to both refinement maps. They are isomorphisms and transitive by [det-sf-comp-coherence-refinement] (2),(3). The common-refinement comparisons are independent of the choice and satisfy the cocycle identity by [det-sf-comp-coherence-cocycle]. The two commuting coefficient squares of step 3 therefore give the commuting square for the canonical comparison between the two dense models. Step 4 supplies the squares for normalizing either original model. Pasting these squares proves independence for all compactifications.

Cited statements: prop-compactification-refinement, lem-weil-pbc-proper-open-section, det-sf-comp-coherence-refinement, det-sf-comp-coherence-cocycle.

### Returned step 6

Choose compactifications $f=pj$ and $g=qi$, with $j:X\to\overline X$ and $i:Y\to\overline Y$ open. Compactify $ip$ densely as $\overline X\xrightarrow{j'}W\xrightarrow{r}\overline Y$ and put $A=j_!K$. By [det-sf-comp-composition-interchange], $r^{-1}(Y)=\overline X$, $r|_{\overline X}=p$, and there is a unique map $\iota_A:i_!Rp_*A\to Rr_*j'_!A$ restricting to $\mathrm{id}_{Rp_*A}$; it is an isomorphism for $A\in\Dctf$. We claim
$$Rr_*\delta_{j',A}\circ\gamma_{r,j'_!A}\circ T_{\overline Y}(\iota_A)=\iota_{T_{\overline X}A}\circ i_!\gamma_{p,A}\circ\delta_{i,Rp_*A}.$$
Restrict to $Y$. By [lem-sfb-proper-direct-image-coefficient-restriction] for $r$ and $Y\subset\overline Y$, the restricted proper comparison is $\gamma_{p,A}$. The $\iota$ restrictions are identities by the interchange statement; the $\delta$ restrictions are identities by step 2. Both sides consequently restrict to $\gamma_{p,A}$. This is an isomorphism by [det-prop-scalar-six-direct-image] (1), since $A\in\Dctf$ by step 1. Identify the source with $i_!Rp_*T_{\overline X}A$ using $i_!\gamma_{p,A}\circ\delta_i$. Both maps now restrict to the identity of $Rp_*T_{\overline X}A$, so uniqueness in the interchange statement (2) proves the equation.

Cited statements: det-sf-comp-composition-interchange, lem-sfb-proper-direct-image-coefficient-restriction, det-prop-scalar-six-direct-image.

### Returned step 7

On these models the canonical compact-support compositor is
$$\alpha_{g,f}:Rq_*i_!Rp_*j_!\xrightarrow{Rq_*\iota}Rq_*Rr_*j'_!j_!\simeq R(qr)_*(j'j)_!.$$
Its first arrow is the isomorphism of [det-sf-comp-composition-interchange] (3); the last arrow composes proper direct images and open extensions. Apply $Rq_*$ to the equation of step 6. The naturality square of $\gamma_q$ moves $T(Rq_*\iota)$ across $\gamma_q$. The composition equation of [det-prop-scalar-six-direct-image] (2) then replaces $Rq_*\gamma_r\circ\gamma_q$ by $\gamma_{qr}$. The open-composition equation of [det-prop-scalar-six-pullback] (2) replaces $j'_!\delta_j\circ\delta_{j',j_!K}$ by $\delta_{j'j}$. Thus the two paths from $T Rq_*i_!Rp_*j_!K$ to $R(qr)_*(j'j)_!TK$ agree, giving
$$\gamma^!_{gf,K}\circ T(\alpha_{g,f,K})=\alpha_{g,f,TK}\circ Rg_!(\gamma^!_{f,K})\circ\gamma^!_{g,Rf_!K}.$$
Step 5 identifies the comparison for the model $(j'j,qr)$ with that for any chosen model of $gf$. The compositor here is precisely the model construction from proper/open interchange, with its canonical proper/open composition identifications. All coefficient-comparison inputs lie in $\Dctf$ by step 1 and [sk-thm-existence] (2), so the displayed equation proves the asserted composition compatibility on the required category.

Cited statements: det-sf-comp-composition-interchange, det-prop-scalar-six-direct-image, det-prop-scalar-six-pullback, sk-thm-existence.

## Unfinished work

The three new nodes are intentionally statement-only and queued for independent proof splitting. Required server checks and push are the remaining delivery operations; their output determines whether this repair is delivered.
