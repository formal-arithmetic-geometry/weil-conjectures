# Stage-1 worker report: Q73

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-integral-pullback-completed-comparison.json`: existing statement, statement dependencies, Lean record and maintainer metadata preserved; eleven-step proof replaced by a five-step assembly (2044 characters).
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-principal-koszul-strict-replacement.json`: statement, status `unsplit`; no full Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-roos-intrinsic-unit-comparison.json`: statement, status `unsplit`; no full Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-finite-pullback-strict-tower-comparison.json`: statement, status `unsplit`; no full Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-normalized-roos-shift-comparison.json`: statement, status `unsplit`; no full Mathlib match.

Also supplied `citations.json` with a verbatim statement quote for every cited node in every assembly step, and the unmodified `searches.jsonl` produced by msearch. All four new nodes have empty proof/proof_deps, null proof_origin/mathlib_match, the item's chapter and unit, and the nearest blueprint ancestor with the full via chain. No Lean file or unit/chapter record is changed.

## Attachments

None. A search of `lean/WeilConjectures/` by the item id and the integral/completed comparison notions found no declaration stating the item. The existing `WeilConjectures.IntegralCompletedComparison.integralPullback_completedComparison`, in `lean/Sheaf/Paper/IntegralPullbackCompletedComparison.lean:413`, has `sorry` as its proof, so it is no attachment. Its statement package and eleven-step docstring agree with the DAG's comparison, including the fixed coefficient transports and finite projections. New helpers have no exact upstream finished declaration.

## WANTED

None. Sources were read in the shared read clone; nothing was downloaded.

## What was wrong and what changed

This is the human-requested re-split of 2026-10-21, not a statement correction or a stale assignment. The old proof had 9601 characters spread over eleven steps; its resolution, canonical-unit, strict-diagram and shift arguments were too much work for one worker. The existing statement is retained exactly. Four separate arguments are now queueable as statement-only nodes. The parent retains the actual formula for gamma and the projection computation; no new node asserts the whole integral/completed comparison. The source route remains Stacks 099N(5) with principal Koszul resolutions, and no SGA source is used.

The original arguments have not been abbreviated away: the next section assigns every old step to an explicit new statement and retains its complete text as a worker handoff. The only assembly-only portions are old steps 8 and 10, whose formulas remain in the item. The source for each new result is marked as a refinement extracted from the old proof, not falsely attributed as a verbatim Stacks theorem.

## Unfinished work

The four new results deliberately have no proofs: parallel workers are to split/prove them. The parent is complete at stage 1 once those smaller statements are granted. No Lean implementation or compilation is authorized or attempted.

## Argument handoff to the new nodes

The following is proof guidance in the report only; the new node files carry statements only.

### lem-a1-principal-koszul-strict-replacement

Old step 1: Put $A=\mathcal O_E$, $t=\varpi_E$, $R_W=\widehat{\mathcal O}_{E,W}$ and $S_{W,n}=(A/t^n)_W$. The coefficient DVR lemma gives that $A$ is a PID, hence Noetherian, $t\ne0$, and its residue field is finite. The finite-quotient lemma gives that every $A/t^n$ is finite with surjective quotient transitions; in particular $A/(t)$ is additive torsion. The two-term free resolution $[A\xrightarrow{t^n}A]\to A/t^n$, in degrees $[-1,0]$, is exact except at degree zero: multiplication is injective since $A$ is a subring of the field $E$, and its cokernel is the quotient. Thus each quotient is perfect. These verify every coefficient hypothesis of the adic datum in the statement. No finiteness hypothesis on either scheme is required.

Uses: `lem-weil-l-adic-extension-integers-dvr`, `lem-weil-valued-dvr-finite-quotients`, `def-weil-pbc-adic-coefficient-datum`

Old step 2: On each of the two sites, sheafify the constant-presheaf exact sequence $0\to A\xrightarrow{t^n}A\to A/t^n\to0$. Exact abelian sheafification gives the same exact sequence of constant sheaves. The constant/completed coefficient lemma says that $R_W$ is flat over $\underline A_W$ and that $R_W/t^nR_W\cong S_{W,n}$ through the specified projection. Tensoring the constant-sheaf sequence with $R_W$ is exact by the meaning of flatness, so $0\to R_W\xrightarrow{t^n}R_W\to S_{W,n}\to0$ is exact. In particular the augmentation $Q_{W,n}=[R_W\xrightarrow{t^n}R_W]\to S_{W,n}$ is a quasi-isomorphism. Its transitions are multiplication by $t$ in degree $-1$ and identity in degree zero; the augmentations commute strictly with the quotient transitions.

Uses: `lem-weil-pbc-sheafification-exact`, `lem-weil-pbc-constant-completion-equivalence`, `def-pc-flat-sheaf-modules`

Old step 5: Choose a flat-term K-flat resolution $P\to K$. Put $P_n=P\otimes_{R_T}S_{T,n}$ and $X_n=P\otimes_{R_T}Q_{T,n}$, with the strict transitions of Step 2. By the adic-datum construction, $P_\bullet$ represents the entire strict reduction tower $K_\bullet$. The maps $a_n:X_n\to P_n$ are a strict tower quasi-isomorphism: $P$ is K-flat and the augmentation of Step 2 is a quasi-isomorphism. Explicitly, its cone is acyclic; tensoring that cone with $P$ stays acyclic by the definition of K-flatness, and the tensor-cone identity identifies it with the cone of $a_n$. Each $X_n$ is K-flat with flat terms: for an acyclic $N$, $N\otimes X_n$ is, up to the standard tensor-cone signs, the cone of $t^n$ on the acyclic $N\otimes P$, hence acyclic; its terms are finite sums of terms of $P$. Thus $X_\bullet\to P_\bullet$ is an objectwise K-flat replacement of the strict diagram, rather than unrelated choices at each level.

Uses: `lem-pc-kflat-resolution`, `def-weil-pbc-adic-coefficient-datum`, `def-pc-kflat-complex`, `def-pc-flat-sheaf-modules`, `def-weil-abstract-derived-category`

### lem-a1-roos-intrinsic-unit-comparison

Old step 3: We first justify the domain of the completed functor, without replacing the imported Roos completeness condition by a stronger hypothesis. Apply the finite-free completed scalar comparison with $L=E$. Since $K$ is derived complete in exactly the imported sense, it says that the specified quotient-cone completion map $K\to\mathsf C(K_\bullet)$ is an isomorphism, natural in $K$, with zero shifted-product component on one K-flat representative. Countable products of $R_T$-modules are exact on the pro-etale site. The normalized strict Roos comparison $\rho:\mathsf C(K_\bullet)\xrightarrow{\sim}R\lim K_\bullet$ identifies that zero-component map with the strict quotient augmentation's canonical map $\operatorname{comp}_K$. Consequently $\operatorname{comp}_K$ is invertible. This uses the actual completion map, not an arbitrary isomorphism between two objects satisfying Roos triangles.

Uses: `def-weil-derived-complete`, `lem-weil-finite-free-completed-scalar-comparison`, `lem-weil-proetale-countable-products-exact`, `lem-weil-strict-roos-comparison`

Old step 4: By Koszul reconstruction, $c_K:K^{\wedge}_{\mathrm{Kos}}\xrightarrow{\sim}R\lim K_\bullet$ satisfies $c_K\kappa_K=\operatorname{comp}_K$. Hence $\kappa_K$ is invertible by Step 3. Here the reconstruction's Koszul limit and the intrinsic definition's explicit fiber model have the same canonical unit: on a representative $C$, their common strict tower is $C\otimes Q_{T,m}$, and its degree-zero inclusions give a strict augmentation. The intrinsic coordinates have differential $(x,y)\mapsto(dx,(1-s)x-dy)$; the cone coordinates have differential $(y,x)\mapsto(-dy-(1-s)x,dx)$. The map $(x,y)\mapsto(-y,x)$ is a chain isomorphism, and sends the intrinsic unit $(u_C,0)$ to the zero-shifted-component cone unit $(0,u_C)$. The strict Roos comparison identifies this unit with $\kappa_K$. Thus the intrinsic unit is invertible and $K$ is derived $(t)$-complete as claimed.

Uses: `prop-weil-pbc-koszul-reconstruction`, `def-weil-pbc-intrinsic-completion`, `lem-weil-strict-roos-comparison`

### lem-a1-finite-pullback-strict-tower-comparison

This node also owns the shifted-K-flat/termwise-tensor part of old step 11. Its final square explicitly states that compatibility before taking any limit.

Old step 6: Write $G$ for ordinary module pullback along $c_g:g^{-1}R_T\to R_{T'}$; this notation does not mean the integral completed operation. The resolving-class description of the strict tower pullback computes $V K_\bullet:=Lg^*_{\mathrm{Tow}}K_\bullet$ by $G X_\bullet$, using Step 5. The ringed-topos K-flat pullback lemma applies to the given morphism of small pro-etale topoi and $c_g$; hence $P'=GP$ is K-flat with flat terms over $R_{T'}$. Additivity and scalar linearity identify $GX_n$ with $P'\otimes Q_{T',n}$, including the transition $(t,1)$. Step 2 on $T'$ and K-flatness of $P'$ therefore give a strict tower quasi-isomorphism $GX_\bullet\to(P'\otimes S_{T',n})_n$. This argument never assumes that $c_g$ is an isomorphism or that completed-ring module pullback is exact.

Uses: `def-weil-pbc-completed-pullback`, `lem-weil-pbc-diagram-kflat-replacements`, `lem-pur-left-derived-from-kflat-class`, `lem-weil-pbc-ringed-topos-kflat-pullback`

Old step 7: Let $B_\bullet=(\operatorname{Res}_n g_n^*P_n)_n$ with its actual finite quotient transitions. There is a natural chain isomorphism $P'\otimes_{R_{T'}}S_{T',n}\cong\operatorname{Res}_n g_n^*P_n$: both are $g^{-1}P\otimes_{g^{-1}R_T}S_{T',n}$. On the left this is tensor reassociation; on the right use $g^{-1}S_{T,n}\cong S_{T',n}$ and the module tensor construction. The scalar map on both sides is $g^{-1}R_T\to g^{-1}S_{T,n}\to S_{T',n}$, precisely the $n$-th component of $c_g$. The reassociation sends $(x\otimes b)\otimes a$ to $x\otimes\bar b a$, with inverse $x\otimes a\mapsto(x\otimes1)\otimes a$. These formulas commute with differentials and with each quotient map $S_{n+1}\to S_n$. Consequently Step 6 supplies a natural isomorphism $b_K:VK_\bullet\xrightarrow{\sim}B_\bullet$ in the derived category of strict $R_{T'}$-module towers. Finite pullback is exact by the constant-coefficient exactness proposition, so the evaluations of $B_\bullet$ represent the specified finite derived pullbacks.

Uses: `def-weil-pbc-completed-pullback`, `def-pur-sheaf-tensor-product`, `prop-weil-pbc-proetale-constant-ring-map`, `prop-weil-pbc-proetale-constant-exact`

Old step 9: The constructions in Steps 5--7 are natural for chain maps of flat-term K-flat representatives: tensoring, the Koszul augmentation and the balanced formulas commute with such maps. Resolving-class uniqueness identifies the calculation $GX_\bullet$ with the specified total left derived tower functor. The integral well-definedness lemma identifies $\mathsf C(B_\bullet)$ with the specified integral functor independently of resolutions. The normalized Roos map is natural on the whole derived tower category. Therefore the formula in Step 8 is natural in $K$: its naturality square holds on K-flat representatives, and descends through localization; the square for an inverted quasi-isomorphism follows by multiplying the square for that quasi-isomorphism by its inverses. This also proves independence from all representatives used in constructing $b_K$ and $\gamma_{g,K}$.

Uses: `lem-pur-left-derived-from-kflat-class`, `lem-pur-integral-operations-well-defined`, `lem-weil-strict-roos-comparison`, `def-weil-abstract-derived-category`

### lem-a1-normalized-roos-shift-comparison

The tower comparison part belongs to the preceding node; this node owns the normalized Roos comparison and shifted K-injective resolution part. Existing `lem-weil-roos-comm-shift` supplies the native cone shift, and does not already assert this comparison with total derived inverse limit.

Old step 11: Finally check shifts on these models. With the cone coordinates $\mathsf C(B)^i=(\prod B_n)^{i-1}\oplus(\prod B_n)^i$ and differential $(y,x)\mapsto(-dy-(1-s)x,dx)$, the map $\mathsf C(B[r])\to\mathsf C(B)[r]$ is $(y,x)\mapsto((-1)^r y,x)$. Substitution in the differential verifies the chain-map identity. In Step 5 use $P[r]$ for $K[r]$ and the natural shifted two-term tensor identification; Steps 6--7 commute with it, since they apply pullback, scalar multiplication and degree-zero quotient maps. For the Roos comparison choose the shifted K-injective resolution $B[r]\to I[r]$. Shifts preserve K-injectivity by its Hom-vanishing definition, and termwise limit commutes with shifts. Its normalization $z\mapsto(0,z)$ commutes with the displayed signed map. Thus $\rho_{B[r]}$ is $\rho_B[r]$ under these shift comparisons, and the same is true of $R\lim(b_K)$. The completed pullback shift of the cited triangle lemma is precisely the composite of the reduction, tower-pullback and limit shift comparisons used here. The formula of Step 8 therefore proves the asserted equality of $\gamma_{g,K[r]}$ and $\gamma_{g,K}[r]$ for every integer $r$.

Uses: `def-weil-abstract-derived-category`, `def-pur-kinjective-complex`, `lem-weil-strict-roos-comparison`, `lem-cbc-completed-pullback-triangles`

Old step 8 remains assembly step 3: gamma is the inverse derived image of the strict comparison after normalized Roos comparison. Old step 10 remains assembly step 4: substitute e_n rho and e_n Rlim(b) into that formula. Assembly step 5 finishes old step 11 using the two independent shift statements.

## Searches and source readings

Whole-DAG key-word searches included strict/Koszul towers, K-flat replacements, intrinsic units, finite reduction/pullback, Roos shifts and all source tags. Blueprint searches were made with `tools/blueprint_refs.py search` for Koszul, Roos, strict tower, intrinsic, completed pullback, pullback comparison, Koszul resolution, K-flat, Koszul strict, Roos shift, finite reduction and completion unit. No imported blueprint node has the same full statement as one of the four new work packages; nearby general facts are reused as inputs in the handoff. `ancestor` returned `lem-a1-finite-map-purity`, with the existing constructible/fibre-comparison via chain. The current `main-20261015` finite-map proof's first paragraph is the place served, and its chapter/unit argument is unchanged.

All Mathlib searches used msearch.py. Each new node has two successful differently phrased LeanFinder searches, Loogle and source grep, plus a LeanSearch attempt recorded as unavailable (HTTP rate limit, not absence). The first broad Loogle attempts for nodes 1 and 4 contained unknown identifiers; they are honestly recorded, and were supplemented with successful `CochainComplex.mappingCone` and `CochainComplex.mappingCone.shiftIso` queries. Every query in the node records is literally present in the tool log. The extra source greps confirmed candidates and their lines. Candidate readings:

- `AdicCompletion.flat_of_isNoetherian`, `RingTheory/AdicCompletion/AsTensorProduct.lean:379`, is ordinary ring-module flatness, not a sheaf Koszul strict-tower replacement theorem.
- `AdicCompletion.of_bijective_iff` and `ofLinearEquiv`, `RingTheory/AdicCompletion/Basic.lean:647,665`, concern ordinary module completion, not unbounded Roos completeness or the specified Koszul unit.
- `SheafOfModules.pullback`, `pullbackIso`, `pullbackComp`, `Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:53,106,167`, are ordinary module functors and composition, without the derived strict quotient tower, generator normalization, localization and shifts.
- `CochainComplex.mappingCone.shiftIso`, `Algebra/Homology/HomotopyCategory/Pretriangulated.lean:347`, supplies the cone shift but not the normalization equation for rho against K-injective total inverse limit. The general exact-functor localization shift instances likewise lack that equation.

Thus there are zero Mathlib leaves among the four new nodes. Ordinary cone shifts and flatness are not being represented as absent from Mathlib; only the stated work packages lack matches.

## Review by Q73

I read the current finite-map blueprint proof, the item's node and Lean statement/docstring, and Stacks `proetale.tex` Tags 099L (`section-derived-completion-noetherian`), 099M (`lemma-naive-completion`), 099N (`lemma-pushforward-Noetherian-case`), `sites-modules.tex` Tag 093M (`lemma-completion-flat`), and `sites-cohomology.tex` Tags 06YS (`lemma-K-flat-resolution`), 0G7E (`lemma-pullback-K-flat`) and 0941 (`lemma-derived-limit-is-ok`). I also read the local Bhatt-Scholze PDF's Proposition 3.5.1, Definition 3.5.2 and Proposition 4.2.8. Bhatt-Scholze singles out the natural completion map; our imported Roos-triangle predicate does not. I therefore retained, rather than silently skipped, the finite-free scalar comparison at L=E and the signed unit identification in the second new node. Each new node identifies the exact old argument being refined; the sources alone are not treated as proving all these refinements.

For assembly step 1 I checked the full statements of the principal strict replacement and unit comparison nodes: the former includes Noetherianity, finite/perfect quotients, the actual quotient augmentation and K-flat strict replacement, while the latter includes invertibility of the actual intrinsic unit under exactly the imported completeness predicate. The coefficient is the nonzero uniformizer of a finite extension's valuation DVR. There is no perfectness assumption on schemes and no boundedness assumption on K. The new unit comparison's signed map sends (u,0) to (0,u), and d_K intertwines the canonical unit, not a freely selected triangle isomorphism.

For step 2 I read the full finite-tower statement: it asserts a natural isomorphism in the derived category of strict completed-ring towers, including the balanced generator formulas, quotient transitions, independence of representatives and every integer shift. Its ordinary module pullback G is distinct from the integral completed operation. The map c_g is never assumed invertible, and G is never assumed exact. This is the work of old steps 6,7,9, not merely the finite evaluation clause already in the completed-pullback definition. The source 0G7E applies to flat-term K-flat complexes on the small ringed topoi; the small indexing category is the positive integers opposite, so no large-diagram issue is introduced.

For step 3 I opened all five cited nodes. The exact-products lemma is for any commutative ring sheaf on any scheme's pro-etale site, so it applies to R_T'. The integral-operation definition specifies precisely C(B), the completed-pullback definition specifies Rlim(V K_bullet), the strict Roos statement supplies a natural isomorphism, and the ringed strict-tower homotopy-limit statement makes Rlim an actual functor. Thus Rlim(b) is invertible for the strict tower isomorphism and the displayed composite is natural and coefficient-linear. No conclusion is inferred from unrelated levelwise derived maps.

For step 4 the Roos statement explicitly says it commutes with each projection; the tower-comparison statement explicitly fixes the finite evaluations to the specified completed-pullback normalization. Their statements give e_n rho and e_n Rlim(b), respectively. The equality after substituting gamma is composition and cancellation of inverse isomorphisms; it has the inverse direction requested by the item. The quote file uses verbatim statements, with the complete new comparison statement where more than one clause is used.

For step 5 I read the entire normalized shift statement and the completed-pullback triangles statement. The former supplies the previously unstated rho/derived-limit shift square, not just a cone shift. The latter concerns this particular reduction/tower-pullback/limit functor without scheme finiteness assumptions. Together with the finite tower shift square, they give the shift square for the product formula defining gamma. On shifted resolutions, I[r] stays K-injective (maps from acyclic complexes shift to maps from acyclic complexes); its terms remain injective, and inverse limit is termwise, so the stipulated limit shift is the intended one. Roos-triangle completeness is stable under shifting the triangle and correcting the last arrow by the standard sign, so K[r] remains in the required domain; this stability is included in the new unit node.

I checked B1--B9 for each new file: every object is introduced, sheaf/module/derived/K-flat/tensor/complete notions have statement dependencies, formulas use single TeX escaping, sources have labels and tags, no node has proof text or proof dependencies, no matching declaration was promoted to a false Mathlib leaf, and blueprint ancestry is filled. The new nodes are four smaller arguments, not clauses relocated one-for-one: the first is a replacement construction independent of g, the second is a normalized model/unit diagram independent of g, the third is a strict tower comparison for all K without completeness and without inverse limits, and the fourth is a generic normalized shift theorem independent of coefficient DVRs and schemes.

Small cases checked: n=1 gives transition differential t*t^n=t^(n+1) and a degree-zero quotient map; the zero complex gives zero units and tower maps, hence identity isomorphisms on zero; an empty scheme gives the zero sheaf/module category and all equations still hold; E=Q_l is allowed and L=E in the scalar comparison does not add an extension hypothesis; g=id makes the balanced maps the usual quotient identifications; a non-flat c_g is allowed because only K-flat representatives are pulled back; r=0 has identity sign and r=1,-1 both negate only the shifted product, while composing shifts gives (-1)^(r+s). I checked both the intrinsic differential and the cone differential under (x,y) -> (-y,x); the signs agree. These tests found a notational ambiguity in the new tower shift source, which I corrected to V_g((K[r])_bullet), and prompted the explicit shifted completeness sentence. No mathematical dispute or statement change was needed.

All five parent steps have fewer than 2000 characters; total assembly length is 2044. The old long steps are assigned to the new statement-only nodes. The item keeps its inherited maintainer-owned fields. The tool uses retained in split_report are generic coefficient, exact-product, tower-limit and shift facts along the existing route; no tool_uses field has been added or changed. The existing lower-level inputs for new proofs are guidance in this report only, because unsplit new nodes must have no proof_deps. No sub-agent was started.

## Not duplicates

The following source-tag inventory records why sharing a Stacks place does not identify the complete new statement. The closest potential overlaps were opened in full and are discussed first.

lem-a1-principal-koszul-strict-replacement vs lem-sfb-flat-scalar-cyclic-resolution: The existing lemma gives one two-term sheaf resolution for a flat constant algebra, whereas the new statement supplies the coefficient-datum verification and a natural objectwise K-flat strict tower replacement after tensoring any flat-term K-flat P, with its augmentations and transitions.

lem-a1-principal-koszul-strict-replacement vs lem-pur-derived-complete-koszul-reconstruction: The existing lemma proves a levelwise quasi-isomorphism and a limit comparison, but not flat-term K-flatness of the source levels or the completed coefficient-datum and quotient normalizations required of a strict resolving replacement.

lem-a1-roos-intrinsic-unit-comparison vs lem-pur-regular-quotient-completion-unit: The existing criterion makes the regular quotient cone unit invertible, but does not assert the signed intrinsic-fiber/strict-Roos/total-limit comparison diagram d_K eta_intr = rho eta_U or its normalization for the two imported definitions.

lem-a1-roos-intrinsic-unit-comparison vs prop-weil-pbc-koszul-reconstruction: The existing c_K intertwines abstract Koszul and quotient units; the new statement identifies the intrinsic explicit fiber unit, quotient zero-component unit and normalized strict Roos map and upgrades the imported existential Roos-triangle predicate to these actual invertible maps.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-intrinsic-to-tower-complete: The old implication starts with intrinsic completeness; the new result starts with the imported Roos-triangle condition and identifies all three actual completion units by a signed model diagram.

lem-a1-finite-pullback-strict-tower-comparison vs def-weil-pbc-completed-pullback: The definition fixes the functor and its finite evaluations; the new result constructs the strict simultaneous zigzag, proves it is an isomorphism of derived tower functors and asserts its representative normalization, localization naturality and shift square.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-constant-completion-equivalence: The existing finite comparisons are in individual quotient derived categories, not the simultaneous normalized isomorphism b_g in the derived category of completed-ring strict towers with its explicit representative zigzag and all-shift square.

lem-a1-normalized-roos-shift-comparison vs lem-weil-strict-roos-comparison: The existing natural normalized rho commutes with units and projections, but states no integer-shift comparison equation for rho against the K-injective total-limit shift.

lem-a1-normalized-roos-shift-comparison vs lem-weil-roos-comm-shift: The existing node gives a coherent native Roos shift and a zero-coordinate map criterion; it has no comparison to the K-injective total-derived-limit functor or its normalized rho.

lem-a1-normalized-roos-shift-comparison vs lem-weil-signed-mapping-cocone-shift: A signed cone shift alone does not assert compatibility of normalized rho with the shift computed by K-injective tower resolutions.

lem-a1-principal-koszul-strict-replacement vs lem-pe-kflat-roos-representative-invariance: The existing statement concerns “K-flat representative invariance of augmented scalar-extension Roos cones”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sbc-scalar-extension-counit-properties: The existing statement concerns “K-flat computation and triangulatedness of a specified scalar-extension counit”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-exc-intrinsic-resolution-tensor-homology: The existing statement concerns “Tensor cohomology in the intrinsic coefficient presentation”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-coef-derived-system-evaluation-calculus: The existing statement concerns “Coherent derived reduction, limit adjunction and fiberwise evaluation”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sf-open-operation-models: The existing statement concerns “Open operation comparisons with fixed tensor models and right square”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sf-open-tensor-support: The existing statement concerns “Derived tensor preserves open support in either factor”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sf-open-pullback-support: The existing statement concerns “Derived pullback preserves open support”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-exc-intrinsic-tor-amplitude-transport: The existing statement concerns “Transport of intrinsic Tor intervals”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-coef-finite-adjunction-diagram-realization: The existing statement concerns “Finite exceptional operations and enriched adjunction on coherent coefficient systems”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-coef-sheaf-flat-model: The existing statement concerns “Monoidal flat model for unbounded complexes on a ringed site”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sf-open-tensor-support-aux: The existing statement concerns “The open tensor projection transpose is invertible”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sf-ringed-derived-native-tensor: The existing statement concerns “Native symmetric derived tensor and one-K-flat localization comparisons”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-coef-semilinear-operations-existence: The existing statement concerns “Geometric and coefficient operations on a fixed semilinear system calculus”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-coef-semilinear-system-existence: The existing statement concerns “Ordinary semilinear system calculus and cartesian internal Hom”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-trf-point-reduction-unit-normalization: The existing statement concerns “Point coefficient-reduction comparisons are normalized by scalar-extension units”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-trf-finite-filtered-flat-resolution: The existing statement concerns “Flat resolutions for a fixed finite filtration”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-trf-ringed-complex-derived-tensor-vanishing: The existing statement concerns “Derived tensor cohomology vanishing for a complex on a ringed site”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pc-kflat-single-tensor-representative: The existing statement concerns “lem-pc-kflat-single-tensor-representative”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sc-flat-telescope-model-shift-gauge: The existing statement concerns “Local supplied-tensorator shift gauge on flat telescope models”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pc-flat-truncation-telescope-comparison: The existing statement concerns “Quasi-isomorphism comparison for telescopes of truncation replacements”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pc-complex-hocolim-colimit: The existing statement concerns “Telescope homotopy colimits are termwise filtered colimits”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pc-derived-tensor-upper-bound: The existing statement concerns “Derived tensor with a module preserves an upper cohomological bound”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pc-kflat-bounded-flat-replacement: The existing statement concerns “Bounded-above flat replacement on a ringed site”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pc-kflat-resolution: The existing statement concerns “Existence of K-flat resolutions on a ringed site”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-sc-bounded-flat-shift-representative: The existing statement concerns “Bounded-flat homotopy representatives and their translates”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pc-bounded-above-flat-tensor-acyclic: The existing statement concerns “Tensoring bounded-above acyclic complexes with bounded-above flat complexes”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sc-flat-telescope-normalization-morphisms: The existing statement concerns “Forward morphisms extending a bounded-flat normalization”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sc-kflat-localized-cone-presentation: The existing statement concerns “K-flat cone presentation after homotopy localization”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sc-flat-telescope-shift-gauge: The existing statement concerns “Source shift gauge for flat telescope normalization”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pc-kflat-hocolim-truncations: The existing statement concerns “Homotopy colimit of truncations”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sc-flat-telescope-bounded-normalization-extension: The existing statement concerns “Extend bounded normalization through telescope cones”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sc-flat-telescope-arrow-diagram: The existing statement concerns “Compatible flat tower diagram over a cochain arrow”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pc-bounded-above-flat-kflat-site: The existing statement concerns “Bounded-above flat complexes on a ringed site are K-flat”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sc-normalized-flat-telescope-stage-comparison: The existing statement concerns “Joint normalization natural on bounded-flat tower maps”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-pc-derived-tensor-cohomology-vanishes: The existing statement concerns “Vanishing of derived tensor cohomology with an O_X-module”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sc-flat-telescope-normalization-is-iso: The existing statement concerns “Invertibility propagates from bounded-flat models to telescopes”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sc-normalized-flat-telescope-comparison: The existing statement concerns “Joint normalized pullback comparison on explicit flat telescopes”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pc-tensor-counit-coordinate-equation: The existing statement concerns “Raw tensor coordinate equation for the universal pullback counit”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sc-flat-telescope-normalization-unshifted-is-iso: The existing statement concerns “Invertibility on literal unshifted telescope cones”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sc-bounded-flat-model-normalization: The existing statement concerns “Supplied-tensorator normalization on bounded flat stages”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sc-flat-telescope-sum-comparison-is-iso: The existing statement concerns “Invertibility of the restricted natural comparison on the sum of bounded-flat stages”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-pc-kflat-complex: The existing statement concerns “K-flat complex of modules on a ringed site”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sc-flat-telescope-stage-map-refinement: The existing statement concerns “Common flat-tower refinement of a homotopy morphism”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sc-flat-telescope-cone-normalization-descent: The existing statement concerns “Cone extension and descent of supplied normalized sum maps”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-sc-derived-tensor-augmentation: The existing statement concerns “Derived tensor augmentation on a scheme”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-pc-derived-tensor-complex-cohomology-vanishes: The existing statement concerns “Vanishing of derived tensor cohomology of two derived objects”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-sc-flat-telescope-stage-map: The existing statement concerns “Concrete flat telescopes and their stage-induced morphisms”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sc-flat-telescope-sum-models: The existing statement concerns “Literal telescope models for a countable coproduct”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pc-kflat-closure: The existing statement concerns “Closure of K-flat complexes”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sc-flat-telescope-stage-naturality: The existing statement concerns “Common-refinement cancellation extends stage naturality”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pc-kflat-cone-direct-sum: The existing statement concerns “Cones and countable direct sums of K-flat complexes”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sfb-local-integral-perfect-model-cohomology: The existing statement concerns “Cohomology of a local integral perfect scalar model”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs det-thm-sf-pf-adic-open: The existing statement concerns “Integral open direct image preserves constructibility”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sfb-condensed-support-projection-formula: The existing statement concerns “Natural support tensor projection formulas on unbounded condensed modules”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-sfb-quotient-kernel-completeness: The existing statement concerns “Local derived completeness for a ring-sheaf quotient kernel”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-sfb-ringed-projection-coherence-data: The existing statement concerns “Recorded data for tensor projection coherence”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs det-prop-diagonal-tower-limit: The existing statement concerns “The $\ell$-adic diagonal class over the completed coefficient sheaf”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sfb-adic-stratum-completion-unit: The existing statement concerns “Restriction of the completion unit to strata and covering slices”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sfb-adic-residue-lisse-perfect-lift: The existing statement concerns “Local perfect lifting from a lisse residue complex without finite coefficient hypotheses”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sfb-finite-constant-model-two-term-free-resolution: The existing statement concerns “Finite scalar local models have two-term finite-free sheaf resolutions”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sfb-integral-quotient-direct-image-comparison: The existing statement concerns “Unbounded quotient-scalar refinement of integral direct image”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-sfb-condensed-pullback-tensor-comparison: The existing statement concerns “Normalized condensed-module pullback tensor comparison”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-sfb-adic-residue-lift-comparisons: The existing statement concerns “The coefficient comparisons and actual finite-reduction Hom tower”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sfb-adic-perfect-model-complete-reduction: The existing statement concerns “Completeness and residue calculation of a completed perfect coefficient model”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sfb-ringed-projection-tensor-structure: The existing statement concerns “Canonical tensor structure in arbitrary recorded presentations”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sfb-ringed-projection-pullback-comparisons: The existing statement concerns “Normalized identity, composition and section pullback comparisons”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sfb-ringed-projection-tensor-compatibility: The existing statement concerns “Tensor constraints and compatibility of normalized comparisons”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs sk-thm-sf-pf-adic: The existing statement concerns “Open direct image and projection formula”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-weil-pbc-completed-quotient-ordinary-unit: The existing statement concerns “Ordinary completed quotient-limit unit”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-derived-exact-equivalence-squares: The existing statement concerns “Compatible derived squares under exact equivalences”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-weil-pbc-completed-base-change-map: The existing statement concerns “Completed base-change map”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-weil-pbc-site-tensor-local-model-comparison: The existing statement concerns “Tensor cohomology comparison from models of good truncations”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-weil-pbc-completed-quotient-completion-unit: The existing statement concerns “Bundled specified completed quotient-completion unit”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs prop-weil-pbc-direct-image-limits: The existing statement concerns “Direct image, derived limits, and completeness”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-weil-pbc-completed-constant-realization-data: The existing statement concerns “Completed constant realization interfaces”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-weil-pbc-completed-constant-module-model: The existing statement concerns “Scalar extension realizes finite completion modules”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-weil-pbc-completed-constant-algebra-flat-quotients: The existing statement concerns “Ordinary flat algebra and quotients of a completed constant ring”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-weil-pbc-reconstruction-uniform-tower: The existing statement concerns “Reconstruction of a uniform local tower”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-constant-completion-unit-normalization: The existing statement concerns “Constant quotient completion unit on every complex”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-weil-pbc-restriction-derived-products: The existing statement concerns “Exact scalar restriction on derived module sheaves is a right adjoint”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-weil-pbc-completed-constant-sheaf-reduction: The existing statement concerns “Completed constant coefficients and finite reduction”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-weil-pbc-flat-common-quotient-reduction-tower: The existing statement concerns “Derived common-quotient reduction as a normalized strict tower”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-weil-pbc-constant-completion-equivalence: The existing statement concerns “Constant-to-completed coefficients on derived-complete categories”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-weil-pbc-adic-coefficient-datum: The existing statement concerns “Tower category and adic coefficient datum”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-weil-pbc-completed-pullback: The existing statement concerns “Completed pullback”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-weil-pbc-completed-constant-presentation-transport: The existing statement concerns “Joint transport of the completed quotient and Koszul presentations”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-weil-pbc-completed-constant-coefficient-equivalence: The existing statement concerns “Scalar and strict quotient compatibility of the completed coefficient equivalence”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-weil-pbc-completed-koszul-quotient-comparison: The existing statement concerns “Unit-compatible Koszul-to-quotient comparison in the completed coefficient presentation”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs prop-weil-pbc-koszul-reconstruction: The existing statement concerns “Koszul and quotient reconstruction”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-weil-pbc-reduction-pullback-derived-tower: The existing statement concerns “Normalized derived pullback of a strict coefficient reduction tower”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-derived-cochain-counit: The existing statement concerns “Derived counit on complex localization”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-weil-pbc-completed-koszul-constant-transport: The existing statement concerns “Koszul completion under a scalar-preserving completed coefficient isomorphism”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-weil-pbc-completed-quotient-unit-normalization: The existing statement concerns “Actual completed quotient unit on a K-flat complex”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-weil-pbc-site-derived-tensor-descent: The existing statement concerns “Derived tensor and K-flat representative descent on a ringed site”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-derived-cochain-right-unit: The existing statement concerns “Derived unit on complex localization”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-derived-exact-equivalence-square-data: The existing statement concerns “Data of compatible exact-equivalence derived squares”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-weil-pbc-intrinsic-completion: The existing statement concerns “Intrinsic derived completion”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-derived-cochain-comparison-factors: The existing statement concerns “Localization comparison for an additive functor on complexes”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-weil-pbc-common-quotient-tower-presentation: The existing statement concerns “Common-quotient tower presentations and local ideal-product membership”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-weil-pbc-completed-constant-presentation-data: The existing statement concerns “Common constant presentation of the two completion objects”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-weil-pbc-finite-perfect-adic-canonical-comparison: The existing statement concerns “Canonical derived quotients as explicit coefficient complexes with compatible finite-free retracts”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-cbc-finite-extension-reduction-cone-bound: The existing statement concerns “Uniformizer cone comparison and uniform reduction bound”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sp-constant-pullback-scalar: The existing statement concerns “Module pullback transports scalar multiplication”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pur-integral-operations-well-defined: The existing statement concerns “The towers defining integral pullback and completed tensor product are invariant under change of K-flat resolution”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pur-acyclic-kflat-tensor-arbitrary: The existing statement concerns “An acyclic K-flat complex tensors acyclically with every complex”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs new-lem-kun-exact-monoidal-equivalence-derived: The existing statement concerns “Coherent monoidal descent of an exact adjoint equivalence”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-kun-flat-resolution-existence: The existing statement concerns “Flat K-flat resolutions”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-sp-constant-inverse-image-section: The existing statement concerns “Transported global sections and constant quotient kernels”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-weil-finite-free-completed-scalar-comparison: The existing statement concerns “Finite free completed coefficient extension is ordinary derived scalar extension”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pur-system-tensor-reduction-formula: The existing statement concerns “Tensor formula for actual semilinear reduction adjoints”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pur-completed-line-derived: The existing statement concerns “Derived finite reductions of a completed coefficient line are ordinary reductions”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-weil-completed-scalar-shift-descent: The existing statement concerns “Normalized descent of the strict completed scalar shift”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pur-kflat-cone-comparison: The existing statement concerns “Two K-flat resolutions: augmentation square computing the derived-to-ordinary tensor comparison”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pur-system-normalized-tensor-closure: The existing statement concerns “Normalized semilinear systems are closed under tensor and inverse image”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs def-weil-integral-derived-reduction: The existing statement concerns “Derived reduction of integral complexes modulo powers of the uniformizer”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pur-varying-ring-tensor-support: The existing statement concerns “Tensor support for canonical varying-ring extension”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pod-point-principal-reduction-coefficients: The existing statement concerns “The completed principal coefficient sequence is short exact”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pod-point-reduction-coefficient-ring: The existing statement concerns “The normalized lifted coefficient quotient is a regular principal quotient”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-principal-koszul-strict-replacement vs lem-pod-completed-integral-scalar-regular: The existing statement concerns “Powers of the uniformizer are regular on completed coefficient sections”; the new conclusion is the principal completed-coefficient strict K-flat replacement package, not merely a finite quotient or tensor property. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs prop-weil-pbc-levelwise-truncations: The existing statement concerns “Levelwise truncations of the adic tower”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-coef-sequence-sections-limit-comparison: The existing statement concerns “Derived sections and total limit with specified projections”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-coef-derived-system-evaluation-calculus: The existing statement concerns “Coherent derived reduction, limit adjunction and fiberwise evaluation”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-sf-integral-compactification-system-realization: The existing statement concerns “Coherent integral realization of compactification expressions and their maps”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-coef-sequence-pushforward-limit-projections: The existing statement concerns “Restricted total-limit comparison with adjunction projections”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-coef-finite-adjunction-diagram-realization: The existing statement concerns “Finite exceptional operations and enriched adjunction on coherent coefficient systems”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-coef-sequence-global-sections-evaluation: The existing statement concerns “Derived termwise global sections with finite evaluation and transition normalization”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-coef-sequence-projection-derived-adjunction: The existing statement concerns “Derived adjunction of a ringed sequence projection”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-coef-ringed-sequence-site: The existing statement concerns “Canonical ringed sequence site for the coefficient quotient tower”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-zl-field-weil-shriek-shift-data: The existing statement concerns “Canonical field-coefficient Weil compact support and shift data”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-zl-left-derived-equivalence-square: The existing statement concerns “Left derived squares under exact equivalences”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-trf-integral-pullback-reduction-counit: The existing statement concerns “K-flat reduction-unit counit calculation for integral inverse image”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-trf-integral-cone-counit-realization: The existing statement concerns “The derived-limit counit recovers a compatible tower family from its cone lift”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-trf-integral-tower-inverse-image-unit: The existing statement concerns “Canonical inverse-image tensor unit on entire quotient towers”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-trf-compact-support-system-evaluation-diagram: The existing statement concerns “The actual compact-support system evaluation diagram”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-trf-coefficient-tower-operations: The existing statement concerns “Coefficient tower operations and point sections”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-trf-compact-support-system-evaluation-coherence: The existing statement concerns “Comparison of strict and enhanced system operation models”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs det-prop-diagonal-tower-system: The existing statement concerns “The torsion diagonal classes as one morphism of inverse systems”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-sfb-adic-stratum-completion-unit: The existing statement concerns “Restriction of the completion unit to strata and covering slices”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-sfb-adic-complete-reduction-cone: The existing statement concerns “Normalized quotient homotopy-limit cone for a complete object”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-sfb-adic-complete-hom-section-surjective: The existing statement concerns “Compatible finite-reduction morphisms lift into a complete target”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-sfb-adic-complete-residue-conservative: The existing statement concerns “Residue reduction is conservative on locally complete objects”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-a1-lisse-section-evaluation: The existing statement concerns “Canonical evaluation of ordinary common-stage sections at a geometric point”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-finite-perfect-adic-coefficient-limit: The existing statement concerns “Actual coefficient limits, finite powers, and compatible finite-projective complex retracts”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-completed-koszul-quotient-roos-augmentation: The existing statement concerns “The completed strict Koszul quotient augmentation on Roos models”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-weil-pbc-completed-quotient-ordinary-unit: The existing statement concerns “Ordinary completed quotient-limit unit”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-ringed-cech-koszul-dual-limit: The existing statement concerns “Extended Cech complex and Koszul dual limit”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-derived-exact-equivalence-squares: The existing statement concerns “Compatible derived squares under exact equivalences”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-weil-pbc-ringed-koszul-system: The existing statement concerns “The finite strict Koszul system and its derived-limit presentations”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-ringed-cech-koszul-comparison-existence: The existing statement concerns “Existence of the normalized ringed Koszul Cech comparison”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-completed-koszul-product-comparison: The existing statement concerns “Finite Koszul comparison induces the normalized product-fiber comparison”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-weil-pbc-completed-quotient-completion-unit: The existing statement concerns “Bundled specified completed quotient-completion unit”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-completed-fiber-strict-limit-comparison: The existing statement concerns “Published completed Koszul fiber computes the strict derived limit”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-levelwise-isomorphism-cones: The existing statement concerns “Levelwise isomorphisms and complete cones”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-koszul-localization-assembly: The existing statement concerns “Localization assembly for the Koszul comparison”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-reconstruction-uniform-tower: The existing statement concerns “Reconstruction of a uniform local tower”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-completed-fiber-roos-representative-comparison: The existing statement concerns “The explicit Koszul comparison is compatible with every derived representative”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-constant-completion-unit-normalization: The existing statement concerns “Constant quotient completion unit on every complex”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-completed-fiber-cech-comparison: The existing statement concerns “Published completed Koszul fiber compared with Cech internal Hom”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-exact-products-roos-comparison: The existing statement concerns “The normalized Roos fibre computes derived inverse limit with exact products”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs prop-weil-pbc-koszul-reconstruction-comparison: The existing statement concerns “Comparison of completed Koszul and quotient derived limits”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-ordered-exchange-coefficient-comparison: The existing statement concerns “Coefficient normalization of the raw ordered completed exchange”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-constant-completion-equivalence: The existing statement concerns “Constant-to-completed coefficients on derived-complete categories”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-weil-pbc-adic-coefficient-datum: The existing statement concerns “Tower category and adic coefficient datum”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-ringed-strict-tower-homotopy-limit: The existing statement concerns “Strict tower homotopy limit”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-finite-perfect-adic-tower-limit: The existing statement concerns “Specified completed strict limit from a compatible finite-projective marking”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-completed-constant-presentation-transport: The existing statement concerns “Joint transport of the completed quotient and Koszul presentations”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-flat-constant-tensor-pro-zero-cones: The existing statement concerns “Flat constant extension and K-flat tensor of pro-zero cone towers”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-completed-constant-coefficient-equivalence: The existing statement concerns “Scalar and strict quotient compatibility of the completed coefficient equivalence”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-completed-koszul-quotient-comparison: The existing statement concerns “Unit-compatible Koszul-to-quotient comparison in the completed coefficient presentation”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-derived-cochain-counit: The existing statement concerns “Derived counit on complex localization”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-completed-koszul-constant-transport: The existing statement concerns “Koszul completion under a scalar-preserving completed coefficient isomorphism”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-finite-perfect-adic-complex-roos: The existing statement concerns “Roos limit of a termwise epimorphic completed-module complex tower”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-weil-pbc-derived-reduction-model-data: The existing statement concerns “Derived reduction model data and normalized complex comparisons”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-completed-quotient-unit-normalization: The existing statement concerns “Actual completed quotient unit on a K-flat complex”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-finite-reduction-reconstruction: The existing statement concerns “Finite reduction of reconstruction”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-derived-cochain-right-unit: The existing statement concerns “Derived unit on complex localization”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-derived-exact-equivalence-square-data: The existing statement concerns “Data of compatible exact-equivalence derived squares”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-ringed-cech-koszul-comparison-on-site: The existing statement concerns “A unit-compatible Cech Koszul comparison on one ringed site”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-weil-pbc-intrinsic-completion: The existing statement concerns “Intrinsic derived completion”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-derived-cochain-comparison-factors: The existing statement concerns “Localization comparison for an additive functor on complexes”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-ringed-cech-koszul-hom-limit-comparison: The existing statement concerns “Telescope Hom comparison for a prescribed strict Koszul limit”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-completed-koszul-reduction-roos-triangle: The existing statement concerns “Normalized quotient Roos triangle on explicit Koszul completion”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-weil-pbc-koszul-reconstruction-models: The existing statement concerns “The fixed Koszul and quotient reconstruction models”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-finite-perfect-adic-realization: The existing statement concerns “Completed realization of uniform finite perfect quotient models”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-pbc-finite-perfect-adic-marked-roos: The existing statement concerns “Roos limit of the canonical finite-projective quotient diagram”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-weil-pbc-completed-constant-presentation-data: The existing statement concerns “Common constant presentation of the two completion objects”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-coef-sequence-roos-model: The existing statement concerns “Normalized DVR tower carried by a normalized derived coefficient sequence”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-strict-roos-comparison: The existing statement concerns “Natural comparison of strict derived inverse limit and the product cone”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-coef-constant-tower-roos: The existing statement concerns “Canonical Roos triangle of a completed-coefficient derived tower”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-pur-principal-koszul-quotient-towers: The existing statement concerns “Canonical principal Koszul and quotient towers with tensor augmentations”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-pur-finite-free-completion-exchange: The existing statement concerns “Finite free change of rings exchanges quotient completion on arbitrary complexes”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-sf-completion-finite-reduction: The existing statement concerns “Finite reduction inverts the completion unit”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-pur-roos-additive-comparison: The existing statement concerns “Additive comparison for the strict Roos cone”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-pur-integral-operation-shift-data: The existing statement concerns “Representative-normalized operation and independent-slot shifts”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-sp-slice-restriction-strict-derived-limit: The existing statement concerns “Slice restriction commutes with total derived inverse limit of strict towers”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-pur-integral-operation-roos-effectivity: The existing statement concerns “Effectivity of the strict finite-operation Roos towers”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-sp-levelwise-kinjective-tower-image: The existing statement concerns “Levelwise K-injective towers compute additive functors applied levelwise”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-sp-completion-mate-comparison: The existing statement concerns “The strict quotient-tower exchange realizes the completed-adjunction mate”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-strict-roos-normalization: The existing statement concerns “StrictRoosNormalization”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-weil-strict-roos-model: The existing statement concerns “StrictRoosModel”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-sf-quotient-tower-evaluation-complex: The existing statement concerns “Explicit finite evaluation of a quotient-tower complex”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-cbc-completed-pullback-triangles: The existing statement concerns “Completed pullback preserves shifts and distinguished triangles”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-sp-constant-reduction-models: The existing statement concerns “Coupled universal models for strict constant-coefficient reduction”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-strict-roos-derivation: The existing statement concerns “StrictRoosDerivation”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-pur-derived-complete-koszul-reconstruction: The existing statement concerns “Koszul reconstruction of a derived-complete reduction tower”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-sf-cbc-compact-support-composition-limit: The existing statement concerns “Normalized reconstruction of composites of completed operations”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-pur-integral-coherence-tower: The existing statement concerns “Coherence identities on normalized integral comparison towers”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-sp-proper-open-tower-comparison: The existing statement concerns “Open-adjunction normalization of proper/open interchange on strict coefficient towers”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-pur-finite-free-completion-exchange-coherence: The existing statement concerns “Coefficient-tower coherence of the specified quotient-completion exchange”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-pur-integral-tower-limit-comparison: The existing statement concerns “Derived limit of the strict integral comparison tower”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-pur-compact-support-completed-projection-coherence: The existing statement concerns “Completion coherence for the integral projection mate”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-sf-completion-unit-finite-projection: The existing statement concerns “Projection of the completion unit is the finite scalar-extension unit”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-sp-completed-pullback-adjunction: The existing statement concerns “Completed pullback is left adjoint to direct image”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs def-pur-synchronized-canonical-maps: The existing statement concerns “The same canonical map at two independent input families”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-pur-compact-support-roos-cofinality: The existing statement concerns “Cofinal restriction of a Roos tower complex”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-weil-compact-support-reduction-tower-functor: The existing statement concerns “Coherent compact-support reduction tower functor”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-sf-cbc-extension-zero-completion: The existing statement concerns “Strict reduction of completed extension by zero”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-pod-integral-system-pullback-lift-associativity: The existing statement concerns “Associativity of a fixed fully faithful integral pullback lift”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-pod-integral-pullback-system-comparison: The existing statement concerns “For every morphism f:X→Y of schemes with ell invertible, the actual constructible completed integral pullback followed by coherent system reduction is naturally isomorphic to coherent system reduction followed by exact finite-system inverse image”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-roos-intrinsic-unit-comparison vs lem-pod-integral-system-reduction-fully-faithful: The existing statement concerns “Coherent reduction is fully faithful on the full category of derived-complete bounded constructible integral coefficient objects”; the new conclusion is the three specified completion units and the signed model diagram for imported Roos completeness. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs prop-weil-pbc-levelwise-truncations: The existing statement concerns “Levelwise truncations of the adic tower”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sbc-completed-operations-linear-natural-exchange: The existing statement concerns “Linearity and naturality of completed pullback, direct image, and exchange”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sbc-reflected-compositor-unit-normalization: The existing statement concerns “Compatibility of a reflected composition isomorphism with completion units”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sbc-scalar-extension-counit-properties: The existing statement concerns “K-flat computation and triangulatedness of a specified scalar-extension counit”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sbc-derived-coefficient-map-descent: The existing statement concerns “Descent of a termwise coefficient map through a resolving counit”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs def-sf-pull-completion-comparison: The existing statement concerns “Strict quotient normalization of pullback completion”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sf-open-operation-models: The existing statement concerns “Open operation comparisons with fixed tensor models and right square”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sf-open-pullback-support: The existing statement concerns “Derived pullback preserves open support”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sf-right-derived-from-adapted-complexes: The existing statement concerns “Right derived functor from a class of adapted complexes”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs def-sf-tensor-completion-comparison: The existing statement concerns “Roos normalization of the tensor completion comparison”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sf-scalar-pullback-composition: The existing statement concerns “Composition coherence of normalized scalar/pullback comparisons”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pod-point-extension-kflat: The existing statement concerns “K-flatness of the point extension of a flat-term module complex”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs def-coef-semilinear-system-models: The existing statement concerns “Generic strict semilinear system constructions and representative normalization”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-etale-native-tensor-pullback: The existing statement concerns “Native unbounded derived tensor commutes with etale inverse image”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs def-zl-field-weil-shriek-shift-data: The existing statement concerns “Canonical field-coefficient Weil compact support and shift data”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs def-zl-derived-change-of-rings-model: The existing statement concerns “Canonical derived change-of-rings cochain model”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-trf-bounded-above-acyclic-derived-computation: The existing statement concerns “Bounded above acyclic complexes compute a left derived functor”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs def-trf-integral-comparison-realization-models: The existing statement concerns “Normalized realization interfaces for integral quotient systems”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs def-trf-singleton-site-operations: The existing statement concerns “Punctual ringed-site operations and normalized comparison predicates”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs def-trf-integral-comparison-sequence-systems: The existing statement concerns “Canonical pullback and scalar change of whole quotient systems”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-trf-integral-pullback-comparison-realization: The existing statement concerns “Strict-system realization and composition coherence of integral pullback comparisons”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pc-ringed-space-tensor-pullback-absolute: The existing statement concerns “Absolute K-flat derived comparison for concrete tensor pullback”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs q3-ringed-space-tensor-pullback-absolute-postcomposition: The existing statement concerns “Absoluteness of tensor pullback derived comparison”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pc-kflat-scalar-extension-counit: The existing statement concerns “Universal scalar extension counit on K-flat module complexes”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs q3-ringed-space-tensor-pullback-left-derived: The existing statement concerns “K-flat derived comparison for concrete tensor pullback”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sfb-constant-module-kflat: The existing statement concerns “Constant realization preserves flat-term K-flat complexes”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sfb-constant-realization-derived-scalar-extension: The existing statement concerns “Derived constant realization commutes with derived scalar extension”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sfb-ringed-site-point-kflat-resolution: The existing statement concerns “K-flat resolution with K-flat stalk”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sfb-successive-derived-quotient-normalization: The existing statement concerns “Successive derived scalar extensions agree with direct quotient extension”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sfb-flat-term-kflat-functor: The existing statement concerns “Flat-preserving colimit functors preserve flat-term K-flat complexes”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs def-sfb-derived-change-of-rings-cochain-model: The existing statement concerns “Derived change-of-rings cochain presentation”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sfb-kflat-scalar-comparison-normalization: The existing statement concerns “Representative and adjunction normalization of scalar pullback comparison”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sfb-scalar-extension-kflat: The existing statement concerns “Scalar extension preserves all K-flat sheaf complexes”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sc-global-tensor-pullback-derived-data: The existing statement concerns “Absolute derived tensor comparison after point evaluation”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-a1-integral-pullback-completed-comparison: The item compares integral and completed pullback with domain, projections and shifts; this new node covers only the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square.

lem-a1-finite-pullback-strict-tower-comparison vs def-a1-integral-completed-pullback-interfaces: The existing statement concerns “Projection-normalized completed coefficient transport and finite pullback evaluation interfaces”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: The existing statement concerns “Derived tensor comparison for arbitrary ringed topoi”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs def-weil-pbc-completed-base-change-map: The existing statement concerns “Completed base-change map”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-tower-compatibility: The existing statement concerns “Compatibility with the coefficient tower”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs prop-weil-pbc-direct-image-limits: The existing statement concerns “Direct image, derived limits, and completeness”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-pulled-reduction-strict-tower-comparison: The existing statement concerns “Augmented strict reduction tower of ordinary pullback”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-ringed-pullback-preserves-kflat: The existing statement concerns “Ringed pullback kflat”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-ringed-derived-adjunction-independent-universes: The existing statement concerns “Derived module inverse image is left adjoint to a supplied derived direct image”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-pulled-reduction-normalization-comparison: The existing statement concerns “Successive quotient normalizations under the pulled reduction comparison”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lemma-weil-pbc-completed-map-reduction: The existing statement concerns “Finite reduction of the completed map”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lemma-weil-pbc-completed-exchange-coherence: The existing statement concerns “Completed exchange coherence”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-ringed-topos-kflat-pullback: The existing statement concerns “Ringed-topos pullback preserves flat-term K-flat complexes”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-ringed-topos-pullback-adapted-flat-resolution: The existing statement concerns “A flat resolution whose ringed-topos pullback is K-flat”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-flat-coefficient-reduction-adjunct: The existing statement concerns “Finite scalar comparison preserves derived reduction adjuncts”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-kflat-tensor-pullback-computation-universes: The existing statement concerns “Derived pullback computes K-flat tensor representatives”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-ordered-exchange-coefficient-comparison: The existing statement concerns “Coefficient normalization of the raw ordered completed exchange”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs def-weil-pbc-four-corners: The existing statement concerns “Four finite-level corners”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-supplied-ringed-topos-kflat-pullback: The existing statement concerns “Tensor pullback adjoint to a supplied ringed-topos module direct image”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-uniqueness: The existing statement concerns “Canonical tensor comparison unit uniqueness”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-constant-derived-normalization-universal: The existing statement concerns “Constant derived realization preserves universal coefficient arrows”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-ringed-topos-acyclic-kflat-pullback: The existing statement concerns “Ringed-topos pullback in the acyclic K-flat case”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-completed-adic-koszul-kflat: The existing statement concerns “K-flatness of the actual completed exterior Koszul complexes”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-intrinsic-to-tower-complete: The existing statement concerns “Intrinsic completeness implies quotient-tower completeness”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lemma-weil-pbc-completed-pullback-reduction: The existing statement concerns “Reduction commutes with completed pullback”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-completed-constant-derived-tensor-tower: The existing statement concerns “Universal derived tensor tower from K-flat resolutions”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs thm-weil-pbc-complete-proetale: The existing statement concerns “Complete pro-etale proper base change”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-diagram-kflat-replacements: The existing statement concerns “Objectwise K-flat replacements in strict diagram categories”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-existence: The existing statement concerns “Canonical tensor comparison unit existence”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-ringed-common-quotient-pullback-comparison: The existing statement concerns “Common quotient reduction of the geometric scalar comparison”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-normalized-derived-isomorphism-transport: The existing statement concerns “Universal normalization and evaluation of source-site local Isom sheaves”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-weil-pbc-derived-scalar-extension-local-systems: The existing statement concerns “Coherent localized derived scalar extension and comparison”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pur-coefficient-tensor-derived-unit: The existing statement concerns “Universal derived comparison for the identity coefficient tensor”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-cbc-strict-quotient-pullback-computation: The existing statement concerns “Resolved strict quotient pullback with its specified augmentation”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs def-pur-completed-coefficient-presentation-transport: The existing statement concerns “Normalized tensor comparison between completed coefficient presentations”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs def-pur-derived-constant-pullback-comparison: The existing statement concerns “Canonical derived constant-sheaf pullback comparison”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pur-resolving-class-derived-adjunction: The existing statement concerns “Normalized derived adjunction from a resolving class”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs def-weil-common-stage-derived-direct-image: The existing statement concerns “Common-stage derived direct image and induced Weil adjunction”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sf-common-stage-pullback-identity: The existing statement concerns “Identity comparison for common-stage derived pullback”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pur-integral-operations-well-defined: The existing statement concerns “The towers defining integral pullback and completed tensor product are invariant under change of K-flat resolution”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pur-derived-change-of-rings: The existing statement concerns “Derived change of rings along a morphism of sheaves of rings, computed by K-flat resolutions”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pur-etale-scalar-pullback-existence: The existing statement concerns “Existence of normalized derived scalar/pullback comparison”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-cbc-derived-constant-tower-normalization: The existing statement concerns “Unique representative normalization of the derived constant-tower comparison”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pur-resolving-class-essential-constancy: The existing statement concerns “Resolving classes make denominator pro-diagrams essentially constant”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sf-integral-pullback-linear-adjunction: The existing statement concerns “Integral constructible pullback has a coefficient-linear right adjoint”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs def-pur-etale-scalar-pullback-iso: The existing statement concerns “Canonical derived scalar and pullback isomorphism”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs def-pur-integral-derived-operations: The existing statement concerns “Integral derived pullback, completed tensor product and internal Hom”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pur-integral-operation-roos-effectivity: The existing statement concerns “Effectivity of the strict finite-operation Roos towers”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs def-pur-change-of-rings-complex: The existing statement concerns “Termwise change of rings of a cochain complex”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pur-left-derived-from-kflat-class: The existing statement concerns “Left derived functor on the derived category computed by a resolving class”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sp-completion-mate-comparison: The existing statement concerns “The strict quotient-tower exchange realizes the completed-adjunction mate”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pur-integral-ambient-operation-models: The existing statement concerns “Ambient completion presentations for integral pullback and tensor”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pur-scalar-tensor-pullback-normalization: The existing statement concerns “Scalar/tensor pullback normalization on a K-flat representative”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-exc-proetale-constant-support-projection: The existing statement concerns “Constant-coefficient projection for compact support”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sf-coherent-rational-pullback-identity: The existing statement concerns “Scalar-compatible identity pullback comparisons at rational stages”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-cbc-completed-pullback-triangles: The existing statement concerns “Completed pullback preserves shifts and distinguished triangles”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pur-kflat-change-of-rings: The existing statement concerns “Change of rings preserves K-flat complexes with flat terms”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs def-pur-open-coefficient-normalizations: The existing statement concerns “Exact-pullback and open-unit coefficient normalizations”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sf-cbc-compact-support-composition-limit: The existing statement concerns “Normalized reconstruction of composites of completed operations”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pur-etale-scalar-pullback-uniqueness: The existing statement concerns “Uniqueness of normalized derived scalar/pullback comparison”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sf-reduction-pull-finite-evaluation: The existing statement concerns “Finite evaluation respects the specified reduction/pullback comparison”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pur-varying-ring-tensor-comparison: The existing statement concerns “Normalized tensor comparison for one varying-ring inverse image”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-cbc-derived-tower-evaluation-normalization: The existing statement concerns “Unique representative normalization of derived tower evaluation”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sp-completed-pullback-adjunction: The existing statement concerns “Completed pullback is left adjoint to direct image”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pur-kflat-change-of-rings-independent: The existing statement concerns “Change of rings preserves K-flat complexes with flat terms in independent universes”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pur-coefficient-pullback-comparison: The existing statement concerns “Canonical inverse-image coefficient comparison”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-fix-tensor-pullback-square: The existing statement concerns “Tensor inverse-image comparisons commute around an open square”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-sf-cbc-extension-zero-completion: The existing statement concerns “Strict reduction of completed extension by zero”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pur-ordinary-adjunction-scalar-compatibility: The existing statement concerns “Scalar compatibility of the ordinary completed adjunction”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pur-completed-coefficient-pushforward-comparison: The existing statement concerns “Completed-coefficient pushforward restriction and strict reduction towers”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pod-integral-system-pullback-lift-associativity: The existing statement concerns “Associativity of a fixed fully faithful integral pullback lift”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pd-module-ringed-topos-derived-comparison: The existing statement concerns “Module-object and ringed-topos derived tensor comparison”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pod-integral-pullback-system-comparison: The existing statement concerns “For every morphism f:X→Y of schemes with ell invertible, the actual constructible completed integral pullback followed by coherent system reduction is naturally isomorphic to coherent system reduction followed by exact finite-system inverse image”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pod-integral-pullback-composition: The existing statement concerns “Composition isomorphism for integral derived pullbacks”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-finite-pullback-strict-tower-comparison vs lem-pod-integral-system-reduction-fully-faithful: The existing statement concerns “Coherent reduction is fully faithful on the full category of derived-complete bounded constructible integral coefficient objects”; the new conclusion is the normalized derived strict-tower pullback zigzag for arbitrary K, with localization naturality and shift square. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-pe-principal-reduction-cone-calculus: The existing statement concerns “Strict principal reduction cones and their compatible cone comparisons”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-coef-sequence-sections-limit-comparison: The existing statement concerns “Derived sections and total limit with specified projections”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-coef-derived-system-evaluation-calculus: The existing statement concerns “Coherent derived reduction, limit adjunction and fiberwise evaluation”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-sf-integral-compactification-system-realization: The existing statement concerns “Coherent integral realization of compactification expressions and their maps”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-coef-sequence-pushforward-limit-projections: The existing statement concerns “Restricted total-limit comparison with adjunction projections”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-coef-finite-adjunction-diagram-realization: The existing statement concerns “Finite exceptional operations and enriched adjunction on coherent coefficient systems”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-sf-double-hom-cone-comparison: The existing statement concerns “Signed double-Hom comparison with a mapping cone”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-coef-sequence-global-sections-evaluation: The existing statement concerns “Derived termwise global sections with finite evaluation and transition normalization”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-coef-sequence-projection-derived-adjunction: The existing statement concerns “Derived adjunction of a ringed sequence projection”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs def-coef-ringed-sequence-site: The existing statement concerns “Canonical ringed sequence site for the coefficient quotient tower”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs def-zl-field-weil-shriek-shift-data: The existing statement concerns “Canonical field-coefficient Weil compact support and shift data”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-zl-left-derived-equivalence-square: The existing statement concerns “Left derived squares under exact equivalences”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-trf-integral-pullback-reduction-counit: The existing statement concerns “K-flat reduction-unit counit calculation for integral inverse image”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-trf-integral-cone-counit-realization: The existing statement concerns “The derived-limit counit recovers a compatible tower family from its cone lift”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs def-trf-integral-tower-inverse-image-unit: The existing statement concerns “Canonical inverse-image tensor unit on entire quotient towers”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs def-trf-compact-support-system-evaluation-diagram: The existing statement concerns “The actual compact-support system evaluation diagram”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs def-trf-coefficient-tower-operations: The existing statement concerns “Coefficient tower operations and point sections”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-trf-compact-support-system-evaluation-coherence: The existing statement concerns “Comparison of strict and enhanced system operation models”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-sfb-adic-complete-reduction-cone: The existing statement concerns “Normalized quotient homotopy-limit cone for a complete object”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-sfb-adic-complete-hom-section-surjective: The existing statement concerns “Compatible finite-reduction morphisms lift into a complete target”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs def-a1-lisse-section-evaluation: The existing statement concerns “Canonical evaluation of ordinary common-stage sections at a geometric point”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-pbc-finite-perfect-adic-coefficient-limit: The existing statement concerns “Actual coefficient limits, finite powers, and compatible finite-projective complex retracts”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-pbc-ringed-cech-koszul-dual-limit: The existing statement concerns “Extended Cech complex and Koszul dual limit”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs def-weil-pbc-ringed-koszul-system: The existing statement concerns “The finite strict Koszul system and its derived-limit presentations”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-pbc-ringed-cech-koszul-comparison-existence: The existing statement concerns “Existence of the normalized ringed Koszul Cech comparison”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-pbc-completed-koszul-product-comparison: The existing statement concerns “Finite Koszul comparison induces the normalized product-fiber comparison”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-pbc-completed-fiber-strict-limit-comparison: The existing statement concerns “Published completed Koszul fiber computes the strict derived limit”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-pbc-completed-fiber-roos-representative-comparison: The existing statement concerns “The explicit Koszul comparison is compatible with every derived representative”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-pbc-completed-fiber-cech-comparison: The existing statement concerns “Published completed Koszul fiber compared with Cech internal Hom”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-pbc-exact-products-roos-comparison: The existing statement concerns “The normalized Roos fibre computes derived inverse limit with exact products”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs prop-weil-pbc-koszul-reconstruction-comparison: The existing statement concerns “Comparison of completed Koszul and quotient derived limits”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-pbc-ringed-strict-tower-homotopy-limit: The existing statement concerns “Strict tower homotopy limit”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-pbc-finite-perfect-adic-tower-limit: The existing statement concerns “Specified completed strict limit from a compatible finite-projective marking”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-pbc-finite-perfect-adic-complex-roos: The existing statement concerns “Roos limit of a termwise epimorphic completed-module complex tower”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs def-weil-pbc-derived-reduction-model-data: The existing statement concerns “Derived reduction model data and normalized complex comparisons”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-pbc-ringed-cech-koszul-comparison-on-site: The existing statement concerns “A unit-compatible Cech Koszul comparison on one ringed site”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-pbc-ringed-cech-koszul-hom-limit-comparison: The existing statement concerns “Telescope Hom comparison for a prescribed strict Koszul limit”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs def-weil-pbc-koszul-reconstruction-models: The existing statement concerns “The fixed Koszul and quotient reconstruction models”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-pbc-finite-perfect-adic-realization: The existing statement concerns “Completed realization of uniform finite perfect quotient models”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-pbc-finite-perfect-adic-marked-roos: The existing statement concerns “Roos limit of the canonical finite-projective quotient diagram”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-completed-scalar-chain-shift: The existing statement concerns “Signed coherent shifts and the strict completed scalar comparison”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-amb-signed-fibre-shift: The existing statement concerns “Coherent signed comparisons with every integer shift”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-coef-sequence-roos-model: The existing statement concerns “Normalized DVR tower carried by a normalized derived coefficient sequence”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-coef-constant-tower-roos: The existing statement concerns “Canonical Roos triangle of a completed-coefficient derived tower”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs def-pur-principal-koszul-quotient-towers: The existing statement concerns “Canonical principal Koszul and quotient towers with tensor augmentations”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-amb-signed-fibre-triangulated: The existing statement concerns “The signed fibre of a natural transformation of additive functors preserves cone triangles”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-pur-finite-free-completion-exchange: The existing statement concerns “Finite free change of rings exchanges quotient completion on arbitrary complexes”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-amb-signed-fibre-complex: The existing statement concerns “The additive signed fibre complex and its homotopies”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-pur-roos-additive-comparison: The existing statement concerns “Additive comparison for the strict Roos cone”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs def-pur-integral-operation-shift-data: The existing statement concerns “Representative-normalized operation and independent-slot shifts”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-sp-slice-restriction-strict-derived-limit: The existing statement concerns “Slice restriction commutes with total derived inverse limit of strict towers”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-sp-levelwise-kinjective-tower-image: The existing statement concerns “Levelwise K-injective towers compute additive functors applied levelwise”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-sp-completion-mate-comparison: The existing statement concerns “The strict quotient-tower exchange realizes the completed-adjunction mate”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-strict-roos-normalization: The existing statement concerns “StrictRoosNormalization”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs def-weil-strict-roos-model: The existing statement concerns “StrictRoosModel”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-sf-quotient-tower-evaluation-complex: The existing statement concerns “Explicit finite evaluation of a quotient-tower complex”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-cbc-completed-pullback-triangles: The existing statement concerns “Completed pullback preserves shifts and distinguished triangles”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs def-sp-constant-reduction-models: The existing statement concerns “Coupled universal models for strict constant-coefficient reduction”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-strict-roos-derivation: The existing statement concerns “StrictRoosDerivation”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-pur-derived-complete-koszul-reconstruction: The existing statement concerns “Koszul reconstruction of a derived-complete reduction tower”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-amb-signed-fibre-cone: The existing statement concerns “Natural signed interchange between the two cones”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-sf-cbc-compact-support-composition-limit: The existing statement concerns “Normalized reconstruction of composites of completed operations”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-pur-integral-coherence-tower: The existing statement concerns “Coherence identities on normalized integral comparison towers”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-sp-proper-open-tower-comparison: The existing statement concerns “Open-adjunction normalization of proper/open interchange on strict coefficient towers”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-pur-finite-free-completion-exchange-coherence: The existing statement concerns “Coefficient-tower coherence of the specified quotient-completion exchange”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-pur-integral-tower-limit-comparison: The existing statement concerns “Derived limit of the strict integral comparison tower”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-pur-compact-support-completed-projection-coherence: The existing statement concerns “Completion coherence for the integral projection mate”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-pur-strict-roos-homotopy-functor: The existing statement concerns “The strict Roos cone preserves compatible homotopies”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-sf-completion-unit-finite-projection: The existing statement concerns “Projection of the completion unit is the finite scalar-extension unit”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs def-pur-synchronized-canonical-maps: The existing statement concerns “The same canonical map at two independent input families”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-pur-compact-support-roos-cofinality: The existing statement concerns “Cofinal restriction of a Roos tower complex”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-weil-compact-support-reduction-tower-functor: The existing statement concerns “Coherent compact-support reduction tower functor”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-sf-cbc-extension-zero-completion: The existing statement concerns “Strict reduction of completed extension by zero”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-pod-integral-system-pullback-lift-associativity: The existing statement concerns “Associativity of a fixed fully faithful integral pullback lift”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-pod-integral-pullback-system-comparison: The existing statement concerns “For every morphism f:X→Y of schemes with ell invertible, the actual constructible completed integral pullback followed by coherent system reduction is naturally isomorphic to coherent system reduction followed by exact finite-system inverse image”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

lem-a1-normalized-roos-shift-comparison vs lem-pod-integral-system-reduction-fully-faithful: The existing statement concerns “Coherent reduction is fully faithful on the full category of derived-complete bounded constructible integral coefficient objects”; the new conclusion is the normalized rho/total-limit integer-shift square computed by shifted K-injective tower resolutions. The shared tag is a source input, not an identification of these statements.

