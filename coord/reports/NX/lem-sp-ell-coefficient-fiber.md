# Worker report: lem-sp-ell-coefficient-fiber

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-ell-coefficient-fiber.json`: unchanged statement, four assembly steps (2101 characters), status split.
- `dag/nodes/sec-smooth-purity/lem-sp-completed-coefficient-regular-quotients.json`: statement-only unsplit; completed coefficient projection kernels, epimorphisms, regular scalars, finite quotients and cofinality. Mathlib: no match.
- `dag/nodes/sec-smooth-purity/lem-sp-regular-scalar-quotient-exact-row.json`: statement-only unsplit; regular-scalar Koszul resolution, total tensor identification and four-term quotient exact row. Mathlib: no match.
- `dag/nodes/sec-smooth-purity/lem-sp-exact-row-augmentation-fiber.json`: statement-only unsplit; generic exact-row shifted augmentation fiber with normalized coordinates and strict naturality. Mathlib: no match.
- `citations.json`: a literal statement excerpt for every step/node citation. Full statements are used to make the quoted hypotheses visible.
- `report.md`: this repair, the preserved original proof, and the prior report.

Three new nodes, zero Mathlib leaves. Search logs and output text, PDF text extraction, old-proof.json and scripts are sandbox working material only.

## Attachments

None. The project-source searches for the blueprint tag, completed coefficient notions, quotient Koszul and cone kernel found no sorry-free declaration of the whole item. The existing `Sheaf.Paper.EllCoefficientFiber` declarations `AlgebraicGeometry.ProEtale.sp_completed_coefficients_regular` and `sp_ell_coefficient_fiber` end in sorry. The source `WeilConjectures` coefficient definitions do not supply these assertions. The generic source kernel-to-shifted-cone theorem has its existing node; it does not state the new exact-row naturality interface and is an ingredient for its later worker, not a proof of the whole item.

## WANTED

None. The blueprint, Bhatt–Scholze PDF, and relevant Stacks source are present. Existing DVR and finite-quotient source nodes are reused as the proof material for the new completed-coefficient node; no new external reference is invented.

## Return repaired

The sole numbered issue is the mandatory re-split of the 6356-character proof. The parent statement is byte-for-byte unchanged. Its proof is now 2101 characters, below 3000, with three new statement-only nodes, each status unsplit, empty proof and proof_deps, null proof_origin, complete source, blueprint provenance and actual logged Mathlib searches. They are distinct arguments, not one renamed version of the entire parent. The original work divides approximately 2647 / 1986 / 1723 characters among coefficient algebra, regular-scalar resolution/exactness, and cone/naturality. The original eight paragraphs are copied verbatim below; none was discarded or replaced by a vague summary. Those paragraphs are handoff material for the new workers, not proof steps placed in their unsplit JSON.

Old steps 1–3 belong to `lem-sp-completed-coefficient-regular-quotients`: the valued DVR argument, conversion of powers, sectionwise regularity, projection kernel and local lifting/gluing remain its complete future proof material. Old steps 4–6 belong to `lem-sp-regular-scalar-quotient-exact-row`: scalar-cone K-flatness, tensor computation, well-defined kernel map and both cancellation arguments are all retained. Old steps 7–8 belong to `lem-sp-exact-row-augmentation-fiber`: the exact-row abstraction captures the three-term signs, all cohomology checks and strict naturality of the shifted cone. The numerical left-square computation from old step 8 also remains explicitly in parent step 4, as does the n=m check. Thus the workers can work on the three arguments independently; none of the new statements depends on another new statement or on the parent.

No statement dispute or source correction is needed. The new general exact-row statement asserts its derived isomorphism, not only cohomology groups. The regular-scalar node states an exact row; the parent obtains its cohomology clauses directly from the cohomology definition. No SGA or purity/trace theorem is used.

## Not duplicates

Whole-DAG searches by coefficient, quotient Koszul, scalar regularity, exact rows and shifted cones, and `blueprint_refs.py search` across every chapter found no node stating any of the three full interfaces. The blueprint searches for “quotient Koszul”, “coefficient fiber”, and “scalar regular” had zero matches; broader Koszul/completed/cone searches were inspected. The parent ancestor is sk-lem-sp-tower and each new provenance has via=[lem-sp-ell-coefficient-fiber]. Their same_as is empty.

- lem-sp-completed-coefficient-regular-quotients vs lem-sp-ell-coefficient-fiber: only the coefficient setup argument is extracted under the human's explicit re-split instruction; it contains no Koszul fiber, cohomology, resolution or fiber transition assertion.
- lem-sp-completed-coefficient-regular-quotients vs lem-pod-completed-integral-scalar-regular: the existing node gives only sectionwise uniformizer-power injectivity, not projection kernels, sheaf epimorphisms, ell conversion or normalized quotient comparison.
- lem-sp-completed-coefficient-regular-quotients vs lem-sp-completed-integral-projection-divisibility: divisibility gives the kernel inclusion only; the new node also proves local surjectivity, the actual quotient identifications, regularity, finiteness and cofinality.
- lem-sp-completed-coefficient-regular-quotients vs det-prop-sfb-qlbar-colimit-x-integral-limit: the existing statement identifies a ring sheaf with a limit, not its quotient kernel or regular scalar assertions.
- lem-sp-completed-coefficient-regular-quotients vs lem-weil-pbc-completed-constant-sheaf-reduction: the latter is a flatness and derived tensor comparison over the discrete constant ring, not the actual quotient ideal in the completed sheaf, sectionwise scalar regularity or normalized projection statement here.
- lem-sp-completed-coefficient-regular-quotients vs lem-weil-ramified-coefficient-quotient-comparison: that is an extension-of-fields coefficient comparison, not this single-ring quotient and regularity argument.
- lem-sp-regular-scalar-quotient-exact-row vs lem-sfb-finite-free-mono-cokernel-kflat: the existing lemma supplies the resolution part but not the quotient exact row or the specified multiplication-by-difference-power kernel map. Its statement will be available to the new worker; the distinct cancellation and local gluing argument is not subsumed by it.
- lem-sp-regular-scalar-quotient-exact-row vs lem-cbc-regular-quotient-cone-augmentation: the existing lemma compares scalar cones after tensoring a supplied exact scalar sequence, not the four-term quotient row with its normalized left injection.
- lem-sp-regular-scalar-quotient-exact-row vs lem-sfb-exact-scalar-periodic-resolution: that assumes a square-zero scalar with kernel=image and constructs an infinite periodic resolution. Here the scalar is regular and the finite quotient row has arbitrary n>=m.
- lem-sp-exact-row-augmentation-fiber vs lem-weil-degreewise-epi-kernel-cocone-qis: the existing theorem compares a degreewise kernel complex with a shifted cone; this new statement also supplies the reduction of the four-term row to A[1], the three-term coordinate presentation, and the strict naturality identity for a diagram of four-term rows. The existing statement does not assert these normalized row diagrams.
- lem-sp-exact-row-augmentation-fiber vs lem-pur-kernel-shifted-cone-boundary: that identifies the connecting morphism in cohomology for a short exact kernel sequence, not a quasi-isomorphism/naturality of these four-term row fibers.
- lem-sp-exact-row-augmentation-fiber vs lem-cbc-regular-quotient-cone-chain: that constructs a scalar cone augmentation to a functor annihilating the scalar, not a shifted augmentation fiber from an exact row.

The new source records cite the blueprint's actual coefficient calculation and the extracted returned steps. No new node cites a Stacks tag as if it stated the composite interface. Supporting Stacks Tags 07A3/06YN and 014E/014F are read below and already represented by the cited definitions and tools.

## Review by NX

I read the standing brief, delivery-errors B–E in both copies, SETUP's three levels, GOAL, the smooth-purity chapter and sk-lem-sp-tower unit, and its current main-20261015 proof first paragraph. I compared the repository's returned version with the sandbox, which initially held only dispatcher markers and no node or report; I copied the current item and retained its metadata, original proof, citations/search records and previous Q97 report. The previous report is archived below and does not describe the new counts.

For the item and each new node I read that blueprint paragraph, whose displayed tensor and power-of-ell sentence are the precise route. I read Bhatt–Scholze §3.5, Definition 3.5.2 and Lemmas 3.5.4–3.5.7, from the local PDF extraction (lines 1200–1290). These are background tower/reduction results, not a verbatim source of these explicit chain-coordinate lemmas; the parent retains proof_origin.by=agent and each new unsplit proof_origin is null. For the resolution portion I read sites-cohomology.tex, definition-K-flat (06YN) and lemma-K-flat-two-out-of-three (07A3). For the cone portion I read derived.tex definition-cone (014E) and the functorial-cone display (014F). The shift differential reverses signs, giving +d then -q exactly as stated.

For completed coefficients I opened every old dependency's statement: the DVR node gives the unit-times-uniformizer factorization and finite residue field; the coefficient-extension definition explicitly supplies nonarchimedeanness, required by the finite-quotient theorem. The positive exponent follows from |ell|=ell^(-1)<1. The limit comparison's clause (3) permits every scheme, as does scalar regularity. Projection divisibility uses n=j-1, hence requires j>=1; local sections of the constant sheaf have representatives by the local-sheafification theorem. Lifting those representatives through O supplies local surjectivity. This is a sheaf quotient, not surjectivity of every section map. All those arguments remain in the first work package.

For parent step 1, its cited new coefficient statement explicitly provides every conclusion taken there, including all actual quotient maps. For step 2, the regular-scalar lemma explicitly supplies both resolutions, the tensor model, the augmentation, the exact row and its left image. Sectionwise regularity for ell and pi comes from step 1. Its general small-site hypothesis is satisfied by the chosen small model of T_proet, in a module universe containing it. Reading def-weil-abstract-derived-category confirms that H^-1 of the two-term complex is its kernel and H^0 its cokernel. No ringed-space-only K-flat theorem is applied to this site.

For parent step 3, the exact-row lemma explicitly supplies the quasi-isomorphism with coordinate a and the sign -red; its hypotheses are the exact B_n-module row supplied by step 2. No choice of an unidentified isomorphism or cone map enters. For step 4, the scalar-restriction definition says the underlying sheaf and morphism are unchanged. Thus the B_n-exact row is still the same exact row after restriction to B_nprime. The new exact-row lemma explicitly allows any commuting four-term diagram and gives r i'=i alpha[1]. I verified its three diagram equations: reduction commutes with ell^m, final reduction commutes with identity on B_m, and the left equation is the displayed power equality. The source and target coefficient actions therefore match; no independent site/field universe is identified.

I checked the new statements on the zero sheaf/empty site, a unit regular scalar, R=Z_ell, ramified O with ell=u*pi^e, n=m=1, n=m, nprime=n, and nprime-n>=m. A unit scalar makes all B_k zero and the scalar cone acyclic, so no nonunit hypothesis is silently needed in the generic lemma. At n=m the left map is identity, middle map zero and the final reduction identity, giving the contractible -1 summand. At equal transition indices alpha=1; when the gap is >=m alpha=0. Local quotient lifts are used only after covers. I also performed the finite arithmetic check recorded below for the kernel, exact row and transition formulas.

Mathlib searches were performed only with msearch.py, with at least two semantic phrasings, Loogle, grep and LeanSearch for each proposed interface. All results were read; every service succeeded. In particular I inspected mappingCone.descShortComplex and quasiIso_descShortComplex (ShortExact.lean:53,137): they are a cone-to-quotient assertion for a short exact sequence of complexes, not the new normalized row comparison in one specialization. Ideal.exact_mulQuot_quotOfMul (OrderOfVanishing/Basic.lean:91) is ordinary ring quotient exactness; it neither sheafifies the row nor provides K-flatness. AdicCompletion.eval_a_of and surjective_eval_a (AdicCompletion/Algebra.lean:153 onward) concern ordinary module completion, not the actual pro-etale coefficient sheaf. The Koszul grep result at LocalCohomology.lean:45 is future work. None warrants a Mathlib leaf. Recorded queries/results are copied from searches.jsonl without invented searches.

The new nodes have no proofs and no proof dependencies; their statements introduce all their objects and cite the relevant definition nodes. They do not refer to the parent for hypotheses. The parent uses only the new nodes, the existing cohomology/cone definition, and scalar restriction. Their union is exactly proof_deps. Each citation has a literal quote in citations.json. No proof step exceeds 2000 characters; the complete parent proof is below the requested 3000. No repository file, launcher file, Lean file or build artifact was written and no compiler/Lake command or agent was started. All generic dependencies that previously required off-unit tool declarations now belong to the separate unsplit work packages; no new assembly edge leaves the unit except definition tools.

## Preserved original proof and work assignment

### Original step 1 — lem-sp-completed-coefficient-regular-quotients

By [lem-weil-l-adic-extension-integers-dvr], $O$ is a DVR with finite residue field and every nonzero element of $E$ is a unit times an integer power of $\pi$. Apply this to $\ell$. Since $|\ell|_E=\ell^{-1}<1$ and $0<|\pi|_E<1$, its exponent $e$ is positive: $\ell=u\pi^e$ with $u\in O^\times$, $e\geq1$. Thus $(\ell^n)=(\pi^{en})$, which proves cofinality (for each $j$, choose $n$ with $en\geq j$; for each $n$, choose $j=en$). The hypotheses of [lem-weil-valued-dvr-finite-quotients] hold: $|\cdot|_E$ is nonarchimedean by clause 1 of [def-weil-l-adic-coefficient-extension], and $O$ is a DVR with maximal ideal $\{|x|_E<1\}$, finite residue field and uniformizer $\pi$ by the clauses just cited. Its finite-quotient clause gives finiteness of $O/\pi^j$, and $O/\ell^n=O/\pi^{en}$ is finite as well.

Uses: def-weil-l-adic-coefficient-extension, lem-weil-l-adic-extension-integers-dvr, lem-weil-valued-dvr-finite-quotients.

### Original step 2 — lem-sp-completed-coefficient-regular-quotients

Clause (3) of [det-prop-sfb-qlbar-colimit-x-integral-limit], for the given arbitrary scheme $T$ and finite extension $E$, identifies the pulled-back ring $R$ with the inverse limit of the uniformizer-power constant quotient sheaves, with their reduction projections. These are precisely the coefficient projections of [sk-def-sp-coefficient-towers]. Apply [lem-pod-completed-integral-scalar-regular] to this inverse-limit sheaf: for every site object $U$, multiplication by $\pi^j$ on $R(U)$ is injective. The image of the constant unit $u$ in $R(U)$ is invertible, so $\ell^m=u^m\pi^{em}$ also acts injectively. This is sectionwise injectivity, hence injectivity as a sheaf map; no hypothesis on the characteristic, dimension or finiteness of $T$ has been used.

Uses: det-prop-sfb-qlbar-colimit-x-integral-limit, sk-def-sp-coefficient-towers, lem-pod-completed-integral-scalar-regular.

### Original step 3 — lem-sp-completed-coefficient-regular-quotients

Write $\rho_j:R\to(O/\pi^j)_T$ for a projection. It kills $\pi^jR$, and [lem-sp-completed-integral-projection-divisibility], with its index $j-1\geq0$, says conversely that every section in its kernel is $\pi^j$ times a section of $R$. The projection is locally surjective: by [def-weil-pbc-constant-sheaf] and [lem-weil-pbc-site-sheafification-sections-local], a target section locally comes from a single element of $O/\pi^j$; choose an $O$-representative $a$, and its compatible residue classes define a section of the inverse limit mapping to that element. Consequently the induced map $R/\pi^jR\to(O/\pi^j)_T$ is locally bijective, hence an isomorphism of sheaves: local inverses agree on overlaps by injectivity and glue uniquely. Because all maps come from the same compatible residue projections, they preserve ring operations and quotient transitions. Substituting $j=en$ and using $\ell^nR=\pi^{en}R$ gives the canonical identification $R/\ell^nR=B_n$. This proves the genuine sheaf quotient assertion, not merely the notation stipulated in [sk-def-sp-coefficient-towers].

Uses: lem-sp-completed-integral-projection-divisibility, def-weil-pbc-constant-sheaf, lem-weil-pbc-site-sheafification-sections-local, sk-def-sp-coefficient-towers.

### Original step 4 — lem-sp-regular-scalar-quotient-exact-row

The two-term complexes have $H^{-1}=0$ by scalar injectivity, and $H^0$ equal to their indicated quotients by step 3. Thus their augmentations are quasi-isomorphisms, by the cohomology definition in [def-weil-abstract-derived-category]. Each is the mapping cone of the corresponding scalar map $R[0]\to R[0]$. For any acyclic complex $A$, the total tensor $A\otimes_RR[0]$ is $A$ by the unit identification, directly from [def-pc-tensor-complex-sheaves]. Both copies are therefore acyclic. Apply [lem-pc-kflat-tensor-cone-two-out-of-three] on the ringed site $(T_{\mathrm{proét}},R)$ to conclude that its tensor with the cone is acyclic. This is exactly K-flatness [def-pc-kflat-complex]. Their two nonzero terms are $R$, so these are finite free K-flat resolutions.

Uses: def-weil-abstract-derived-category, def-pc-tensor-complex-sheaves, lem-pc-kflat-tensor-cone-two-out-of-three, def-pc-kflat-complex.

### Original step 5 — lem-sp-regular-scalar-quotient-exact-row

Tensoring $K_m$ with $B_n[0]$ using [def-pc-tensor-complex-sheaves] gives exactly $P_{n,m}=[B_n\xrightarrow{\ell^m}B_n]$. Reduction $B_n\to B_m$ kills its differential since $n\geq m$, so $\epsilon_{n,m}$ is a chain map. Define $a_{n,m}:B_m\to B_n$ by $\bar x\mapsto\ell^{n-m}\bar x$: locally lift $\bar x$ to $R$; changing the lift by $\ell^my$ changes the answer by $\ell^ny=0$ in $B_n$. These local formulas agree and glue. They are $B_n$-linear, with $B_m$ carrying its reduction action.

Uses: def-pc-tensor-complex-sheaves.

### Original step 6 — lem-sp-regular-scalar-quotient-exact-row

The map $a_{n,m}$ identifies $B_m$ with $\ker(\ell^m:B_n\to B_n)$. Indeed, locally lift a section $\bar x\in B_n$ to $x\in R$. If $\ell^m\bar x=0$, then, after a further cover if needed, $\ell^m x=\ell^ny$ for some $y\in R$. Cancellation of the injective scalar $\ell^m$ gives $x=\ell^{n-m}y$, proving local surjectivity onto the kernel. If $\ell^{n-m}y=\ell^nz$, cancellation gives $y=\ell^mz$, proving injectivity (when $n=m$ this cancels the identity). Also $\operatorname{im}(\ell^m:B_n\to B_n)=\ker(B_n\to B_m)$: both are locally the residue classes represented by $\ell^my$, and reduction is locally surjective. Hence $H^{-1}(P_{n,m})=\ell^{n-m}B_n\cong B_m$ and $H^0(P_{n,m})=B_m$, by [def-weil-abstract-derived-category].

Uses: def-weil-abstract-derived-category.

### Original step 7 — lem-sp-exact-row-augmentation-fiber

Use the cone and shift signs of [def-weil-abstract-derived-category]. In degrees $-1,0,1$, the shifted cone $F_{n,m}=\operatorname{Cone}(\epsilon_{n,m})[-1]$ is the three-term complex $B_n\xrightarrow{\ell^m}B_n\xrightarrow{-\mathrm{red}}B_m$, zero elsewhere. The map $i_{n,m}:B_m[1]\to F_{n,m}$ has degree $-1$ component $a_{n,m}$ and all other components zero; it is a chain map since $\ell^m\ell^{n-m}=\ell^n=0$ in $B_n$. Step 6 says that $H^{-1}(i_{n,m})$ is an isomorphism. It also gives $H^0(F_{n,m})=\ker(\mathrm{red})/\operatorname{im}(\ell^m)=0$ and $H^1(F_{n,m})=\operatorname{coker}(-\mathrm{red})=0$. All remaining cohomology vanishes by the displayed terms. Thus $i_{n,m}$ is the specified quasi-isomorphism of $B_n$-complexes.

Uses: def-weil-abstract-derived-category.

### Original step 8 — lem-sp-exact-row-augmentation-fiber

For $n'\geq n\geq m$, coefficient reduction on both terms of $P$ commutes with $\epsilon$ and induces on the three displayed terms of $F$ the maps $(\mathrm{red},\mathrm{red},1_{B_m})$. The formula for the cone in [def-weil-abstract-derived-category] gives this chain map directly, with no choice of cone morphism. For any local lift $x\in R$ of a section of $B_m$, its degree $-1$ component sends $\ell^{n'-m}x\bmod\ell^{n'}$ to $\ell^{n'-m}x\bmod\ell^n$, which equals $\ell^{n-m}(\ell^{n'-n}x)\bmod\ell^n$. All other components of $i$ are zero. Therefore the chain-level square is exactly $F_{n',m}\to F_{n,m}$ composed with $i_{n',m}$ equals $i_{n,m}$ composed with $\ell^{n'-n}:B_m[1]\to B_m[1]$ (viewing both sources by restriction to $B_{n'}$). Inverting the quasi-isomorphisms proves the claimed transition formula. For $n=m$, $\ell^m=0$ in $B_m$, $a_{m,m}=1$, and the remaining two-term summand is $B_m\xrightarrow{-1}B_m$, so the same computation includes the boundary case.

Uses: def-weil-abstract-derived-category.

## Archived prior Q97 report (before this repair)

The following is historical retained material; current changes and counts are above.

# Worker report: lem-sp-ell-coefficient-fiber

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-ell-coefficient-fiber.json`: statement item, now split into eight proof steps; Mathlib verdict: no match for the whole statement.
- `citations.json`: seventeen literal excerpts, one for each step/node citation.
- `report.md`: this report.

No new DAG nodes and no Mathlib leaves. The sandbox also holds the mandatory search log, a local text extraction of Bhatt–Scholze, and the script that writes the item. These are working files, not additions to the library.

## Attachments

None. I searched the project source for the exact blueprint tag and for the coefficient, uniformizer and Koszul notions. `WeilConjectures/SixFunctors/ProEtale/CompletedIntegral.lean` defines the inverse-limit coefficients, finite projections and scalar restrictions, but does not prove the complete item, especially its augmented quotient fiber and power transition formula. Existing individual scalar/divisibility results are cited through their existing DAG nodes; their existence does not attach this conjunction.

## WANTED

None for this split. The coefficient DVR and finite-quotient facts already have nodes; their existing source records mention the previously wanted Serre reference. I use their statements as algebraic tools and introduce no new external theorem.

## Corrections and limitations

The item statement is unchanged. No STATEMENT-DISPUTED finding was needed. The statement already distinguishes the completed ring from the discrete constant ring, and the shifted fiber from the two-term coefficient tensor complex.

The source proof only sketches the coefficient calculation. In particular, Bhatt–Scholze Lemmas 3.5.4–3.5.7 concern compatible systems and pro-isomorphisms; they do not state this precise chain-coordinate fiber map. I read §3.5, including Definition 3.5.2 and the proof of Lemma 3.5.4, and kept `proof_origin.by = agent` for the explicit expansion. The blueprint first paragraph is the item's route: no purity, trace, SGA, or alternative reconstruction argument is introduced.

The K-flat statement for a bounded-above flat complex in `lem-pc-bounded-above-flat-kflat` is stated for a ringed space. I did not apply that statement to an arbitrary pro-etale ringed site. Instead step 4 uses the existing ringed-site tensor/cone lemma, whose hypotheses match exactly.

Nothing mathematical remains unfinished in the requested one-level split. The cited unsplit statements retain their own ownership and work queues.

## Not duplicates

No new nodes were created. Whole-DAG searches and blueprint searches for coefficient, projection divisibility, K-flat, regular completed and Koszul found the existing reusable ingredients, but no blueprint node states the complete item. The item remains the coefficient-fiber subargument of `sk-lem-sp-tower`.

## Review by Q97

I read `coord/delivery-errors.md` B–E in full, the stage-1 brief, the three blueprint levels in SETUP, GOAL, the smooth-purity chapter record and the `sk-lem-sp-tower` unit record. I read the current blueprint proof at `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/sk-lem-sp-tower.proof.md` and the extracted Bhatt–Scholze §3.5 text. There are no new nodes whose sources require a separate audit. I opened the statement of every cited existing node and checked its actual quantifiers, rather than relying on its title or its proof.

Step 1 uses `lem-weil-l-adic-extension-integers-dvr` for the DVR, residue field and uniformizer factorization and `lem-weil-valued-dvr-finite-quotients` for finiteness. The latter needs a nonarchimedean valued field, a DVR valuation ring and a finite residue field, all supplied for this E. The exponent of ell is positive because the absolute value restricts to the ell-adic absolute value. Cofinality and conversion of ell-power quotients to uniformizer-power quotients are written out, not hidden in another node.

Step 2 uses clause (3) of `det-prop-sfb-qlbar-colimit-x-integral-limit` to match the pulled-back ring with the genuine inverse limit and `sk-def-sp-coefficient-towers` for the named coefficient projections. `lem-pod-completed-integral-scalar-regular` explicitly allows every scheme T and site object U; its name does not restrict it to a geometric point. Its uniformizer-power injectivity gives ell-power injectivity by multiplication by a unit. This checks the object match needed before using cancellation later.

Step 3 uses `lem-sp-completed-integral-projection-divisibility` with index j-1, which is nonnegative because j is positive. This theorem states divisibility of sections in the kernel of the actual projection, precisely what is used. The constant-sheaf definition and `lem-weil-pbc-site-sheafification-sections-local` supply local representatives for target sections; lifting a representative a to all compatible residues supplies the local preimage. Kernel equality plus this local lifting proves the sheaf quotient comparison. The proof does not confuse the notation R/ell^n stipulated in a definition with a theorem about its actual quotient. Compatibility follows from the common projections, not an unspecified transport.

Step 4 uses the explicit cohomology/cone definitions in `def-weil-abstract-derived-category`, the tensor convention in `def-pc-tensor-complex-sheaves`, and `lem-pc-kflat-tensor-cone-two-out-of-three`. I read Stacks `sites-cohomology.tex`, Tag 07A3, label `lemma-K-flat-two-out-of-three`, and Definition 06YN. The tensor lemma is for a site and an arbitrary acyclic complex, so it applies with this completed ring. Tensoring with R[0] is the identity, and the two-term scalar complex is its cone. This proves K-flatness using the cited definition, rather than silently deducing it from finite freeness without a theorem.

Step 5 uses the tensor definition to compute P and constructs the B_n-linear map from B_m by local lifts. Independence of the representative is the equality ell^(n-m)ell^m=ell^n. Step 6 uses only the already established quotient/regularity results and the cohomology definition: local lifts and explicit cancellation prove both the kernel and cokernel assertions. Sheaf quotient lifts are only local, and the proof explicitly permits further covers when an element lies in an image ideal. No surjectivity on sections of arbitrary quotients is assumed.

Step 7 uses the cone and shift formula of `def-weil-abstract-derived-category`, which I compared with `derived.tex`, label `definition-cone`. The shifted cone has B_n, B_n, B_m in degrees -1,0,1 and differentials ell^m and minus reduction. The degree -1 coordinate in the item is therefore a chain map with the stated sign; direct cohomology checks show it is a quasi-isomorphism of B_n-complexes.

Step 8 uses the same cone formula to define the strict reduction map in all three degrees. I verified the chain-level equality on a local lift: reduction of ell^(n'-m)x equals ell^(n-m)ell^(n'-n)x modulo ell^n. This is the actual transition, not a claim that two unidentified isomorphisms commute. For comparison across different coefficient levels, both maps are read after restriction to B_n'. The identity transition n'=n and n=m both work; for n=m the contractible complementary summand has differential -1.

For edge cases I checked empty T (zero sheaves), E=Q_ell, arbitrary ramification e, m=n=1, n=m, n'=n and n'-n at least m. The last case gives zero on B_m as required for the later pro-zero argument. A finite arithmetic check tested 36 combinations t=p^e with p=2,3, e=1,2, 1<=m<=3 and m<=n<=4, and every n<=n'<=5: kernel=image of a, injectivity of a, the augmentation kernel, and the transition equality all passed. This is a check of the local arithmetic formulas, not a substitute for the sheaf proof.

All steps are below 2000 characters. Steps 5–8 are elementary calculations from the preceding proved assertions and the displayed definitions, so they remain steps rather than generating duplicate or clause-only nodes. Every other non-elementary ingredient has a cited node. Seven generic off-unit tools are declared with their precise purpose in `split_report.tool_uses`; none replaces the unit's reconstruction route. The twelve proof dependencies are exactly the union of the eight `uses` lists. The statement dependencies are unchanged and cover all its named notions. Literal excerpts in `citations.json` were checked against the current node statements. Search records preserve the imported searches and add only the five searches actually run by Q97, using two distinct semantic phrasings; no service failure was reported as a no-match. The grep hit is a future-work comment at Mathlib/Algebra/Homology/LocalCohomology.lean:45, not a theorem.

## Validation

Server `srvcheck.py ... check_dag` passed: no finding introduced by the sandbox or on its nodes. The required `deliver.py Q97 lem-sp-ell-coefficient-fiber --no-push` exited 0 and printed `OK (not pushed) deliver/Q97/lem-sp-ell-coefficient-fiber at d31de0575bc: preflight passed`. Only this validation paragraph was updated after that dry run; the delivery push runs preflight again. No Lean file was written and no compiler or build tool was run.
