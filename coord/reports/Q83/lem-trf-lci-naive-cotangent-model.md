# Repair report: lem-trf-lci-naive-cotangent-model

## Files written

- Item: dag/nodes/sec-trace-formula/lem-trf-lci-naive-cotangent-model.json; unchanged statement, three assembly steps.
- lem-trf-standard-cotangent-chain-projection: statement; unsplit; no full Mathlib match.
- lem-trf-standard-cotangent-boundary-cokernel: statement; unsplit; no full Mathlib match.
- lem-trf-conormal-semilinear-difference-homotopy: statement; Mathlib leaf (exact semilinear Extension API).
- lem-trf-localized-presentation-homotopy-equivalence: statement; unsplit; no full Mathlib match.

## Attachments

None. The project declaration Algebra.CotangentResolution.Naive.exists_comparison in lean/Sheaf/RingTheory/NaiveCotangentComparison.lean:292-295 contains sorry. Searches of WeilConjectures by the item tag, naive cotangent, conormal, and truncation found no full finished comparison. The existing polynomial-presentation homotopy theorem is only the polynomial special case of the new localized assertion, not a substitute for it.

## WANTED

None. All source texts used are available in literature/stacks-project.

## What was wrong and repair

The return required distributing 8009 characters of argument, at least two comparable new statement-only unsplit nodes, and an assembly at most 3000 characters. The sandbox had only dispatcher marker files; no prior node, report, citations or searches were present. I copied the current live item, preserving its full statement, metadata, Lean record and historical searches. The copied ten-step proof agrees with the return's step lengths and is preserved verbatim below. No git command, repository write, compiler or Lean edit was used. The current source rather than an unavailable historical checkout is the baseline, and deliver.py rebases its own temporary delivery worktree.

The repair adds three unsplit arguments and a Mathlib leaf. Their workload is the standard chain projection (old steps 1-2), the explicit cokernel inverse (3-5), the induced-map/difference calculus (6-7, an exact Mathlib leaf), and the localized inverse construction (8 plus the inverse argument in 9 and the modulo-square part of 7). Choice independence in 9 and the semilinear square in 10 remain in assembly steps 2-3, citing the extracted statements. Thus no argument was replaced with an unexplained shorter claim. The new unsplit nodes have empty proof/proof_deps and null proof_origin; their eventual workers receive the complete mathematical statement, source, searches and the preserved argument here.

## Preserved original argument and allocation

### Old step 1 → lem-trf-standard-cotangent-chain-projection

Use [lem-trf-cotangent-resolution-coherence] with $R=A[B]$, augmentation $\epsilon:R\twoheadrightarrow B$, $I=\ker\epsilon$, and $Q_1=A[R]$, $Q_2=A[Q_1]$. Denote their respective polynomial variables by $X_b,Y_p,Z_f$. Write $M_n=\Omega^1_{Q_n/A}\otimes_{Q_n}B$, with $Q_0=R$. The two faces on $Q_1$ send $Y_p$ to $p$ and $X_{\epsilon(p)}$. On $Q_2$ the three faces send $Z_f$ to $f,Y_{d_0f},Y_{d_1f}$. Thus $L_{B/A}$ is represented by $\cdots\to M_2\xrightarrow{\partial_2}M_1\xrightarrow{\partial_1}M_0$. By [lem-weil-pbc-polynomial-ring-kahler-basis-any-variables], $M_1$ is free on $u_p=\mathrm dY_p\otimes1$ and $M_2$ is free on $\mathrm dZ_f\otimes1$. These are precisely the standard-resolution faces, not faces for an arbitrary presentation.

Original uses: lem-trf-cotangent-resolution-coherence, lem-weil-pbc-polynomial-ring-kahler-basis-any-variables.

### Old step 2 → lem-trf-standard-cotangent-chain-projection

Define $D:Q_1\to I/I^2$ by $D(f)=d_0(f)-d_1(f)\bmod I^2$. Both face maps have the same image in $B$, so the difference lies in $I$. It is additive, kills $A$, and satisfies $D(fg)=\overline fD(g)+\overline gD(f)$ because the product of two face differences lies in $I^2$. Hence [def-weil-pbc-kahler-differentials] gives a $B$-linear map $\rho:M_1\to I/I^2$, $\rho(u_p)=p-X_{\epsilon(p)}\bmod I^2$. Its composition with the conormal differential is $\partial_1$: both send $u_p$ to $\mathrm dp-\mathrm dX_{\epsilon(p)}$. Moreover $\rho(\partial_2(\mathrm dZ_f))=D(f)-D(Y_{d_0f})+D(Y_{d_1f})=0$: the last two terms subtract $d_0f-d_1f$ since $\epsilon d_0f=\epsilon d_1f$. Thus degree zero identity, degree minus one $\rho$, and zero in all lower degrees form a chain map $c:L_{B/A}\to C(R)$.

Original uses: def-weil-pbc-kahler-differentials.

### Old step 3 → lem-trf-standard-cotangent-boundary-cokernel

We compute $E=M_1/\operatorname{im}\partial_2$ explicitly. Let $t_p$ be the class of $u_p$. For each $f\in Q_1$, the defining relation is the class of $\mathrm df\otimes1$ minus $t_{d_0f}$ plus $t_{d_1f}$ equal to zero. In particular $f=Y_{X_b}$ gives $t_{X_b}=0$ for every $b\in B$. Taking $f=2Y_0$ gives $t_{2X_0}=-t_0$, and $f=Y_0^2$ gives $t_{X_0^2}=t_0$. For $h,k\in I$, the choices $f=Y_h+Y_k$ and $f=Y_hY_k$ now give $t_{h+k}=t_h+t_k-t_0$ and $t_{hk}=t_0$. These identities follow by differentiating the displayed polynomials using the Leibniz rule [def-weil-pbc-kahler-differentials]; their coefficients are evaluated in $B$, so the coefficients $\epsilon(h)$ and $\epsilon(k)$ in the product derivative vanish.

Original uses: def-weil-pbc-kahler-differentials.

### Old step 4 → lem-trf-standard-cotangent-boundary-cokernel

For $r\in R$, $h\in I$, set $b=\epsilon(r)$. The relations for $Y_rY_h$ and $Y_rY_0$ yield respectively $b t_h-t_{rh}+t_{X_bX_0}=0$ and $b t_0-t_0+t_{X_bX_0}=0$. Subtracting gives $t_{rh}-t_0=b(t_h-t_0)$. Together with Step 3 this says that $h\mapsto t_h-t_0$ is additive, is $R$-linear with the $R$-action through $\epsilon$, and kills $I^2$ (each product of two elements of $I$ maps to zero). It therefore defines a $B$-linear map $v:I/I^2\to E$. This uses just quotient-module relations and the computed identities, with no regular-sequence or finiteness hypothesis.

Original uses: (earlier explicitly proved relations only).

### Old step 5 → lem-trf-standard-cotangent-boundary-cokernel

The induced map $\overline\rho:E\to I/I^2$ is inverse to $v$. Indeed, for $h\in I$ one has $\overline\rho(t_h-t_0)=(h-X_0)-(0-X_0)=h\bmod I^2$. Conversely let $p\in R$ and $b=\epsilon(p)$. For $f=Y_p-Y_{X_b}$ the defining relation of $E$ becomes $t_p-t_{X_b}-t_{p-X_b}+t_0=0$. Since $t_{X_b}=0$, this reads $v\overline\rho(t_p)=t_p$. The $t_p$ generate $E$, so both composites are identities. Therefore $\rho$ identifies $M_1/\operatorname{im}\partial_2$ with $I/I^2$ and intertwines the remaining differential with the conormal differential by Step 2. The degree-zero identity then makes $\tau_{\geq-1}L_{B/A}\to C(R)$ an isomorphism of the displayed two-term complexes. Its construction commutes strictly with ring squares: $X_b,Y_p,Z_f$ map to the variables indexed by their images, and every formula above commutes with those maps.

Original uses: (earlier explicitly proved relations only).

### Old step 6 → lem-trf-conormal-semilinear-difference-homotopy

For a surjection $P\to B$ as in the statement, put $C(P)=[J/J^2\to\Omega^1_{P/A}\otimes_PB]$. Any map $a:R\to P$ over $B$ induces a chain map $C(a)$: on conormal classes it sends $[h]$ to $[a(h)]$, and on differential tensors it sends $\mathrm dr\otimes b$ to $\mathrm da(r)\otimes b$. The map on conormal quotients is well defined since $a(I^2)\subset J^2$; the map on differentials follows from [def-weil-pbc-kahler-differentials], and the two maps commute with the differential on each $[h]$. These formulas work also for semilinear maps over a base-ring square, preserve identities, and compose termwise. A lift $a:R=A[B]\to P$ exists: choose a preimage in $P$ of each $b\in B$ and apply [def-weil-pbc-mv-polynomial-ring].

Original uses: def-weil-pbc-kahler-differentials, def-weil-pbc-mv-polynomial-ring.

### Old step 7 → lem-trf-conormal-semilinear-difference-homotopy

For later independence and inverses, the following difference calculation applies to maps of these complexes, including semilinear maps. Suppose $a,b:Q\to T$ over the same ring square and quotient $B\to B'$ induce the same map to $B'$, and $K=\ker(T\to B')$. Then $a-b$ modulo $K^2$ is a derivation into the $B'$-module $K/K^2$: $a(xy)-b(xy)=a(x)(a(y)-b(y))+(a(x)-b(x))b(y)$. By [def-weil-pbc-kahler-differentials] it gives $H:\Omega^1_{Q/A}\otimes_QB\to K/K^2$, $H(\mathrm dx\otimes b_0)=b'_0[a(x)-b(x)]$. On conormal generators $H\,\mathrm d([h])=[a(h)-b(h)]$, and on differential generators $\mathrm dH(\mathrm dx\otimes b_0)=b'_0(\mathrm da(x)-\mathrm db(x))$. Thus $C(a)-C(b)=\mathrm dH+H\mathrm d$. The same calculation is valid for maps into $T/K^2$, interpreting differentials after tensoring with $B'$: $\mathrm d(K^2)\otimes B'=0$ by the Leibniz rule. This also verifies independence of lifts represented only modulo a squared ideal.

Original uses: def-weil-pbc-kahler-differentials.

### Old step 8 → lem-trf-localized-presentation-homotopy-equivalence

If $P$ is polynomial, [lem-weil-pbc-nl-presentations-homotopy-equivalent] makes $C(a):C(R)\to C(P)$ a homotopy equivalence for any lift $a$. For the allowed general case write $P=W^{-1}F$, $F=A[x_e]$. Lift the images of $x_e$ in $B$ to $R/I^2$ by [def-weil-pbc-mv-polynomial-ring]. This makes $D=R/I^2$ an $F$-algebra, with square-zero ideal $N=I/I^2$, and $D/N=B$. The given map $P\to B$ is an $F$-algebra map. Applying [lem-weil-pbc-localization-square-zero-lifting] yields $\ell:P\to R/I^2$ lifting it. Since $\ell(J)\subset N$ and $N^2=0$, $\ell$ induces a map $J/J^2\to I/I^2$. The derivation $\mathrm d:R\to\Omega^1_{R/A}\otimes_RB$ vanishes on $I^2$, so it descends to $R/I^2$ and, composed with $\ell$, gives the degree-zero map by [def-weil-pbc-kahler-differentials]. These maps form a chain map $C(\ell):C(P)\to C(R)$.

Original uses: lem-weil-pbc-nl-presentations-homotopy-equivalent, def-weil-pbc-mv-polynomial-ring, lem-weil-pbc-localization-square-zero-lifting, def-weil-pbc-kahler-differentials.

### Old step 9 → assembly step 2 and lem-trf-localized-presentation-homotopy-equivalence

The two composites in Step 8 are homotopic to identities by Step 7. On $R$ compare $\ell a:R\to R/I^2$ with the quotient map; they have the same reduction to $B$, and induce $C(\ell)C(a)$ and $1_{C(R)}$. In the other direction $a$ descends to $\bar a:R/I^2\to P/J^2$. Compare $\bar a\ell:P\to P/J^2$ with the quotient map; they induce $C(a)C(\ell)$ and $1_{C(P)}$. Thus $C(a)$ is a homotopy equivalence also when $P$ is a localization. Step 7 also says that all choices of $a$ give the same map in the homotopy category, hence the same map in the derived category [def-weil-abstract-derived-category]. Composing the canonical map $c$ of Steps 2–5 with $C(a)$ now defines the required canonical morphism $L_{B/A}\to C(P)$, independent of every lift. It induces the asserted isomorphism on truncations, since Step 5 identifies the truncation with $C(R)$ and $C(a)$ is a homotopy equivalence.

Original uses: def-weil-abstract-derived-category.

### Old step 10 → assembly step 3

Finally consider any given diagram $A\to A'$, $B\to B'$, $P\to P'$. Put $R'=A'[B']$ and choose lifts $a:R\to P$, $a':R'\to P'$. Let $s:R\to R'$ be the standard map $X_b\mapsto X_{b'}$. The composites $R\xrightarrow{a}P\to P'$ and $R\xrightarrow{s}R'\xrightarrow{a'}P'$ have the same reduction to $B'$. Step 7 gives a semilinear homotopy between their maps $C(R)\to C(P')$. The canonical comparison $c$ commutes strictly with the standard resolution map by Step 5 and [lem-trf-cotangent-resolution-coherence]. Composing that strict square with this homotopy proves the required naturality square in the derived category (the target is regarded as a $B$-complex by restriction of scalars). The map $C(P)\to C(P')$ is exactly the formula of Step 6, including for localized presentations. This proves all naturality assertions. The calculation only quotients $M_1$ by $\operatorname{im}\partial_2$; it makes no claim on the lower cohomology or any finite generation.

Original uses: lem-trf-cotangent-resolution-coherence.

## Review by Q83

I read Stacks cotangent.tex Tags 08RB (lemma-relation-with-naive-cotangent-complex) and 08UP (remark-explicit-comparison-map), including their omitted-verification notices, and algebra.tex Tag 00S1 (lemma-NL-homotopy), its full proof, equation-functoriality-NL, and Tag 04EG (lemma-localization-formally-etale). I verified these tags against tags/tags. I also read the current main-20261015 blueprint proof of lem-trf-local-term-locality, the trace-formula chapter and sk-i-curve-zero unit. This repair follows the item's existing ring-theoretic subargument; it changes no chapter/unit route and introduces no SGA source.

The first new node records exactly the 08UP face-difference chain map: its universal-derivation check is the old step 2, with the actual standard faces in old step 1. It also records strict naturality of those explicit formulas. It does not assert a truncation isomorphism. The second new node isolates the substantial quotient calculation that the source omits: its hypothesis that rho kills the incoming boundary is supplied by the first node, while the inverse h ↦ t_h − t_0, additivity, scalar compatibility and annihilation of I² are precisely old steps 3-5. Keeping rho's chain-map construction and its cokernel bijectivity separate avoids merely restating the item's derived comparison.

For the third new node I read Mathlib RingTheory/Extension/Basic.lean:102-107,330-341,465-504 and Extension/Cotangent/Basic.lean:53-67,142-207,212-319. The extension API allows distinct source and target base rings, and its maps are already linear after restricting the target scalars. Hom.sub, Hom.sub_tmul, Cotangent.map_sub_map and CotangentSpace.map_sub_map give exactly the difference derivation and both homotopy identities, not just equality on H1. Cotangent.map_mk, CotangentSpace.map_tmul and the respective map_id/map_comp results give the generator formulas and composition, while map_comp_cotangentComplex supplies the chain-map identity. This is a Mathlib leaf, not new proof work. Tensor factors are commuted canonically between the item's Ω tensor B convention and Mathlib's B tensor Ω convention.

The fourth new node is the localized argument, which 00S1 alone does not state. I checked 04EG against the existing square-zero-lifting node's full statement: after lifting the polynomial variables of F=A[E] into D=R/I², this is an F-algebra, N=I/I² is square-zero, D/N=B and P is a localization of F. Thus that lifting statement applies with exactly its hypotheses. The resulting ell sends J into N and J² to zero. The derivation on R kills I² by Leibniz, so the displayed map g is well defined and commutes with the conormal differential. To verify the two inverse homotopies, compare ell a with the quotient R→R/I² and compare a-bar ell with P→P/J². The same difference calculation applies to maps into these squared-ideal quotients: differences lie in I/I² or J/J², products of differences vanish, and d(I²) tensor B and d(J²) tensor B vanish. Explicitly the homotopy sends dx tensor b to b times the difference of the two images. Its composite with the conormal differential is the difference on kernel classes, and differentiating that difference is the difference on differential generators. This preserves, rather than hides, the final clause of old step 7. In particular no nonexistent ring inverse P→R is required. These are the two inverse identities recorded in the new node. The polynomial case is W={1}, so the existing polynomial-only equivalence node need not be applied as if it covered localizations.

I checked every assembly citation against its statement, not its proof. In assembly step 1 the resolution-coherence node identifies K with L and gives standard functoriality. The chain-projection node gives rho partial_2=0 and delta rho=partial_1, exactly the hypothesis and remaining-differential compatibility needed by the boundary-cokernel node. That second node gives an actual module isomorphism on the good-truncation term, so together with the degree-zero identity this is an isomorphism of the two-term complexes and hence in D(B). The derived-category node supplies the localization interpretation. There is no inference of higher vanishing.

In assembly step 2 the localized-presentation node applies because R=A[B] is polynomial with a surjective evaluation and the item's P is localized polynomial; the unlocalized case is W={1}. It gives both existence of the lift and homotopy equivalence for every lift. The semilinear difference-homotopy leaf gives the exact displayed induced maps and independence of the chosen lift. The derived-category statement explicitly allows the equivalent localization of the homotopy category, so homotopic maps have equal images and homotopy equivalences become invertible. The comparison is therefore the composition of precisely the two available isomorphisms on the truncated object.

In assembly step 3 the same leaf is used over the given A→A′, B→B′ square. Both pa and a′ s have reduction B→B′, so the leaf's common-quotient hypothesis holds. Its chain-map composition rule gives C(p)C(a) and C(a′)C(s), and its homotopy equates these after passage to the derived category. The chain-projection node supplies strict commutation with the standard resolution map; the coherence node identifies that map with the specified cotangent functoriality. Thus the resulting square commutes for the correct restriction of scalars, rather than making an unsupported claim about scalar extension. citations.json contains a verbatim statement excerpt for every use in all three steps.

Small cases were checked without a compiler. If B is the zero ring, all displayed B-modules vanish; this also handles 0∈W. If I=0, the cokernel claim says E=0 and the inverse is the zero map, consistent with the generator relations. For char 2 and for arbitrary torsion in A the old calculation uses no division by 2: t_(2X_0)=−t_0 remains valid and yields the additive correction. With no variables the inverse construction only uses the given base map and localization lifting; with infinitely many variables every polynomial and derivative has finite support. When the two maps a_0,a_1 coincide, H=0; for identity squares the same formulas give the identity and zero comparison homotopy. The example P=Z[1/2] and R=Z[B] with B=P shows why an inverse P→R cannot be assumed, while ell:P→R/I² exists as stated. No regular sequence, finite generation, Noetherianity, flatness or finite presentation was inserted.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 of delivery-errors.md against these files. The new unsplit nodes are statement-only, self-contained, use ordinary TeX, and have explicit sources and blueprint ancestry. Definitions are either cited (polynomials and Kähler differentials) or spelled out (localization, semilinearity and the complexes/homotopies). Mathlib candidates were read; services returning rate limits are recorded as unavailable. The searches and duplicate comparisons below precede node creation; no unsupported source result is substituted for a node in the assembly. The subarguments are strictly smaller than the derived comparison, no dependency points back to the item, and the new modules/statements are independent enough for separate workers. The largest assembly step is below 2000 characters. I corrected the returned proof's excessive workload by extracting its arguments and corrected the draft leaf's Extension.ofSurjective line reference to 102; no mathematical statement change was needed.

## Searches and blueprint

The new nodes each have two distinct LeanFinder phrasings, a LeanSearch attempt, a Loogle query, and a grep query in searches.jsonl. Full returned hits are retained in the per-node search text files. Three LeanSearch attempts returned HTTP rate-limit messages and are recorded unavailable, not no match. The localization LeanSearch succeeded and found derivation/square-zero APIs, but not the full equivalence. Extra greps read the actual difference-homotopy, conormal-map, identity and composition declarations. The quotient and chain-map searches returned generic Moore-complex/presentation machinery, not the specific standard-resolution statements. The localization-away conormal splitting was read at Extension/Cotangent/LocalizationAway.lean:188-219; it identifies a conormal module for a composite principal-localization presentation, not this general localized-presentation homotopy equivalence. Smooth/Basic.lean:202-224 provides an infinitesimal map, not all the inverse chain-homotopy assertions.

Whole-DAG searches used the source tags 08UP, 08RB, 00S1, 04EG, keywords cotangent/conormal/homotopy/cokernel, and the candidate declaration names. Whole-blueprint searches used cotangent, conormal, homotopy, 08UP, 00S1, 04EG; no imported blueprint node states an extracted claim. The ancestor tool gives lem-trf-local-term-locality; each new from.via begins with this item and keeps its prior via chain, with an exact old-step allocation in from.place. Searches of both Lean roots find polynomial-only equivalences and H1 consequences but no completed standard low-degree comparison. In particular def-trf-naive-cotangent-comparison-data defines requested data without asserting existence and is not a theorem to cite for any of these arguments.

## What could not be finished

None for stage 1. The three new unsplit arguments intentionally await other workers, as the return requires. No stage-2 or stage-3 work was attempted.

## Not duplicates

lem-trf-standard-cotangent-chain-projection vs lem-trf-cotangent-base-change-adjunct-formula: the existing node identifies the derived scalar-extension adjunct of the standard cotangent functoriality map when a base-changed resolution and a K-flat model are supplied. It neither constructs the face-difference map to I/I² nor proves delta rho = partial_1 and rho partial_2 = 0; those are the extracted chain-projection lemma, without the extra base-change and flatness hypotheses.

lem-trf-standard-cotangent-chain-projection vs lem-trf-polynomial-resolution-universal-evaluation: the existing node identifies signed bar models of derived colimits, evaluates them on augmented polynomial resolutions, and compares their semilinear functoriality. It has no conormal module I/I², face-difference map rho, or boundary identities delta rho = partial_1 and rho partial_2 = 0. The extracted node constructs exactly that two-term chain projection and its strict naturality; bar evaluation cannot supply it.

lem-trf-standard-cotangent-chain-projection vs lem-trf-constant-polynomial-resolution-retraction: the existing node contracts the constant resolution of an already polynomial algebra and describes its differential augmentation to Omega[0]; the new node constructs the face-difference map into I/I² for an arbitrary quotient B and proves annihilation of the second standard boundary.

lem-trf-standard-cotangent-chain-projection vs lem-trf-cotangent-bar-arrow-comparisons: the existing node identifies the two transitivity arrows for a triple of rings with pair-site bar maps; the new node concerns the explicit degree-minus-one conormal projection of one standard resolution, not transitivity or a bar comparison.

lem-trf-standard-cotangent-chain-projection vs lem-trf-cotangent-bar-diagram-compatibility: the existing node compares pair-site short exact sequences and their bar maps under diagrams of ring triples; the new node proves well-definedness and the two differential identities for the face-difference projection to I/I², none of which that statement supplies.

lem-trf-standard-cotangent-chain-projection vs lem-trf-polynomial-square-bar-naturality: the existing node supplies semilinear simplicial maps and their compatibility with derived bar comparisons; the new node constructs rho into the conormal module, proves delta rho = partial_1 and rho partial_2 = 0, and proves strict naturality of that projection. The bar statement does not assert any of these conormal projection identities.

lem-trf-standard-cotangent-chain-projection vs lem-trf-lci-koszul-duality-determinant-comparison: the new node constructs the standard simplicial face-difference chain map for any ring map; the existing node identifies signed Koszul duality with determinant comparisons for scheme local complete intersections and uses the present item as a dependency, so it cannot supply this ring-level chain map.

lem-trf-standard-cotangent-boundary-cokernel vs lem-trf-lci-koszul-duality-determinant-comparison: the new node calculates the explicit cokernel of the second standard simplicial differential for arbitrary rings; the existing node gives a derived sheaf duality/determinant comparison under Koszul-regularity and local-freeness assumptions, not this cokernel calculation.

lem-trf-conormal-semilinear-difference-homotopy vs def-trf-naive-cotangent-comparison-data: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node defines the full comparison datum without an existence theorem.

lem-trf-conormal-semilinear-difference-homotopy vs lem-trf-lci-naive-cotangent-model: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node assembles the full natural derived cotangent truncation comparison for all polynomial and localized polynomial presentations.

lem-trf-conormal-semilinear-difference-homotopy vs lem-per-jacobian-torsion-etale-shrink: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node finds an etale open after a torsion Jacobian assumption on an adic completion.

lem-trf-conormal-semilinear-difference-homotopy vs lem-weil-pbc-nl-presentation-h1-functoriality: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node only asserts induced H1-map independence for polynomial presentations, not equality up to chain homotopy for arbitrary surjections.

lem-trf-conormal-semilinear-difference-homotopy vs lem-weil-pbc-complete-intersection-fraction-field-cotangent-model: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node identifies homology over a finitely generated fraction-field complete-intersection presentation, not the standard simplicial boundary quotient.

lem-trf-conormal-semilinear-difference-homotopy vs lem-weil-pbc-conormal-module-principal-localization: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node gives a stabilized conormal-module isomorphism for finite presentations after principal localization, not an explicit chain homotopy inverse.

lem-trf-conormal-semilinear-difference-homotopy vs lem-weil-pbc-smooth-localization-conormal-split: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node proves splitting of the localized conormal sequence under smoothness assumptions.

lem-trf-conormal-semilinear-difference-homotopy vs lem-weil-pbc-two-term-homotopy-equivalence-direct-sum: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node deduces an isomorphism of direct sums from already supplied homotopies; it does not construct the conormal maps or homotopies.

lem-trf-conormal-semilinear-difference-homotopy vs lem-weil-pbc-etale-ring-map-conormal-criterion: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node is a finite-presentation etaleness criterion involving a Jacobian isomorphism.

lem-trf-conormal-semilinear-difference-homotopy vs lem-weil-pbc-jacobi-zariski-surjection-h1: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node computes H1 for a surjective ring map using its canonical polynomial presentation, not the second standard-resolution boundary cokernel.

lem-trf-conormal-semilinear-difference-homotopy vs lem-weil-pbc-jacobi-zariski-homology-sequence: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node gives the Jacobi–Zariski exact sequence for a triple of rings, not explicit homotopies or the standard simplicial quotient.

lem-trf-conormal-semilinear-difference-homotopy vs lem-weil-pbc-smooth-at-prime-free-conormal-basis: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node constructs a finite conormal basis near a smooth prime.

lem-trf-conormal-semilinear-difference-homotopy vs lem-weil-pbc-cartier-equality: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node is the dimension formula for a finitely generated field extension.

lem-trf-conormal-semilinear-difference-homotopy vs lem-weil-pbc-polynomial-ring-h1-cotangent-vanishing: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node asserts H1 vanishing for finite polynomial algebras, not the full low-degree standard-resolution calculation.

lem-trf-conormal-semilinear-difference-homotopy vs lem-weil-pbc-smooth-free-differentials-strictly-standard-power: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node constructs strictly standard powers from stably free differentials.

lem-trf-conormal-semilinear-difference-homotopy vs lem-weil-pbc-pth-root-presentation-differentials: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node computes differentials of a specific pth-root algebra.

lem-trf-conormal-semilinear-difference-homotopy vs lem-weil-pbc-jacobi-zariski-regular-sequence-left-injective: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node is the left-injectivity clause for a regular-sequence Jacobi–Zariski sequence.

lem-trf-conormal-semilinear-difference-homotopy vs lem-weil-pbc-colimit-etale-ring-map: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node descends etaleness of a finite-presentation map along a directed ring colimit.

lem-trf-conormal-semilinear-difference-homotopy vs lem-weil-pbc-nl-presentations-homotopy-equivalent: the new node gives the actual semilinear chain maps and explicit homotopies for arbitrary surjections, including changing both base and quotient rings, whereas the existing node asserts homotopy equivalence only for polynomial presentations over the same base and quotient, without arbitrary-map difference homotopies or localized rings.

lem-trf-standard-cotangent-chain-projection vs def-trf-cotangent-resolution-data: the new node constructs the explicit standard-resolution chain projection and strict ring-square commutation, without claiming the derived truncation isomorphism, whereas the existing node states Standard polynomial cotangent resolution and coherence data.

lem-trf-standard-cotangent-chain-projection vs lem-trf-cotangent-sheaf-model: the new node constructs the explicit standard-resolution chain projection and strict ring-square commutation, without claiming the derived truncation isomorphism, whereas the existing node states Cotangent sheaf model and its standard functoriality comparison.

lem-trf-standard-cotangent-chain-projection vs lem-trf-cotangent-resolution-coherence: the new node constructs the explicit standard-resolution chain projection and strict ring-square commutation, without claiming the derived truncation isomorphism, whereas the existing node states Functorial standard resolutions and comparison with arbitrary polynomial resolutions.

lem-trf-standard-cotangent-chain-projection vs lem-trf-affine-cotangent-comparison: the new node constructs the explicit standard-resolution chain projection and strict ring-square commutation, without claiming the derived truncation isomorphism, whereas the existing node states Sheaf cotangent stalks, section maps and ring localization.

lem-trf-standard-cotangent-chain-projection vs lem-trf-cotangent-transitivity-triangle: the new node constructs the explicit standard-resolution chain projection and strict ring-square commutation, without claiming the derived truncation isomorphism, whereas the existing node states Transitivity triangle for ring cotangent complexes.

lem-trf-standard-cotangent-chain-projection vs lem-trf-smooth-cotangent-identification: the new node constructs the explicit standard-resolution chain projection and strict ring-square commutation, without claiming the derived truncation isomorphism, whereas the existing node states Cotangent complex and differential basis for a polynomial algebra.

lem-trf-standard-cotangent-chain-projection vs def-trf-naive-cotangent-comparison-data: the new node constructs the explicit standard-resolution chain projection and strict ring-square commutation, without claiming the derived truncation isomorphism, whereas the existing node defines the full comparison datum without an existence theorem.

lem-trf-standard-cotangent-chain-projection vs lem-trf-cotangent-flat-base-change: the new node constructs the explicit standard-resolution chain projection and strict ring-square commutation, without claiming the derived truncation isomorphism, whereas the existing node states Derived base change for ring cotangent complexes.

lem-trf-standard-cotangent-chain-projection vs lem-trf-lci-naive-cotangent-model: the new node constructs the explicit standard-resolution chain projection and strict ring-square commutation, without claiming the derived truncation isomorphism, whereas the existing node assembles the full natural derived cotangent truncation comparison for all polynomial and localized polynomial presentations.

lem-trf-standard-cotangent-chain-projection vs lem-trf-lci-cotangent-presentation: the new node constructs the explicit standard-resolution chain projection and strict ring-square commutation, without claiming the derived truncation isomorphism, whereas the existing node gives the geometric LCI model, Tor amplitude and base-change assertions with Koszul regularity.

lem-trf-standard-cotangent-chain-projection vs lem-sfb-etale-source-adjunction-line: the new node constructs the explicit standard-resolution chain projection and strict ring-square commutation, without claiming the derived truncation isomorphism, whereas the existing node states Etale source locality of the canonical relative adjunction line.

lem-trf-standard-cotangent-chain-projection vs lem-sfb-scheme-cotangent-transitivity: the new node constructs the explicit standard-resolution chain projection and strict ring-square commutation, without claiming the derived truncation isomorphism, whereas the existing node states Functoriality and transitivity triangle for cotangent complexes of schemes.

lem-trf-standard-cotangent-boundary-cokernel vs def-trf-naive-cotangent-comparison-data: the new node computes the standard second-boundary cokernel by its explicit inverse, under the supplied rho-annihilation hypothesis, whereas the existing node defines the full comparison datum without an existence theorem.

lem-trf-standard-cotangent-boundary-cokernel vs lem-trf-lci-naive-cotangent-model: the new node computes the standard second-boundary cokernel by its explicit inverse, under the supplied rho-annihilation hypothesis, whereas the existing node assembles the full natural derived cotangent truncation comparison for all polynomial and localized polynomial presentations.

lem-trf-standard-cotangent-boundary-cokernel vs lem-trf-lci-cotangent-presentation: the new node computes the standard second-boundary cokernel by its explicit inverse, under the supplied rho-annihilation hypothesis, whereas the existing node gives the geometric LCI model, Tor amplitude and base-change assertions with Koszul regularity.

lem-trf-localized-presentation-homotopy-equivalence vs def-trf-naive-cotangent-comparison-data: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node defines the full comparison datum without an existence theorem.

lem-trf-localized-presentation-homotopy-equivalence vs lem-trf-lci-naive-cotangent-model: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node assembles the full natural derived cotangent truncation comparison for all polynomial and localized polynomial presentations.

lem-trf-localized-presentation-homotopy-equivalence vs lem-per-jacobian-torsion-etale-shrink: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node finds an etale open after a torsion Jacobian assumption on an adic completion.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-localization-square-zero-lifting: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node gives a ring-map lift across a square-zero ideal, not maps or homotopy equivalence of conormal complexes.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-nl-presentation-h1-functoriality: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node only asserts induced H1-map independence for polynomial presentations, not equality up to chain homotopy for arbitrary surjections.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-complete-intersection-fraction-field-cotangent-model: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node identifies homology over a finitely generated fraction-field complete-intersection presentation, not the standard simplicial boundary quotient.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-conormal-module-principal-localization: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node gives a stabilized conormal-module isomorphism for finite presentations after principal localization, not an explicit chain homotopy inverse.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-polynomial-local-completion-formally-smooth: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node asserts adic formal smoothness of a completed polynomial local ring.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-smooth-localization-conormal-split: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node proves splitting of the localized conormal sequence under smoothness assumptions.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-two-term-homotopy-equivalence-direct-sum: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node deduces an isomorphism of direct sums from already supplied homotopies; it does not construct the conormal maps or homotopies.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-etale-ring-map-conormal-criterion: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node is a finite-presentation etaleness criterion involving a Jacobian isomorphism.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-jacobi-zariski-surjection-h1: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node computes H1 for a surjective ring map using its canonical polynomial presentation, not the second standard-resolution boundary cokernel.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-jacobi-zariski-homology-sequence: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node gives the Jacobi–Zariski exact sequence for a triple of rings, not explicit homotopies or the standard simplicial quotient.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-smooth-at-prime-free-conormal-basis: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node constructs a finite conormal basis near a smooth prime.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-cartier-equality: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node is the dimension formula for a finitely generated field extension.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-polynomial-ring-h1-cotangent-vanishing: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node asserts H1 vanishing for finite polynomial algebras, not the full low-degree standard-resolution calculation.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-smooth-free-differentials-strictly-standard-power: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node constructs strictly standard powers from stably free differentials.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-pth-root-presentation-differentials: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node computes differentials of a specific pth-root algebra.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-field-cohen-power-series-formally-smooth: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node asserts adic formal smoothness of power series over a characteristic-zero field or a Cohen ring.

lem-trf-localized-presentation-homotopy-equivalence vs new-separably-generated-differentials-basis: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node gives a differential basis from a separating transcendence basis.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-jacobi-zariski-regular-sequence-left-injective: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node is the left-injectivity clause for a regular-sequence Jacobi–Zariski sequence.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-colimit-etale-ring-map: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node descends etaleness of a finite-presentation map along a directed ring colimit.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-nl-presentations-homotopy-equivalent: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node asserts homotopy equivalence only for polynomial presentations over the same base and quotient, without arbitrary-map difference homotopies or localized rings.

lem-trf-localized-presentation-homotopy-equivalence vs lem-weil-pbc-smooth-over-field-regular-local: the new node constructs a chain homotopy inverse through the squared-ideal quotient for arbitrary localized polynomial presentations, whereas the existing node proves regularity of local rings of smooth algebras over a field.


## Validation

### Landing-refusal repair and current-DAG review, 2026-10-22

The returned delivery was approved mathematically but refused landing because its side completion had not been promoted to the live queue. I continued the retained sandbox rather than replacing its proof, searches or reports. The first required dry run in this repair exited successfully at fa0174885bd. I then compared returned-item.json with the current read clone's item: every JSON field is identical. The current released stage-1 repair note still requires at least two new arguments and a short assembly. The retained four-node extraction satisfies that order; no target statement, chapter or unit route changes are required.

I reread the current statements of lem-trf-cotangent-resolution-coherence, def-weil-abstract-derived-category, def-weil-pbc-kahler-differentials and def-weil-pbc-mv-polynomial-ring, and all four extracted statements. The resolution statement supplies precisely the standard alternating complex and its semilinear functoriality, and the derived-category statement explicitly permits localization of the homotopy category. Thus all three assembly steps retain the hypotheses described in the signed review above. All eleven citations.json quotes remain verbatim substrings of those current statements. I also reread the supporting square-zero localization statement and Stacks 08RB/08UP, 00S1 and 04EG: the localized inverse uses the square-zero quotient R/I², never an asserted inverse P→R. Rechecked zero rings, empty variable sets, infinite variable sets, coincident presentation maps and characteristic two; no extra hypothesis arises.

The current-DAG tag scan found lem-trf-lci-koszul-duality-determinant-comparison in addition to the previously documented pairs. I read its complete statement and dependencies and added both missing comparisons under Not duplicates. It is a scheme-level Koszul/determinant assertion which depends on this item; citing it here would introduce a cycle and would not provide either extracted standard-resolution calculation. Other previously documented tag comparisons remain present. In assembly step 2 I now name the induced truncated map bar-c and display the actual composition Q(C(a))Q(bar-c); this makes the two invertible factors and their domains explicit rather than leaving the factor implicit. The mathematical statement of every node and the allocation of every original argument are retained.

The existing searches.jsonl and recorded hits were reread; the search questions and all new-node statements are unchanged, so no searches were invented or unnecessarily repeated. The delivery tool fetches origin/sheaf-dag and overlays only worker-owned fields in its temporary delivery tree, preserving current maintainer metadata. A fresh final dry run and push follow these content and report repairs.

The first server dry run required the explicit mathlib_match.line field, even though the declaration locations were already in how. Added line 311, verified against the pinned Cotangent/Basic.lean, and reran the required dry run.


### Continued landing-refusal repair: refreshed live-DAG duplicate review

The resumed dry run exited with a duplicate-check failure naming four newly present 08QL nodes. I opened the full current statements of lem-trf-constant-polynomial-resolution-retraction, lem-trf-cotangent-bar-arrow-comparisons, lem-trf-cotangent-bar-diagram-compatibility and lem-trf-polynomial-square-bar-naturality. The first has polynomial target and computes a constant-resolution contraction; the other three identify bar/transitivity comparison maps. None constructs the conormal face-difference map or gives its two boundary identities. I added four explicit pairs under Not duplicates rather than treating a shared source tag as a mathematical match. These nodes are not used in the assembly.

For the requested rebase I compared returned-item.json with the current repository item field by field: they are identical, so no cited statement or hypothesis changed between that returned baseline and this current read clone. I reread all current external statements cited by the three assembly steps: resolution-coherence still supplies the specified alternating complex and strict standard maps, and the derived-category definition still includes localization of the homotopy category. The Kähler and polynomial definitions still supply the same universal properties used by the extracted statements. All eleven citation excerpts remain literal substrings. I reread 08RB/08UP, 00S1 and 04EG at their source labels and the recorded Mathlib search results; the existing search questions remain unchanged. The four new-node statements and the full preserved old argument remain intact, with three unsplit nodes and one Mathlib leaf. This report and the item's split summary now record the actual current-DAG repair; deliver.py constructs its commit on freshly fetched origin/sheaf-dag, preserving maintainer fields.


### Current-DAG repair review by Q83, 2026-10-23

I resumed the retained delivery and ran the required dry run first. It exited with a new duplicate-review diagnostic for lem-trf-polynomial-resolution-universal-evaluation (08QL). I read that entire current statement: it supplies signed comparisons between bar complexes and polynomial-resolution evaluation, including their naturality, but no conormal quotient or face-difference projection. The pair now recorded under Not duplicates explains precisely why it cannot replace the extracted chain-projection lemma. This is a repair to the current DAG review, not an unchanged re-push.

The retained returned-item.json and the current repository item are identical field by field. I reread all current statements used by the assembly (resolution-coherence and the derived-category definition, together with all four extracted statements), and the Kähler/polynomial definitions and square-zero localization lifting statement underlying those extracted arguments. Step 1 still obtains both boundary identities from the chain-projection node and the explicit quotient isomorphism from the boundary-cokernel node; step 2 still uses the localized equivalence for the surjective polynomial presentation A[B] and choice-independence from the difference homotopy; step 3 still applies that homotopy over the actual ring square and restricts target scalars. All eleven citation quotes are literal substrings of the statements now read. No hypothesis or mathematical statement changed.

I reread cotangent.tex at 08RB, 08UP and 08QL and algebra.tex at 00S1 and 04EG, and checked the Mathlib semilinear map and homotopy declarations at the locations recorded in mathlib_match. The retained search log and hits answer the unchanged search questions, so the searches are reused. The zero-ring, empty/infinite variable, characteristic-two, and equal-map checks in the signed review above still apply: no division, finite generation or inverse ring map P→R is used. The assembly steps are all below 2000 characters and total less than 3000; the three unsplit arguments and one Mathlib leaf are retained. The delivery tool will construct the repaired commit over its freshly fetched current origin/sheaf-dag.

The first push after the passing dry run was refused without pushing because the current DAG gained lem-trf-cotangent-base-change-adjunct-formula (08QL). I opened its entire statement and checked its added base-changed-resolution and K-flatness hypotheses. It proves the scalar-extension adjunct formula, not the conormal projection, and is now compared explicitly under Not duplicates. The assembly cites none of its results; all retained citations remain valid. A new dry run precedes the next push.


### Renewed landing-refusal repair by Q83, 2026-10-23

The retained returned-item.json and the current repository item are identical in every JSON field. Comparing the delivery with the current item shows exactly the intended three differing fields: proof, proof_deps and split_report; statement, statement dependencies, source, blueprint ancestry, Lean and maintainer records agree. All four extracted nodes are still absent from this read clone. The required initial dry run completed successfully at 9537f3cf249 before this repair's edits. I retained all prior arguments, reports, source references and search logs.

I reread each current assembly dependency's complete statement. In step 1 resolution-coherence supplies the actual standard alternating complex, chain-projection supplies delta rho = partial_1 and rho partial_2 = 0, and boundary-cokernel supplies precisely the induced quotient isomorphism. In step 2 localized-presentation-homotopy-equivalence applies to the polynomial surjection A[B] and the given localized polynomial P; the difference-homotopy leaf supplies independence of a, and the derived-category definition explicitly allows passage through the homotopy category. I made the factorization c = bar-c pi explicit, so the original derived morphism and its asserted truncation map are visibly related. In step 3 I wrote the derived naturality equation itself, obtained by composing the cited difference homotopy with strict standard-resolution naturality. The target is still restricted along B to B-prime; no scalar-extension identification is presumed. These are proof clarifications to the rebased split, not an unchanged re-push.

All eleven citations.json quotes are still verbatim parts of those statements. I reread Stacks cotangent.tex at 08RB and 08UP, including the omitted verifications, algebra.tex at 00S1 and 04EG, and Mathlib's Extension maps and both map_sub_map identities at the recorded lines. The localized inverse continues to land in R/I squared, whose square-zero ideal is I/I squared; no inverse P to R is used. Empty and infinite variable sets, zero quotient rings and characteristic two require no added hypotheses. The project exists_comparison theorem at lean/Sheaf/RingTheory/NaiveCotangentComparison.lean:292 still has sorry, and the project-source searches yield no exact finished attachment.

The retained searches.jsonl answers unchanged questions; its unavailable LeanSearch responses remain labelled unavailable, and no searches were invented or repeated. The initial current-server preflight accepted the existing duplicate comparisons. All new nodes remain statement-only (three unsplit and one Mathlib leaf), and the assembly remains below the 3000-character limit. A fresh final dry run and then the authorized push follow these edits.
