# Stage-1 repair: Q19

## Files written

- dag/nodes/sec-trace-formula/lem-trf-relative-completion-etale-approximation.json: unchanged statement; four-step assembly, 1859 characters.
- dag/nodes/sec-trace-formula/lem-trf-completed-base-affine-etale-span.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-varying-base-smooth-span-model.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-smooth-span-etale-slice.json: statement, unsplit; no Mathlib match.
- citations.json: verbatim statements for every citation in the four assembly steps.

## Attachments

None. The upstream WeilConjectures searches found approximation ingredients, not a complete declaration of this item. The project declaration AlgebraicGeometry.relative_completion_etale_approximation at lean/Sheaf/TraceFormula/RelativeCompletionEtaleApproximation.lean:114 ends with sorry (line 160); it is not an attachment. Smooth.exists_etale_comp_of_etale_residueFieldMap at lean/WeilConjectures/AlgebraicGeometry/Morphisms/Slicing.lean:186 is already represented by lem-sbc-smooth-separable-point-etale-slice; its conclusion supplies a slice map, not the immersion and pointed span pullback comparisons in the new third node.

## WANTED

None. All sources needed here are present.

## Return repaired

The return requires distribution of the entire 7020-character argument, at least two comparable independent new nodes, unchanged parent statement, and assembly at most 3000 characters. This repair delivers three unsplit statement-only nodes. Their arguments have comparable scope: completed-base preparation and approximation (old steps 1–2 and the affine shrinking from step 5), smooth-model construction with varying target map (old steps 3–6), and slicing with both Cartesian identifications and residue fields (old steps 7–9). None is the parent with a new label: the first concludes over the complete base only, the second starts from an existing etale span with no formal isomorphism, and the third starts from an arbitrary smooth-base span and uses no completion or limit.

The sandbox initially contained only dispatcher brief markers, with no node files, report, or search log. The mandatory first dry run therefore exited with “no node files”. I recovered the complete returned proof from the current read-only repository, copied the item to the sandbox, and preserved the old argument below. There was no local earlier proof or logged search to discard. The delivery tool rebases the split fields onto the current server version; no git command, compiler, Lake, repository write, launcher edit, or sub-agent was used.

The current main-20261015 ancestor proof is about contracting correspondences; the item's blueprint.from already explicitly records that its nodal-model ancestry is historical. I retained that ancestry and its via chain, and assigned exact 0GDX proof paragraphs to the extracted arguments. This repair does not change the unit, chapter, statement, or route.

## Review by Q19

I read Stacks more-morphisms.tex, Tag 0GDX (lemma-relative-map-approximation-pre), including its hypotheses and all three proof paragraphs. I also read Tag 0CAV (lemma-isomorphism-approximation) and Tag 057G (lemma-slice-smooth). The first new node is the first 0GDX paragraph plus the affine finite-presentation preparation; the second is the Popescu/factorization/fixed-family descent portion; the third is the final closed-slice pullback. The original proof's extra details remain allocated to those nodes, not removed. The complete original steps and the allocation are recorded below so a future worker retains the argument and every previously cited dependency. New nodes themselves have empty proof and proof_deps, and null proof_origin, as required for parallel work.

For assembly step 1 I opened lem-weil-pbc-etale-composition-cancellation: clause (1) states open immersions are etale and clause (2) states composition is etale. These are exactly what extends the affine-local diagram to the original schemes. Affine neighbourhoods are chosen inside the given finite type charts; stalks and completion scalar maps at their marked points are unchanged. The old proof's excellence and Noetherian/finitely presented algebra arguments have moved to the first new node, not been inferred from this etale citation.

For assembly step 2 I read the new completed-base node's whole statement against 0GDX/0CAV and the statements of lem-trf-completed-local-base-change, lem-trf-isomorphism-completion-approximation, and the completion locality/completeness/G-ring nodes. It explicitly provides the point x_B, both induced residue isomorphisms, an affine finitely presented source, and the two B-arrows. The input is an isomorphism of completed stalks as algebras over the completed base, not just an abstract ring isomorphism. In the future proof 0CAV is applied with N=2 and the inverse transported isomorphism. No arbitrary choice of a point above x is made: the closed fibre is unchanged because the completion has the same residue field. Finite presentation after shrinking is valid because the two affine families are finite type over Noetherian bases and the span arrow is etale.

For assembly step 3 I read the smooth-model node's statement and checked it explicitly supplies the map B to S', the equality lambda' r=lambda, the actual fixed models X'=X times_S S' and Y'=Y times_T S', the base-change equations for both arrows, and each induced residue-field isomorphism used in the assembly. I opened lem-trf-fixed-family-etale-span-descent: it assumes an affine finitely presented span and fixed affine finitely presented models over a stage, and concludes these exact pullback equations and residue comparisons. This is an ingredient of the new node, not a substitute for it: it assumes the inverse system and base residue equalities that the new node must construct. The R-to-completion regular-map argument, fibre Noetherianity, small filtered index, directed reindexing, and factorization of lambda over Spec Z all remain in its assigned argument. The assertion kappa(x) to kappa(x') is an isomorphism in the parent follows from the composite with kappa(x_B), using the compatibility of the actual projections; it is not an additional descent assertion.

For assembly step 4 I checked the third new node supplies the entire closed-slice pullback result, not merely existence of some etale map through the point. I opened lem-trf-finite-residue-point-closed-in-fibre and lem-trf-smooth-point-etale-immersion: smoothness gives local finite type, the identity residue extension is finite separable, and the first node proves the closed-fibre-point hypothesis needed by the second. I opened def-weil-closed-immersion: its definition of immersion permits shrinking the ambient target so the slice is closed. I opened def-pc-fibre-product and the statements of the etale base-change and composition nodes. The new conclusion requires both explicit comparison isomorphisms, all commuting projections, and the actual fibre Spec(kappa(h')); merely putting h' in the image set would not suffice. Its ideal vanishes in kappa(h') because h' maps to s', which lies on the closed slice. Hence the quotient-tensor calculation gives the unique point and its unchanged residue field. The hypotheses in step 3 are exactly the hypotheses this slice node requires.

I checked small cases for each new statement. Taking X=S and Y=T gives the identity completed-base span when the formal data agree. A nonclosed x over s is allowed: uniqueness of x_B and unchanged residue fields use base change along the closed point of B, not closedness of x. Mixed characteristic and nilpotents cause no extra regularity assumption: finite type over Z ensures excellence; we do not claim every Noetherian ring has regular completion. The smooth-model result allows an arbitrary lambda:B to T and does not claim lambda equals any finite-stage map without the specified factorization through r. The slice result does not assume H' is smooth, or intersections of affine opens are affine; only the base q is smooth. In relative dimension zero the slice may be open, with zero defining ideal. For a positive-dimensional smooth fibre the rational point is closed by the finite-residue criterion; a nilpotent ideal of a closed slice is harmless since its image in the residue field is zero. Spec of the zero ring cannot furnish a marked point and is excluded by the hypotheses, rather than silently used as a case.

I checked delivery-errors B–E against the files: every object in a new statement is introduced, every notion has a definition citation or an inline meaning, no source tag is used as a definition, the JSON has single TeX backslashes, and there are no new proofs hidden in statements. All new-node searches were actually run through msearch.py and their complete outputs are retained in the sandbox. Each has two semantic phrasings, LeanSearch, Loogle, and a source grep. Loogle's unknown-identifier responses for the deprecated IsEtale name are recorded as errors, not evidence of absence; the successful semantic searches and grep supply the search evidence. The returned hits on standard etale presentations and the etale locus do not approximate a formal isomorphism. I read Mathlib/RingTheory/Smooth/NoetherianDescent.lean (Smooth.exists_finiteType and Etale.exists_subalgebra_fg), Mathlib/Algebra/Category/Ring/FinitePresentation.lean:81, Mathlib/AlgebraicGeometry/Morphisms/LocalFlatDescent.lean:47, and the local Etale/Smooth files. They give partial descent/permanence tools, not any complete new result: Noetherian descent does not make a smooth model of the completed base, and faithful-flat descent is a different hypothesis. There is therefore no Mathlib leaf here.

The four new parent steps have lengths below 2000 characters each. No long step was cosmetically shortened: the original proof is preserved below and each argument is assigned to a genuinely smaller parallel task. The three new nodes cite no parent as a dependency. I checked the statement is byte-for-byte unchanged and that every proof use is in proof_deps; citations.json quotes the entire exact statement where this assembly takes several clauses.

## Original arguments preserved and assigned

### Returned step 1 → lem-trf-completed-base-affine-etale-span (except the affine restriction, which remains assembly step 1)

Work on affine neighbourhoods $S=\operatorname{Spec}R$, $T=\operatorname{Spec}D$, and affine neighbourhoods of $x$ and $y$ mapping into them. Open immersions are etale and compositions of etale maps are etale by [lem-weil-pbc-etale-composition-cancellation], so a diagram for these neighbourhoods gives one for the original schemes. The bases are Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. By [lem-trf-integers-excellent] and [lem-exc-finite-type-localization-excellent], $R$ and $A=R_{\mathfrak p}=\mathcal O_{S,s}$ are excellent; the definition [def-exc-excellent-ring] gives that $A$ is a Noetherian G-ring. The affine coordinate algebras of $X/S$ and $Y/T$ are finite type by hypothesis, hence finite presentation by [lem-weil-pbc-finite-type-noetherian-finite-presentation].

Dependencies retained for this assigned argument: lem-weil-pbc-etale-composition-cancellation, lem-weil-pbc-finite-type-over-noetherian, lem-trf-integers-excellent, lem-exc-finite-type-localization-excellent, def-exc-excellent-ring, lem-weil-pbc-finite-type-noetherian-finite-presentation.

Source: literature/stacks-project/more-morphisms.tex, Tag 0GDX hypotheses; affine reductions in its proof; Tags 07QU, 07QW and 00FP.

### Returned step 2 → lem-trf-completed-base-affine-etale-span

Put $B=\operatorname{Spec}\widehat A$, with closed point $b$. The ring $\widehat A$ is Noetherian by [lem-weil-pbc-adic-completion-noetherian]. By [lem-weil-pbc-local-completion-local-ring] its maximal ideal is $\mathfrak m_A\widehat A$ and its residue field is $\kappa(s)$; [lem-weil-pbc-adic-completion-mod-ideal] makes it complete for that ideal. Thus [lem-weil-pbc-complete-local-g-ring] applies to $\widehat A$. Put $X_B=X\times_SB$, with point $x_B$ over $(x,b)$. Its closed fibre is $X_s$, since $\kappa(b)=\kappa(s)$, so $\kappa(x_B)=\kappa(x)$. The completed-local identification [lem-trf-completed-local-base-change] identifies its completed stalk with $\widehat{\mathcal O}_{X,x}$ as a $\widehat A$-algebra. The families $X_B/B$ and $Y_\sigma/B$ are locally finite type by [lem-weil-pbc-lft-base-change]. Apply [lem-trf-isomorphism-completion-approximation] with $N=2$ and the inverse of the transported given isomorphism. This gives a span $X_B\leftarrow(U,u)\to Y_\sigma$ over $B$, both arrows etale, with $\kappa(x_B)\cong\kappa(u)\cong\kappa(y_\sigma)$.

Dependencies retained for this assigned argument: lem-weil-pbc-adic-completion-noetherian, lem-weil-pbc-local-completion-local-ring, lem-weil-pbc-adic-completion-mod-ideal, lem-weil-pbc-complete-local-g-ring, lem-trf-completed-local-base-change, lem-weil-pbc-lft-base-change, lem-trf-isomorphism-completion-approximation.

Source: literature/stacks-project/more-morphisms.tex, Tag 0GDX proof, first paragraph; Tag 0CAV; Algebra Tags 0316, 05GG, 05GI.

### Returned step 3 → lem-trf-varying-base-smooth-span-model

The localization $R\to A$ is regular by [lem-weil-pbc-localization-regular], and $A\to\widehat A$ is regular by [lem-weil-pbc-g-ring-completion-regular]. For a prime $\mathfrak q\subset R$, the fibre of $R\to\widehat A$ is zero if $\mathfrak q\not\subset\mathfrak p$, and otherwise is the fibre of $A\to\widehat A$ at $\mathfrak qA$; hence it is Noetherian. Consequently [lem-weil-pbc-regular-composition] makes $R\to\widehat A$ regular. Both rings are Noetherian, so [lem-weil-pbc-popescu-smoothing] writes $\widehat A$ as a colimit over a small filtered category of smooth $R$-algebras. Reindex by a nonempty directed set using [lem-weil-pbc-filtered-category-directed-cofinal]. By [lem-weil-pbc-limit-affine-transition], $B=\varprojlim_i S_i$ as schemes, with $S_i$ affine and smooth over $S$.

Dependencies retained for this assigned argument: lem-weil-pbc-localization-regular, lem-weil-pbc-g-ring-completion-regular, lem-weil-pbc-regular-composition, lem-weil-pbc-popescu-smoothing, lem-weil-pbc-filtered-category-directed-cofinal, lem-weil-pbc-limit-affine-transition.

Source: literature/stacks-project/more-morphisms.tex, Tag 0GDX proof, second paragraph; Tags 0AH2, 07QI, 07GC, 0032 and 01YW.

### Returned step 4 → lem-trf-varying-base-smooth-span-model

Let $s_i$ be the image of $b$ in $S_i$. The field maps $\kappa(s)\to\kappa(s_i)\to\kappa(b)=\kappa(s)$ have composite the identity. The second map is injective and its image contains all of $\kappa(s)$, so both maps are isomorphisms. These are the actual residue maps induced by $B\to S_i\to S$.

Dependencies retained for this assigned argument: .

Source: literature/stacks-project/more-morphisms.tex, Tag 0GDX proof, second paragraph: kappa(s)=kappa(s_i).

### Returned step 5 → lem-trf-varying-base-smooth-span-model for finite-stage target factorization and fixed models; lem-trf-completed-base-affine-etale-span for shrinking H to an affine finitely presented B-scheme

The affine target $T$ is finitely presented over $\operatorname{Spec}\mathbf Z$ by [lem-weil-pbc-finite-type-noetherian-finite-presentation]. Apply [lem-weil-pbc-finite-presentation-map-limit-factorization] over $\operatorname{Spec}\mathbf Z$ to the map $B\to T$ defined by $\sigma$. After restricting to stages $j\geq i_0$, it factors through $\sigma_{i_0}:S_{i_0}\to T$; write $\sigma_j$ for its composite with $S_j\to S_{i_0}$. In particular $\sigma_j(s_j)=t$. Fix, from now on, $X_j=X\times_SS_j$ and $Y_j=Y\times_{T,\sigma_j}S_j$. These are affine schemes of finite presentation over $S_j$ by [lem-weil-pbc-finite-presentation-base-change-composition]. Their actual pullbacks to $B$ are $X_B$ and $Y_\sigma$. Shrink $U$ to an affine neighbourhood of $u$. Its map to the affine $X_B$ is etale, hence locally of finite presentation [def-weil-etale-morphism]; on affines the coordinate map is finitely presented, and composition in [lem-weil-pbc-finite-presentation-base-change-composition] gives that $U/B$ is of finite presentation. Restricting an etale map to an open remains etale by [lem-weil-pbc-etale-composition-cancellation].

Dependencies retained for this assigned argument: lem-weil-pbc-finite-type-noetherian-finite-presentation, lem-weil-pbc-finite-presentation-map-limit-factorization, lem-weil-pbc-finite-presentation-base-change-composition, def-weil-etale-morphism, lem-weil-pbc-etale-composition-cancellation.

Source: literature/stacks-project/more-morphisms.tex, Tag 0GDX proof, second and third paragraphs; Tag 01ZC and algebraic finite-presentation permanence.

### Returned step 6 → lem-trf-varying-base-smooth-span-model

Apply [lem-trf-fixed-family-etale-span-descent] to the affine limit $B=\varprojlim S_j$, the point $b$, the fixed models $P_0=X_{i_0}$ and $Q_0=Y_{i_0}$, and the span from step 2. Step 4 supplies every required base residue-field isomorphism, and step 5 supplies finite presentation and the actual pullback identifications. It gives a stage $j$, a scheme $U_j$, etale arrows $U_j\to X_j$ and $U_j\to Y_j$, and an isomorphism $U_j\times_{S_j}B\cong U$ intertwining both arrows. Define $u_j$ as the image of $u$, $x_j$ as the image of $x_B$, and $y_j$ as the image of $y_\sigma$. The lemma gives $\kappa(u_j)\cong\kappa(u)$, $\kappa(x_j)\cong\kappa(x_B)$, $\kappa(y_j)\cong\kappa(y_\sigma)$, and residue-field isomorphisms for both stage arrows. In particular $\kappa(u_j)=\kappa(x)$. Only $U$ and its arrows have been descended; the two target models remain the specified fibre products.

Dependencies retained for this assigned argument: lem-trf-fixed-family-etale-span-descent.

Source: literature/stacks-project/more-morphisms.tex, Tag 0GDX proof, third paragraph; fixed-family pointed refinement of Tags 01ZM and 07RP.

### Returned step 7 → lem-trf-smooth-span-etale-slice

Since $S_j\to S$ is smooth and $\kappa(s_j)=\kappa(s)$, [lem-trf-finite-residue-point-closed-in-fibre] makes $s_j$ closed in its fibre. The identity residue extension is finite separable, so [lem-trf-smooth-point-etale-immersion] gives an immersion $V\to S_j$ through $s_j$, etale over $S$, with singleton underlying fibre over $s$. By the definition of immersion [def-weil-closed-immersion], shrink $S_j$ around $s_j$ so that this immersion is closed, and restrict $U_j,X_j,Y_j$ to that open. Restriction preserves the two etale arrows by [lem-weil-pbc-etale-composition-cancellation]. Write $v\in V$ for the point mapping to $s_j$, so $\kappa(v)=\kappa(s_j)=\kappa(s)$. Set $\tau=\sigma_j|_V$; then $\tau(v)=t$.

Dependencies retained for this assigned argument: lem-trf-finite-residue-point-closed-in-fibre, lem-trf-smooth-point-etale-immersion, def-weil-closed-immersion, lem-weil-pbc-etale-composition-cancellation.

Source: literature/stacks-project/more-morphisms.tex, Tag 0GDX proof, final paragraph; Tags 01TE and 057G.

### Returned step 8 → lem-trf-smooth-span-etale-slice

Put $W=U_j\times_{S_j}V$. The universal property of fibre products [def-pc-fibre-product] gives, compatibly with every projection,
\[
W\cong U_j\times_{X_j}(X\times_SV),\qquad
W\cong U_j\times_{Y_j}(Y\times_TV).
\]
Indeed a test-scheme map into either right-hand side is exactly a pair of maps to $U_j,V$ agreeing in $S_j$, because $X_j=X\times_SS_j$ and $Y_j=Y\times_TS_j$. Thus $W\to X\times_SV$ and $W\to Y\times_TV$ are actual base changes of the two etale stage arrows. They are etale by [lem-weil-pbc-etale-base-change-finite-limits]. The projection $X\times_SV\to X$ is a base change of $V\to S$, hence etale by the same node, and $W\to X$ is etale by [lem-weil-pbc-etale-composition-cancellation]. All triangles commute by the displayed universal properties.

Dependencies retained for this assigned argument: def-pc-fibre-product, lem-weil-pbc-etale-base-change-finite-limits, lem-weil-pbc-etale-composition-cancellation.

Source: literature/stacks-project/more-morphisms.tex, Tag 0GDX proof, final paragraph: Cartesian identifications and conclusion.

### Returned step 9 → lem-trf-smooth-span-etale-slice

On an affine neighbourhood of $s_j$, write $V=\operatorname{Spec}(C/J)\hookrightarrow\operatorname{Spec}C\subseteq S_j$. By the closed-immersion definition [def-weil-closed-immersion], $J$ vanishes in $\kappa(s_j)$, hence in $\kappa(u_j)$. The fibre of $W=U_j\times_{S_j}V$ over $u_j$ is therefore $\operatorname{Spec}(\kappa(u_j)\otimes_C C/J)=\operatorname{Spec}\kappa(u_j)$ [def-pc-fibre-product]. It has a unique point $w$, with $\kappa(w)=\kappa(u_j)=\kappa(x)$. Also $w\mapsto v$ and $\kappa(v)=\kappa(s)$. Taking $(U,u)=(W,w)$ now gives every required clause.

Dependencies retained for this assigned argument: def-weil-closed-immersion, def-pc-fibre-product.

Source: literature/stacks-project/more-morphisms.tex, Tag 0GDX, final fibre-product construction: marked points and residue fields.

## Not duplicates

lem-trf-completed-base-affine-etale-span vs lem-trf-fixed-family-etale-span-descent: The existing node assumes a directed inverse system and residue equalities at every stage; it does not construct a smooth system for the completion or factor a varying map to T. The new smooth-model node must establish those hypotheses before using it; the other new nodes do not assert limit descent.

lem-trf-completed-base-affine-etale-span vs lem-trf-completed-stalk-isomorphism-etale: The existing node tests an existing locally finite type map by its actual completed stalk map; it constructs neither a span over the completion nor its smooth model or slice pullback.

lem-trf-completed-base-affine-etale-span vs lem-trf-completed-local-base-change: The existing node identifies a completed stalk after base change and the point x_B; it does not construct an affine finitely presented etale span. The other new nodes start with an existing span or a smooth-stage diagram.

lem-trf-completed-base-affine-etale-span vs lem-trf-relative-completion-etale-approximation: The parent turns a formal isomorphism into a final etale-base diagram; the new node isolates only the indicated intermediate construction and has a different input/output interface.

lem-trf-completed-base-affine-etale-span vs lem-trf-isomorphism-completion-approximation: The existing node works over one locally Noetherian base with a G-ring stalk, assuming two families already over that base. The new completed-base node must prepare that base from two different original bases and compare completions; the other new nodes use a span as input and involve no approximation of stalk isomorphisms.

lem-trf-varying-base-smooth-span-model vs lem-trf-fixed-family-etale-span-descent: The existing node assumes a directed inverse system and residue equalities at every stage; it does not construct a smooth system for the completion or factor a varying map to T. The new smooth-model node must establish those hypotheses before using it; the other new nodes do not assert limit descent.

lem-trf-varying-base-smooth-span-model vs lem-trf-completed-local-base-change: The existing node identifies a completed stalk after base change and the point x_B; it does not construct an affine finitely presented etale span. The other new nodes start with an existing span or a smooth-stage diagram.

lem-trf-varying-base-smooth-span-model vs lem-trf-relative-completion-etale-approximation: The parent turns a formal isomorphism into a final etale-base diagram; the new node isolates only the indicated intermediate construction and has a different input/output interface.

lem-trf-smooth-span-etale-slice vs lem-sbc-closed-fiber-power-series-test: The existing node constructs a flat power-series test under depth and boundary hypotheses; none of the new nodes has that input or conclusion.

lem-trf-smooth-span-etale-slice vs lem-sbc-smooth-separable-point-etale-slice: The existing node gives an affine slice map with etale composite, without the immersion, fixed-target pullback identities, or the prescribed span point and its residue comparisons.

lem-trf-smooth-span-etale-slice vs lem-sbc-smooth-closed-point-local-section: The existing node constructs a flat local base extension through a point, not a closed etale slice or a span with two fixed target families.

lem-trf-smooth-span-etale-slice vs lem-sbc-smooth-local-depth-two-closed-fiber-flat: The existing node proves flatness at a point of a supplied finite cover using depth hypotheses; it constructs none of the three new intermediate diagrams.

lem-trf-smooth-span-etale-slice vs lem-sbc-smooth-local-depth-two-finite-flat: The existing node proves flatness of a supplied finite morphism under depth hypotheses; it constructs none of the new diagrams.

lem-trf-smooth-span-etale-slice vs lem-trf-fixed-family-etale-span-descent: The existing node assumes a directed inverse system and residue equalities at every stage; it does not construct a smooth system for the completion or factor a varying map to T. The new smooth-model node must establish those hypotheses before using it; the other new nodes do not assert limit descent.

lem-trf-smooth-span-etale-slice vs lem-trf-completed-local-base-change: The existing node identifies a completed stalk after base change and the point x_B; it does not construct an affine finitely presented etale span. The other new nodes start with an existing span or a smooth-stage diagram.

lem-trf-smooth-span-etale-slice vs lem-trf-relative-completion-etale-approximation: The parent turns a formal isomorphism into a final etale-base diagram; the new node isolates only the indicated intermediate construction and has a different input/output interface.

lem-trf-smooth-span-etale-slice vs lem-trf-smooth-point-etale-immersion: The existing node constructs an immersion slice of a single smooth morphism; the new slice node controls two fixed target families, their Cartesian pullback arrows, the fibre over the specified span point, and induced residue maps. The other new nodes conclude before slicing.

## What remains

The three new nodes intentionally remain unsplit statement-only tasks, searched and ready for separate workers. No source error or statement dispute was introduced or found in this repair. The parent statement and existing metadata are preserved. Server dry-run and push results will be recorded after validation.
