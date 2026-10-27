# Repair of lem-sfb-invariant-local-curve-pencils

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-invariant-local-curve-pencils.json`: unchanged statement and statement dependencies, new seven-step assembly, 2549 characters of proof text.
- `lem-sfb-effective-action-norm-pencil`: statement, unsplit, no Mathlib match; effective generic action and norm coherence.
- `lem-sfb-relative-norm-pair-interpolation`: statement, unsplit, no Mathlib match; simultaneous special-fibre and generic-fibre section choice.
- `lem-sfb-relative-pencil-finite-shrink`: statement, unsplit, no Mathlib match; base-locus removal, finite spreading and surjectivity.
- `lem-sfb-integral-coordinate-avoidance`: statement, unsplit, no Mathlib match; integral coordinate matrix and marked finite-etale fibres.
- `lem-sfb-separable-open-pencil-specialization`: statement, unsplit, no Mathlib match; specialization of a supplied nonempty parameter open and avoidance over a finite separable extension.
- `citations.json`: verbatim statement quotes for every citation in every assembly step.

All five new node files are under the item's chapter directory. They contain self-contained statements only, with empty proof and proof_deps and null proof_origin. They inherit the unit and the blueprint ancestor/via chain. Their separate proof tasks are recorded below without putting proof sketches in their statements.

## Attachments

None. I searched `lean/WeilConjectures/` by the item tag and by invariant/separating pencils, norm sections and coordinate avoidance. The apparent separating-pair declarations there concern affine-open separatedness, not linear-series pencils. The recorded theorem `AlgebraicGeometry.exists_invariant_local_curve_pencils` in `lean/Sheaf/AlgebraicGeometry/InvariantLocalCurvePencils.lean` ends in `sorry`. It is not a completed attachment. I also read its docstring, which retains the sixteen returned arguments.

## WANTED

WANTED: local copy of de Jong, *Families of curves and alterations* (1997), §§3.3--3.5, printed pp.605--606, for this item and the five extracted nodes. I read the publisher's PDF at https://www.numdam.org/item/10.5802/aif.1575.pdf, especially PDF pages 7--8. No document was downloaded or written into the read-only repository. The publisher uses a quotient in §3.4; this delivery retains the already accepted quotient-free norm-section route and marks the assembly agent-written.

## What was wrong and the repair

The human return asks for spreading 12736 characters of proof over at least four new independent tasks, preserving the statement and all the arguments. It does not ask for a mathematical change. The sandbox initially contained only dispatcher marker files, so there was no prior local report, citation file, search log or node copy to overwrite. I copied the current repository item, whose sixteen proof-step lengths exactly match the returned item, and retained that full snapshot as `returned-item.json` in the sandbox. The copied node includes the current source, searches, Lean records and review metadata; only split-owned proof/report fields are changed by this repair. No git command was run in the shared repository.

Five new statements distribute the old arguments. The extraction map and verbatim old steps below make the preservation check reproducible. No argument has been replaced by a vague assertion. Normalization and the finite affine covering remain explicit assembly steps. Effectivity and norm identities, interpolation, proper finite spreading, coordinate avoidance and finite-separable descent now have independent statement-only nodes. The separable-specialization node assumes the nonempty separating open and does not prove its existence: the existing separating-pair theorem supplies that input. Thus it is a smaller parameter-selection/descent argument, not a renamed zero-dimensional instance of the entire parent. Likewise finite shrinking takes an already constructed section pair, and coordinate avoidance takes an already finite separating pencil.

The statement's distinction between finite-etale distinguished fibres and disjointness from the marking is preserved. No statement dispute was found in this repair. The old accepted norm construction avoids scheme quotients, and no excluded SGA source is used.

## Searches and Mathlib verdicts

Every new statement was searched using the required msearch.py commands: LeanFinder, Loogle, grep, a second semantic phrasing, and LeanSearch. Exact query text and actual top results are recorded in the nodes and searches.jsonl. The LeanSearch specialization query was unavailable; its verdict is unavailable. The other semantic and grep searches ran. Loogle does not know IsAmple or IsHProjective under those names; I recorded those diagnostics and additionally searched the closed-immersion/proper interface. The hit `IsClosedImmersion.iff_isProper_and_mono` concerns embeddings, not interpolation.

The useful partial hits were the finite/proper and finite-fibre-neighbourhood results in Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean, Matrix.SpecialLinearGroup and its transvection construction, and Algebra.Etale.iff_exists_algEquiv_prod. I read the local finite/proper source and the determinant-one definition. These give components of the new statements, not the full section-pair shrinking, integral simultaneous avoidance, or finite-separable parameter argument in one specialization. The SL2 cusp hit assumes a principal ideal ring and moves one cusp; it does not give avoidance for an arbitrary infinite domain. Galois faithfulness hits concern field actions, not restriction of integral scheme automorphisms plus orbit-bundle linearization. Ordinary section-localization hits do not give the two-fibre interpolation. The remaining curve hits concern Weierstrass curves rather than the arbitrary curves here. There are zero new Mathlib leaves.

I searched the whole DAG by norm sections, orbit bundles, relative pencils, dense lifts, finite-fibre neighbourhoods and coordinate avoidance, and ran blueprint_refs.py searches for orbit bundle, norm section, relative pencil, finite pencil, coordinate avoidance, separating pair and separable pencil. Those whole-blueprint searches gave no duplicate. Existing definitions and the special-fibre and generic norm-pencil inputs are reused. The new nodes' source is the same de Jong place as the returned argument, with exact extracted step ranges; the supporting Stacks facts remain in the retained argument citations below.

## Not duplicates

lem-sfb-effective-action-norm-pencil vs def-sfb-pencil-orbit-bundle-norm: the existing node defines the ordered tensors and section formula; the new theorem proves effectivity on the generic fibre, group linearization, invariance and compatibility with base change and powers.
lem-sfb-effective-action-norm-pencil vs lem-sfb-finite-norm-invertible-sections: the existing theorem descends an invertible module along a finite surjection equipped with norm maps; this theorem forms an orbit tensor on the same scheme and constructs no quotient or descended module.
lem-sfb-relative-norm-pair-interpolation vs lem-sfb-ample-curve-two-section-pencil: the existing node chooses sections on one curve over one field; the new statement chooses ordinary sections over a base neighbourhood meeting both a prescribed special-fibre finiteness condition and the generic separating condition.
lem-sfb-relative-norm-pair-interpolation vs lem-sfb-separating-pair-open: the existing node supplies the generic nonempty open; the new statement meets it with lifts having the required special-fibre values, including finite residue fields.
lem-sfb-relative-norm-pair-interpolation vs lem-trf-ample-fibre-section-lifting: lifting one section is an input; simultaneous generic separation is additional content.
lem-sfb-relative-pencil-finite-shrink vs lem-trf-proper-finite-fibre-finite-near: the latter starts with a proper morphism and one finite fibre over its target; the new statement starts with a potentially nongenerating section pair and obtains a map finite over the entire relative projective line after shrinking the base.
lem-sfb-relative-pencil-finite-shrink vs thm-pqf-finite-iff-proper-finite-fibres: the latter is a finiteness criterion, not the construction of the map or the base neighbourhood; generic surjectivity is propagated as well.
lem-sfb-integral-coordinate-avoidance vs lem-sfb-invariant-local-curve-pencils: the new statement assumes the finite separating relative pencil and proves a target-coordinate transformation over the given ring; it constructs neither the relative pencil nor a base cover or normalization.
lem-sfb-separable-open-pencil-specialization vs lem-sfb-separating-pair-open: the latter asserts a nonempty open, possibly without rational points; the new statement takes that open as a hypothesis, specializes over a finite separable extension, and descends the avoidance conditions.
lem-sfb-separable-open-pencil-specialization vs lem-sfb-invariant-local-curve-pencils: the new theorem assumes the full extension-compatible norm-pencil open. It is a parameter selection and coefficient descent theorem and includes no relative model, local pencils, affine covering or normalization.

## Review by O2

I read the chapter and unit records and the node's ancestor chain. These are node-level extractions within the already accepted constructibility/alteration route, leaving the chapter and unit route unchanged. The source for the item and all five extractions is de Jong §3.4, with §3.3 for the field case and the start of §3.5 for the finite cover. I read that passage in the publisher PDF. I also opened the existing norm definition, special-fibre pencil, separating-pair open and normal-model statements, and the statements for all the supporting citations retained below. Their source tags, including fibre lifting 0D2M, proper finite-neighbourhood 02UP, proper finite-fibres 02OG, flat cohomology base change and coherent cohomology, remain identifiable in those nodes. No node is cited for content available only in its proof.

Assembly step 1 uses the normal-model statement with L=k(X), E=K; its explicit scalar-extension clause gives the smooth generic fibre and its functoriality extends the action. Its H-projectivity conclusion permits the projective-implies-proper theorem. The proper closed-image theorem supplies closedness, and finite-type over a Noetherian field supplies Noetherianity. The remaining identification of a normal domain with its integral closure in its own fraction field is written directly.

Step 2 uses the first new statement exactly for faithful generic action and the orbit-norm identities. The projective definition supplies the embedding, and the projective-ample statement applies over every affine base neighbourhood, including the field-valued fibres. Its hypotheses really require a closed immersion into projective space over an affine base, which we have. It is not used for a non-affine base's absolute ampleness. Norms are taken over the effective group; no division by its order or lifting of invariant sections is assumed.

Step 3 uses the second new statement with Y=N restricted to the chosen affine open. Step 1 provides integrality, surjectivity and all geometric fibres pure of dimension one; the normal-model generic fibre is the original smooth geometrically integral C. Step 2 provides the faithful generic action and embedding. A closed point on an integral positive-dimensional base cannot be its generic point, so its maximal ideal is nonzero. The interpolation node explicitly allows finite k and finite residue field and returns only special/generic generation, not unsupported global generation.

Step 4 applies the third new statement to the invertible module B raised to the interpolation exponent. Its two section-pair hypotheses are exactly the two clauses returned by step 3. The statement supplies global generation after shrinking, finite surjectivity and retention of the generic etale open; the first new statement supplies invariance. The shrunk affine domain remains infinite (a finite integral domain is a field). The fourth new statement therefore applies with the given reduced finite-etale marking. It returns a determinant-one matrix over that domain, so the coordinate automorphism exists on the entire shrunk base; no denominators need further shrinking.

Step 5 is elementary Noetherian topology, with its minimal-closed-subset and quasi-compactness arguments written out. It uses no uncited vanishing or geometric theorem.

Step 6 writes the dimension-zero reduction explicitly. The smooth-curve-normal statement applies to X=C, not to a potentially singular total space over a positive-dimensional base. The projective-ample theorem applies over Spec K. The separating-pair-open statement requires faithful G and an ample invertible L, supplied in step 2 and this step; it supplies both finite-dimensionality in its affine-parameter formulation and an open that works over every extension field. Nonempty as a scheme is not mistaken for having a K-point.

Step 7 uses the fifth new statement with that supplied open, rather than using any unproved rational-point assertion over a finite field. It gives a finite separable E and the actual pair and matrix with all the avoidance conclusions. Applying the same scalar-extension clause of the normal-model theorem identifies X_E=C_E and S_E=Spec E and extends the original J-action trivially on E. One open is then affine and covers the base. Every cited new statement introduces its own objects, and citations.json quotes the actual statement text for every use.

I tested the extracted claims against these cases: trivial group; a nonfaithful action with kernel divisible by the characteristic; wild faithful actions; finite base field and finite special residue field; empty marking; a marking containing an original distinguished fibre; characteristic two; reducible or nonreduced special fibres; and a purely inseparable Frobenius pencil. Only the generic curve is assumed smooth and geometrically integral. The special-fibre interpolation uses the existing result allowing nonreduced and reducible schemes. A Frobenius pencil fails the required generic etaleness assumption and is never selected from W_n. The coordinate lemma explicitly assumes A infinite, so it makes no false assertion for SL2 over a small finite field. The field-specialization lemma instead permits extension of a finite field. Over an imperfect field a nonempty open of affine space still has a point in the infinite separable closure; algebraic closure alone is not substituted for separable closure. The finite set avoided need not consist of rational points, since its minimal polynomials produce a homogeneous vanishing polynomial. The three distinguished rational points remain distinct in characteristic two. Etaleness of their finite fibres implies reducedness; disjointness from M is checked separately and retained separately in every statement.

The five extraction statements have no proofs to overrun the long-step limit. The parent's seven steps total 2549 text characters and every one is below 2000. I corrected one draft reference to a nonexistent separated-morphism definition by using the existing proper-morphism convention node that also defines separatedness. I preserved the parent statement exactly; no imported or reviewed metadata is intentionally revised. The full old arguments follow, with their exact original citations and elementary flags. These are retained handover material for future workers, not additional proof steps in the unsplit new nodes.

## What remains

The five new arguments are intentionally unsplit work items, ready for independent workers. There is no unresolved mathematical or source dispute in this repair. Server validation and delivery results will be recorded after they finish.

## Extraction map and complete retained arguments

The following reproduces every returned proof step verbatim, including its dependency list. Steps 1 and 14 are realized in the short assembly; all other arguments are assigned to the five new nodes. Some preliminary sentences of step 2 are assembled in step 1, and the dimension-zero normal-model identification remains in assembly step 7. The specialization task reuses the coordinate-avoidance argument over the separable closure, so that argument is preserved once under its own independent task rather than being silently omitted.

### Returned step 1 → assembly step 1

Apply [lem-sfb-finite-normal-relative-curve-model] with $E=K$ and $L=k(X)$. Its scalar-extension clause applies to the given smooth geometrically integral generic curve. It gives a finite surjection $\nu:N\to X$, where $N$ is the normalization in $k(X)$, $N\to S$ is H-projective with pure one-dimensional geometric fibres, and $N_K=C$. Its functoriality extends the $J$-action. Normality of $S$ identifies its normalization in $K$ with $S$: on affine normal domains the integral closure in the fraction field is the same ring. Thus in positive base dimension it suffices to construct the requested pencils on $N$, and no constant extension is involved.

Original uses: lem-sfb-finite-normal-relative-curve-model. Elementary: false.

Original source: literature/de-jong-families-curves-alterations-1997.pdf — de Jong, Families of curves and alterations, §3.4, printed p.606

### Returned step 2 → lem-sfb-effective-action-norm-pencil (properness/Noetherianity assembled in step 1)

The projective-implies-proper theorem makes $N\to S$ proper. Also $S$ and $N$ are Noetherian by [lem-weil-pbc-finite-type-over-noetherian], since they are of finite type over a field. The image of $N$ in $S$ is closed and contains the generic point, hence is all of $S$. Thus every fibre is nonempty. Replace $J$ by its image $G\subseteq\operatorname{Aut}_S(N)$; invariance under $G$ will imply invariance under $J$. The action of $G$ on $C=N_K$ is faithful: if an element is the identity there, its equalizer with the identity is closed because $N/S$ is separated and contains the generic point of integral $N$. Its defining ideal is zero, since it vanishes in $k(N)$ and affine coordinate rings of $N$ inject into that field. Hence the equalizer is all of $N$. This reduction removes the kernel before taking any products; no scheme quotient is constructed.

Original uses: lem-kun-projective-implies-proper, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-proper-closed-image, lem-sc-integral-function-field-affine-fraction. Elementary: false.

Original source: literature/de-jong-families-curves-alterations-1997.pdf — §3.4, printed p.606; agent-written quotient-free norm-section replacement for the two linear-series inputs, retaining lifting, density, spreading and coordinate avoidance. The source itself uses a quotient; this proof does not.

### Returned step 3 → lem-sfb-effective-action-norm-pencil

Choose a projective embedding $i:N\hookrightarrow\mathbf P^D_S$ and put $L=i^*\mathcal O(1)$. Form the invertible module $B=\bigotimes_{g\in G}g^*L$ and, for $a\in\Gamma(N_U,L^{\otimes n})$, its norm section $\mathcal N_G(a)=\bigotimes_{g\in G}g^*a\in\Gamma(N_U,B^{\otimes n})$, where $U\subseteq S$ is any open. These are genuine constructions with pullbacks and tensor products, locally tensor products of free rank-one modules. For $h\in G$, the identification $h^*B\cong B$ permutes the factors by the bijection $g\mapsto gh$, and sends $h^*\mathcal N_G(a)$ to $\mathcal N_G(a)$. In trivializations this is simply reordering a finite product. Therefore whenever two norm sections generate, their projective-coordinate morphism is $G$-invariant. Pulling back to a fibre commutes with this formula: both sides are the tensor product of the pulled-back sections. Also $\mathcal N_G(a^m)=\mathcal N_G(a)^m$.

Original uses: def-kun-projective, def-pc-module-pullback, def-pur-sheaf-tensor-product, def-sc-invertible-module. Elementary: true.

Original source: literature/de-jong-families-curves-alterations-1997.pdf — §3.4, printed p.606; agent-written quotient-free norm-section replacement for the two linear-series inputs, retaining lifting, density, spreading and coordinate avoidance. The source itself uses a quotient; this proof does not.

### Returned step 4 → lem-sfb-relative-norm-pair-interpolation

Assume $\dim S>0$, and fix a closed point $s\in S$. Choose an affine neighbourhood $U=\operatorname{Spec}A$. The domain $A$ is infinite and its maximal ideal $\mathfrak m$ at $s$ is nonzero: otherwise $s$ would be the closed generic point of $S$, forcing $S$ to be a point; a finite domain is a field. Hence $K=\operatorname{Frac}A$ is infinite. Apply the projective-ample theorem to the embedding of $N_U$ from step 3, and to its base changes to $s$ and $K$. It makes $L_U$, $L_s$ and $L_K$ ample invertible modules. The special fibre $N_s$ is nonempty, projective and of dimension one, since its geometric fibre is pure of dimension one. The $G$-action restricts to each of these fibres; only its generic restriction is required to be faithful.

Original uses: lem-sc-integral-function-field-affine-fraction, lem-weil-pbc-projective-ample-invertible. Elementary: false.

Original source: literature/de-jong-families-curves-alterations-1997.pdf — §3.4, printed p.606; agent-written quotient-free norm-section replacement for the two linear-series inputs, retaining lifting, density, spreading and coordinate avoidance. The source itself uses a quotient; this proof does not.

### Returned step 5 → lem-sfb-relative-norm-pair-interpolation

Apply [lem-sfb-ample-curve-two-section-pencil] to $(N_s,L_s,G)$ to obtain $d\geq1$ and sections $a_s,b_s$ whose norm pair gives a finite special-fibre pencil. For any $m\geq1$, the sections $a_s^m,b_s^m$ have norms $\mathcal N_G(a_s)^m,\mathcal N_G(b_s)^m$. This is still a generating pair and its pencil is the old finite pencil composed with $[x:y]\mapsto[x^m:y^m]$. That power map is finite: on each standard affine chart the coordinate ring is free over the power subring, with basis $1,t,\ldots,t^{m-1}$. Choose $m$ so large that $n=dm$ is at least both the lifting threshold of [lem-trf-ample-fibre-section-lifting] for $(N_U,L_U,s)$ and the threshold of [lem-sfb-separating-pair-open] for $(C,L_K,G)$. Lift the ordinary sections $a_s^m,b_s^m$, intersect the two supplied neighbourhoods, and shrink to an affine neighbourhood of $s$. Denote these ordinary lifts by $a_0,b_0$. Their norms restrict to the finite special pencil. No assertion about lifting invariant sections is used.

Original uses: lem-sfb-ample-curve-two-section-pencil, lem-weil-pbc-finite-composition, lem-trf-ample-fibre-section-lifting, lem-sfb-separating-pair-open. Elementary: false.

Original source: literature/de-jong-families-curves-alterations-1997.pdf — §3.4, printed p.606; agent-written quotient-free norm-section replacement for the two linear-series inputs, retaining lifting, density, spreading and coordinate avoidance. The source itself uses a quotient; this proof does not.

### Returned step 6 → lem-sfb-relative-norm-pair-interpolation

Put $V=\Gamma(C,L_K^{\otimes n})$ and $H=\Gamma(N_U,L^{\otimes n})$. Properness gives quasi-compactness and quasi-separatedness. Since $A\to K$ is a flat localization, degree-zero flat base change gives $H\otimes_AK=V$. Proper coherent cohomology gives finite dimensionality of $V$. Choose $e_1,\ldots,e_t\in H$ whose images form a $K$-basis of $V$, by clearing the finitely many denominators of a basis in $H\otimes_AK$. Fix $0\ne u\in\mathfrak m$. For arbitrary $r_j,s_j\in A$, the ordinary pair $(a_0+u\sum r_je_j,b_0+u\sum s_je_j)$ keeps the chosen special-fibre values, and therefore keeps their norms too. These pairs are Zariski dense in $V^2$: their coefficient map is an invertible affine change of coordinates over $K$, and a polynomial over $K$ vanishing on all of $A^{2t}$ is zero, by induction on the number of variables and the univariate root bound over the infinite set $A$.

Original uses: lem-pc-flat-base-change-cohom, lem-pc-coherent-hi. Elementary: false.

Original source: literature/de-jong-families-curves-alterations-1997.pdf — §3.4, printed p.606; agent-written quotient-free norm-section replacement for the two linear-series inputs, retaining lifting, density, spreading and coordinate avoidance. The source itself uses a quotient; this proof does not.

### Returned step 7 → lem-sfb-relative-norm-pair-interpolation

By [lem-sfb-separating-pair-open], the chosen degree $n$ has a nonempty open $W_n\subseteq V^2$ of ordinary section pairs whose norm pencil is finite, surjective and generically etale on $C$. The faithful action required there was checked in step 2. The dense set in step 6 meets $W_n$. Choose the corresponding global ordinary pair $(a,b)$ on $N_U$ and put $\alpha=\mathcal N_G(a)$, $\beta=\mathcal N_G(b)$. On $N_s$ these keep the finite norm pencil; on $C$ their pencil is finite surjective and generically etale. In particular they have no generic base point. The residue field $\kappa(s)$ need not be infinite. The construction used only $N$, its sections and its action.

Original uses: lem-sfb-separating-pair-open. Elementary: false.

Original source: literature/de-jong-families-curves-alterations-1997.pdf — §3.4, printed p.606; agent-written quotient-free norm-section replacement for the two linear-series inputs, retaining lifting, density, spreading and coordinate avoidance. The source itself uses a quotient; this proof does not.

### Returned step 8 → lem-sfb-relative-pencil-finite-shrink

The simultaneous zero locus $Z$ of $\alpha,\beta$ is closed, by the nonvanishing-section theorem, and misses $N_s$. Since $N_U\to U$ is proper, its image is closed and misses $s$. Remove this image and shrink affinely about $s$. The generating-sections criterion and the projective-space construction now give $\psi=[\alpha:\beta]:N_U\to\mathbf P^1_U$, invariant by step 3. This morphism is proper: its source is proper over $U$ and its target is proper, hence separated, over $U$. Its fibre over $s$ is the finite norm pencil retained in step 7.

Original uses: lem-weil-pbc-nonvanishing-section-trivializes, lem-weil-pbc-proper-closed-image, lem-weil-pbc-invertible-generating-sections-fibre, def-weil-pbc-morphism-to-projective-space-by-sections, lemma-nagata-proper-to-separated-target, lemma-nagata-projective-space-base-change-proper. Elementary: false.

Original source: literature/de-jong-families-curves-alterations-1997.pdf — §3.4, printed p.606; agent-written quotient-free norm-section replacement for the two linear-series inputs, retaining lifting, density, spreading and coordinate avoidance. The source itself uses a quotient; this proof does not.

### Returned step 9 → lem-sfb-relative-pencil-finite-shrink

For every $z\in\mathbf P^1_s$, the fibre of $\psi$ over $z$ is finite. The proper-finite-fibre theorem gives an open neighbourhood $W_z\subseteq\mathbf P^1_U$ over which $\psi$ is finite. Put $W=\bigcup_zW_z$. Its closed complement misses $\mathbf P^1_s$. The projection $\mathbf P^1_U\to U$ is proper, so the image of that complement is closed and misses $s$. Remove that image and shrink affinely once more. Now $\mathbf P^1_U\subseteq W$, so every fibre of $\psi$ is finite, as it is a fibre of a finite restriction over some $W_z$. The target is Noetherian, being of finite type over the Noetherian affine $U$. The proper-finite-fibres criterion [thm-pqf-finite-iff-proper-finite-fibres] therefore makes $\psi$ finite. It remains the invariant map directly constructed on $N_U$.

Original uses: lem-trf-proper-finite-fibre-finite-near, lemma-nagata-projective-space-base-change-proper, lem-weil-pbc-proper-closed-image, thm-pqf-finite-iff-proper-finite-fibres, lem-weil-pbc-finite-closed-map-finite-fibres, lem-weil-pbc-finite-type-over-noetherian. Elementary: false.

Original source: literature/de-jong-families-curves-alterations-1997.pdf — §3.4, printed p.606; agent-written quotient-free norm-section replacement for the two linear-series inputs, retaining lifting, density, spreading and coordinate avoidance. The source itself uses a quotient; this proof does not.

### Returned step 10 → lem-sfb-relative-pencil-finite-shrink

The finite map $\psi$ is surjective. It is surjective on the generic fibre by the separating-pair lemma. Its image is closed by the finite-closed-map theorem and therefore contains the closure of that generic fibre in $\mathbf P^1_U$, which is all of $\mathbf P^1_U$: on either standard chart $\operatorname{Spec}A[t]$ the inclusion into $K[t]$ shows that every function vanishing on the generic fibre is zero. Thus no point of the target is missed. The restriction $\psi_K$ is generically etale by step 7.

Original uses: lem-sfb-separating-pair-open, lem-weil-pbc-finite-closed-map-finite-fibres. Elementary: false.

Original source: literature/de-jong-families-curves-alterations-1997.pdf — §3.4, printed p.606; agent-written quotient-free norm-section replacement for the two linear-series inputs, retaining lifting, density, spreading and coordinate avoidance. The source itself uses a quotient; this proof does not.

### Returned step 11 → lem-sfb-integral-coordinate-avoidance

By the conclusion of [lem-sfb-separating-pair-open] choose a nonempty open $V_0\subseteq C$ on which $\psi_K$ is etale. Its complement $R$ is finite: it is a closed subset of the Noetherian integral curve $C$ missing the generic point, so its dimension is at most zero (a positive chain inside it could be extended by the generic point to a chain of length two); apply [lem-sc-zero-dim-noetherian-closed-finite]. Hence $B=\psi_K(R\cup|M|)$ is a finite set of closed points of $\mathbf P^1_K$, using the closed-map assertion for the finite map. Choose a nonzero homogeneous polynomial $P(X,Y)\in K[X,Y]$ vanishing on $B$: homogenize the finitely many minimal polynomials of its affine closed points and include a factor $Y$ if infinity belongs to $B$.

Original uses: lem-sfb-separating-pair-open, lem-weil-pbc-finite-type-over-noetherian, lem-sc-zero-dim-noetherian-closed-finite, lem-weil-pbc-finite-closed-map-finite-fibres. Elementary: false.

Original source: literature/de-jong-families-curves-alterations-1997.pdf — §3.4, printed p.606; agent-written quotient-free norm-section replacement for the two linear-series inputs, retaining lifting, density, spreading and coordinate avoidance. The source itself uses a quotient; this proof does not.

### Returned step 12 → lem-sfb-integral-coordinate-avoidance

Here is the coordinate change explicitly. Let $E_{ij}$ be the two-by-two matrix unit, and write $u(a)=I+aE_{12}$ and $l(b)=I+bE_{21}$. The map $(a,b,c)\mapsto g=u(a)l(b)u(c)$ has determinant one and parametrizes the open cell of $\mathrm{SL}_2$ with lower-left entry $b\ne0$: its diagonal entries are $1+ab,1+bc$, which recover $a,c$. The condition $P(g^{-1}(v))\ne0$ for each $v\in\{[0:1],[1:1],[1:0]\}$ is a nonempty open condition on this cell. Indeed each vanishing condition is proper, since determinant-one matrices act transitively on the projective line over an algebraic closure; explicitly extend any nonzero column to a determinant-one matrix. A finite union of these proper polynomial zero loci cannot fill the integral affine parameter space. Therefore their product gives a nonzero polynomial in $K[a,b,c]$. As in step 6, it is nonzero at some $(a,b,c)\in A^3$. The resulting matrix defines an automorphism of $\mathbf P^1_U$ over all of $U$, since its determinant is one. Put $\varphi=g\circ\psi$. Then $\varphi_K^{-1}\{0,1,\infty\}$ avoids both $R$ and $M$.

Original uses: . Elementary: true.

Original source: literature/de-jong-families-curves-alterations-1997.pdf — §3.4, printed p.606; agent-written quotient-free norm-section replacement for the two linear-series inputs, retaining lifting, density, spreading and coordinate avoidance. The source itself uses a quotient; this proof does not.

### Returned step 13 → lem-sfb-integral-coordinate-avoidance

All points above the three values now lie in the etale open $V_0$ for $\psi_K$ (with its target relabelled by $g$). Base change of this etale morphism along each of the three rational points shows that each inverse fibre is etale over $K$. It is finite because $\varphi_K$ is finite; the finite-etale algebra criterion makes it a product of finite separable fields, so it is reduced. The union of the three disjoint fibres has the same properties. This proves the required marked-fibre assertion, including its separate disjointness from $M$. Finiteness, surjectivity and $J$-invariance were preserved by the target automorphism.

Original uses: lem-weil-pbc-etale-base-change-finite-limits, lem-sc-finite-etale-algebra-criterion. Elementary: false.

Original source: literature/de-jong-families-curves-alterations-1997.pdf — §3.4, printed p.606; agent-written quotient-free norm-section replacement for the two linear-series inputs, retaining lifting, density, spreading and coordinate avoidance. The source itself uses a quotient; this proof does not.

### Returned step 14 → assembly step 5

Repeat steps 4--13 for every closed point $s$. The resulting affine neighbourhoods cover $S$: a nonempty closed complement would contain a closed point. To see the latter directly, choose a minimal nonempty closed subset using Noetherianity; it is a singleton since schemes are $T_0$, and its point is closed in $S$. Quasi-compactness of the Noetherian scheme $S$ now supplies a finite subcover. With $E=K$, step 1 identifies $X_E=N$ and $S_E=S$, giving exactly the positive-dimensional assertion.

Original uses: lem-weil-pbc-finite-type-over-noetherian. Elementary: true.

Original source: literature/de-jong-families-curves-alterations-1997.pdf — §3.4, printed p.606; agent-written quotient-free norm-section replacement for the two linear-series inputs, retaining lifting, density, spreading and coordinate avoidance. The source itself uses a quotient; this proof does not.

### Returned step 15 → lem-sfb-separable-open-pencil-specialization (field reduction in assembly step 6; the supplied separating open remains the existing theorem)

If $\dim S=0$, the normal integral scheme $S$ is $\operatorname{Spec}K$: its underlying space has just its generic point, an affine neighbourhood is all of $S$, and its reduced zero-dimensional domain is a field. Thus $X=C$ is smooth and normal. Reduce $J$ to its effective image $G$ as in step 2. Choose an embedding of $C$ in projective space and its ample $L$ by the projective-ample theorem. By [lem-sfb-separating-pair-open], for any sufficiently large $n$ there is a nonempty open $W_n$ of ordinary section pairs giving finite surjective generically etale norm pencils on $C$. Choose a separable closure $\Omega/K$. It is infinite: if it had $q$ elements, $T^q-T-1$, with derivative $-1$, would be separable without an $\Omega$-root. The polynomial argument of step 6 gives a pair in $W_n(\Omega)$. Its norm pencil is invariant by permutation of factors as in step 3. Steps 11--12 over $\Omega$ give a determinant-one coordinate change avoiding the marking and the complement of an etale open. No quotient of $C$ is formed.

Original uses: lem-sc-smooth-normal, lem-weil-pbc-projective-ample-invertible, lem-sfb-separating-pair-open, lem-weil-pbc-separable-closure-exists-galois. Elementary: false.

Original source: literature/de-jong-families-curves-alterations-1997.pdf — §3.4, printed p.606; agent-written quotient-free norm-section replacement for the two linear-series inputs, retaining lifting, density, spreading and coordinate avoidance. The source itself uses a quotient; this proof does not.

### Returned step 16 → lem-sfb-separable-open-pencil-specialization (normal-model identification in assembly step 7)

Let $E\subseteq\Omega$ be generated over $K$ by the finitely many coefficients of that ordinary section pair and coordinate-change matrix. The algebraic-generators theorem makes $E/K$ finite, and the separable-closure theorem makes it separable. The pair belongs to $W(E)$ because its defining nonvanishing polynomial conditions hold in $\Omega$, hence already in the subfield $E$. Taking its norm pair therefore defines a finite surjective invariant pencil on $C_E$, generically etale by the separating-pair lemma. The avoidance conditions hold after extension to $\Omega$; etaleness at points descends along field extension by [lem-sc-etale-base-change-geometric], and disjointness descends because field extension is faithfully flat (a nonempty finite scheme over a field stays nonempty, as its nonzero finite-dimensional coordinate algebra stays nonzero after tensoring). Apply step 13 over $E$. Finally the scalar-extension clause of the normal-model theorem identifies $S_E=\operatorname{Spec}E$ and $X_E=C_E$, identifies $k(X)\otimes_KE$ as a field, and extends the $J$-action by fixing $E$. One affine open suffices. This gives every zero-dimensional clause, including the finite-ground-field case.

Original uses: lem-weil-pbc-algebraic-generators-finite-extension, lem-weil-pbc-separable-closure-exists-galois, lem-sfb-separating-pair-open, lem-sc-etale-base-change-geometric, lem-sfb-finite-normal-relative-curve-model. Elementary: false.

Original source: literature/de-jong-families-curves-alterations-1997.pdf — §3.4, printed p.606; agent-written quotient-free norm-section replacement for the two linear-series inputs, retaining lifting, density, spreading and coordinate avoidance. The source itself uses a quotient; this proof does not.
