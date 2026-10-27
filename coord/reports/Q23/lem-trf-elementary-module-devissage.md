# Q23 stage-1 repair: lem-trf-elementary-module-devissage

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-elementary-module-devissage.json`: split; unchanged statement and Lean binding; five assembly steps, 2070 characters total.
- `dag/nodes/sec-trace-formula/lem-trf-affine-fibre-support-model.json`: statement; unsplit, no Mathlib match. An affine supporting model for a module on a possibly non-affine locally finite-type morphism, preserving the local dimension of the distinguished fibre support.
- `dag/nodes/sec-trace-formula/lem-trf-pointed-etale-ambient-lift.json`: statement; unsplit, no Mathlib match. A compatible, pointed ambient lift over an etale changed base, including both cartesian identifications and the residue-field calculation.
- `citations.json`: exact statement quotations for every citation in every parent step.

Both children have empty proof and proof_deps, proof_origin null, complete definition dependencies, blueprint ancestry and actual logged searches. Neither is claimed proved. No Lean or repository file was written, no compiler or git command was run here, and no agent was started.

## Attachments

None. Searching the whole project under lean/WeilConjectures for the blueprint id, elementary_module_devissage and elementary devissage found no exact declaration. The present declaration AlgebraicGeometry.Scheme.Modules.exists_elementary_module_devissage in lean/Sheaf/TraceFormula/ElementaryModuleDevissage.lean:70 ends in sorry. It is not an attachment. Its seven-step docstring agrees with the returned argument. The new supporting model is not the existing supporting-subsheme theorem alone; the new ambient construction is not the existing one-square affine etale lift alone.

## WANTED

None. Read the local Stacks source: flat.tex Tag 057S, lemma-elementary-devissage (statement and entire proof, lines 494--595); Tag 057Q, lemma-sheaf-lives-on-subscheme (446--491); Tag 057R, lemma-lift-etale (84--94); coherent.tex Tag 02KG, lemma-affine-base-change (907--940). These sources cover the item and both children. The geometric local structure is cited through the existing node whose statement packages Tags 057K--057L. No SGA source is used.

## Return repaired

The only numbered substance of this return was the human's re-split requirement: 5399 characters was too much proof work for one worker. The new affine fibre-support model receives old steps 1--2, including affine charts, open fibre-support restriction, dimension invariance by cofinal neighbourhoods, supporting finite-presentation closed subscheme, quotient algebra finite type, and the point/dimension identification. The new pointed ambient lift receives old steps 4--6, including the base-change rings and finite presentations, etale cancellation, the ambient lifting theorem, both cartesian descriptions, the field-isomorphism argument, and compatibility over the changed base. These are separate intermediate arguments of comparable size (1596 and 2474 characters in the retained proof), neither a restatement of the module devissage conclusion. The remaining old step 3 and old step 7 are assembly applications of already existing lemmas. The parent has no step longer than 2000 characters and its total is below 3000.

The original seven texts and their citations appear verbatim below. Thus the repair relocates all their arguments rather than obscuring them by a summary. The children deliberately state their whole intermediate conclusions, including the compatibility data which the assembly uses. Other workers can start on either child with its own hypotheses and source. The old argument is not inserted as a proof into the children, which remain statement-only.

No parent statement change or statement dispute was needed. The sandbox initially contained only launcher brief markers, with no node, report, citations, or searches to resume. I copied the current repository item, which contains the returned seven-step head and earlier review fields, and retained its statement, citations/search history and Lean attachment. There were no prior sandbox query results to repeat. Newly run wrapper results and their full replies are retained in searches.jsonl and search-results/.

## Review by Q23

I read the entire statement and proof of Stacks 057S, its 057Q supporting-scheme input and 057R affine lifting input, and the 02KG base-change formula. I checked the two extracted statements against those exact paragraphs. In the first child I retained the distinction between finite type of a module and finite presentation of the closed immersion; no Noetherian hypothesis on the base has been inserted. In the second child the base is changed BEFORE lifting: v lands in Z times_S S1, rather than using an ambient lift over X which might have no S1-structure. The equalities f1 i=r and fg=a f1 are explicit conclusions. Residue-field isomorphisms refer to the canonical maps, not to abstract field isomorphisms. The finite-presentation condition is lfp plus quasi-compact and quasi-separated throughout.

Parent step 1 uses exactly the new affine model's existence of U,V,Z,H,z and dimension equality. The model assumes the same local finite type, finite-type quasi-coherence and nonzero fibre stalk as the parent, and gives both initial open neighbourhoods and j_*H=u^*F. Parent step 2 uses the existing lem-trf-etale-finite-smooth-local-structure statement, which explicitly gives all of W,Y,S1,b,a,pi,h,w,y,s1, their commutative diagram, both canonical field isomorphisms, finite singleton fibre, smooth dimension n, geometrically integral fibres and pure transcendence. Its locally finite-type hypothesis is justified by the finite-type map pj in step 1; its dimension is that child's dimension equality. I did not rely on the proof of this cited node.

Parent step 3 uses the new pointed ambient lift with X=U, S=V, r=h pi, a and b from step 2, and j from step 1. All five schemes required affine are affine from steps 1--2; j is finitely presented; b,a are etale; ar=pjb is step 2's diagram; w and both canonical field isomorphisms are step 2's output. The cited conclusion actually gives the cartesian square and f1 i=h pi used here. In particular, it does not merely give some unspecified ambient etale neighbourhood. The auxiliary assertions about v and D preserve the old base-change argument as separate proof work in that child.

Parent step 4 uses the exact statements of lem-weil-pbc-module-pullback-finite-type and lem-weil-pbc-module-pullback-quasi-coherent for H, with no finite-presentation assumption on H. I read lem-weil-pbc-affine-pushforward-base-change: its clause (1) asserts the isomorphism for EVERY base change of an affine morphism and a quasi-coherent module. Here j is affine by the closed-immersion affine quotient characterization, H is quasi-coherent, and the square from step 3 is the square required; its primed source is W, not X1. Its formula is g1^* j_*H = i_* b^*H, giving the isomorphism in the desired orientation after inversion. The cited def-pc-module-pullback explicitly includes (h composed with g)^*=g^*h^*, so the last module identification uses its statement and not an unstated convention.

Parent step 5 uses clause (2) of lem-weil-pbc-etale-composition-cancellation, which states etale composition. The factor maps u,v are etale and preserve canonical residue fields by the first child; g1,a have the pointed field isomorphisms in steps 2--3. Composition of these field maps is ordinary isomorphism composition. The equations follow by substitution of fu=vp, pg1=af1 and f1 i=h pi. The geometric pi,h data and marked points have not been shrunk or replaced, so their singleton fibre and pure transcendence are precisely the same assertions already obtained in step 2. Thus every non-elementary claim remaining in the parent is supplied by an explicitly cited statement.

For the old arguments assigned to the children I also opened every cited node statement. The support node supplies exactly j,H and the fibre-support equality, the closed-immersion definition supplies the affine quotient and homeomorphism, the finite-type definition supplies finite algebra generators, the dimension definition is minimum over open neighbourhoods, and module pullback includes composition. For the ambient lift, the affine fibre-product lemma supplies Spec of the tensor product; the lfp affine-opens criterion supplies a finite algebra presentation; etale base change and cancellation apply to D->Z and W->D with the correct composites; affine etale closed-immersion lifting supplies the one square; fibre-product universal properties supply the second; and the closed-immersion residue-field lemma supplies precisely the canonical field maps for j and i. These were read for the repair, and their role is preserved in the old argument below. No citation was added merely for its title.

I tested the first child on F=O_X, on a finite module supported on a proper closed subset of a fibre, on zero-dimensional fibres and on non-Noetherian affine bases. F=0 admits no marked point in its support, so it does not produce a spurious dimension. For a non-closed x, dim_x is minimum over neighbourhoods, not local-ring dimension; this distinction is kept in the statement. In the second child j=id reduces to lifting W itself, a=id removes the base change, a nilpotent/nonreduced closed immersion is still handled by the quotient tensor formula, and w excludes empty W. The closed-immersion field maps remain isomorphisms in the nonreduced case. Neither child assumes a smooth, reduced, integral or flat ambient scheme. No false edge case or additional hypothesis was found.

I checked B--E of delivery-errors.md: both new statements introduce all objects and define/support their notions, use single TeX escapes and correct tags/labels, contain no proof or proof dependency, and have actual wrapper queries of all required kinds with results read. Blueprint searches by 057S, 057Q, 057R, fibre support, etale closed immersion, support and ambient, plus DAG statement/source/keyword searches and project-source searches, found no existing node with either whole intermediate statement. Related nodes are distinguished below. Every parent quote is copied literally from the used statement. There is no new reference back to the parent in a statement/proof dependency, no change of chapter or unit route, and no whole-parent restatement hidden in a child. The recorded blueprint ancestor in main-20261015 now has the contracting-correspondence formulation, not the historical semistable paragraph in the item's inherited ancestry; this repair retains that ancestry and cites the actual Stacks construction for its mathematics.

## Search results read

For the affine model, the two LeanFinder phrasings returned affine finite-type/finite-presentation criteria, restriction-vanishing facts, and IdealSheafData.subschemeObjIso/glueDataObj. These do not construct a finitely presented supporting subscheme for the given module with prescribed fibre support and dimension. LeanSearch returned general finiteness classes and the affine property of closed immersions. Loogle returned zero hits, and the two grep queries returned zero hits. These are component facts, not a one-line specialization giving the whole new statement.

For the ambient model, the two LeanFinder phrasings returned etale stability/cancellation, etale loci, pullbacks in Scheme.Etale and a residue preimmersion. LeanSearch's IsClosedImmersion.lift factors an EXISTING morphism through a closed immersion using kernel containment; it does not construct an ambient etale scheme, so it is not a match. Loogle returned zero hits. The algebraic-geometry grep returned ZariskisMainTheorem.exists_etale_isCompl_of_quasiFiniteAt and EtalePoint.exists_fac_of_etale_of_isSepClosed: I opened their source statements (lines 49 and 37 respectively), which require a quasi-finite point or a separably closed field and give different conclusions. The second grep returned the ring-level quasi-finite idempotent-decomposition theorem, StandardEtalePair lifting identities and etale-locus localization, again no arbitrary closed-subscheme ambient lift. All saved full replies were read. No unavailable service has been called a no-match.

## Not duplicates

lem-trf-affine-fibre-support-model vs lem-trf-elementary-module-devissage: the child stops at a supporting closed subscheme on affine open charts and its local dimension; it has no finite-over-smooth map or elementary devissage conclusion.
lem-trf-pointed-etale-ambient-lift vs lem-trf-elementary-module-devissage: the child starts with a prescribed etale cover of a prescribed closed subscheme and changed base; it has no module, support dimension, finite map, or smooth family.
lem-trf-affine-fibre-support-model vs lem-trf-finite-type-sheaf-fp-support: the existing node requires a globally affine finite-type morphism and supplies j,H; the child performs the non-affine affine-chart reduction, relates original and restricted supports/dimensions, and supplies finite type of the supporting scheme plus pointed neighbourhood data. This is the old steps 1--2 work package required by the human's re-split, not a duplicate 057Q node.
lem-trf-pointed-etale-ambient-lift vs lem-trf-finite-type-sheaf-fp-support: the existing node constructs a supporting subscheme for a module; the child lifts a specified etale scheme through a fixed ambient closed immersion over a new base, with no module.
lem-trf-affine-fibre-support-model vs lem-weil-pbc-affine-etale-closed-immersion-lift: the existing node constructs an ambient etale lift from an etale scheme over a closed subscheme; the child constructs the initial supporting subscheme and local dimension, with no input etale cover to lift.
lem-trf-pointed-etale-ambient-lift vs lem-weil-pbc-affine-etale-closed-immersion-lift: the existing node gives one unpointed square over a single ambient scheme; the child proves base-change compatibility, etaleness of W->Z times_S S1, finite presentation of both changed immersions, the second cartesian identification over X, and the elementary pointed residue-field assertion. These are old steps 4--6, additional work rather than a renamed lifting lemma.

## Unfinished work and validation

No claimed proof of a new child is delivered: both are intentionally queued for independent workers. All seven arguments of the returned proof are preserved below, with old citation lists, as handoff material. The final dry run and push results will be recorded after they exit.

## Original arguments retained for the new workers

The following is a verbatim archive of the returned proof, not proof steps of either unsplit child.

### Original step 1: assigned to lem-trf-affine-fibre-support-model

Choose an affine open neighbourhood $V\subseteq S$ of $s$, and an affine chart $U\subseteq f^{-1}(V)$ containing $x$ on which the coordinate algebra is finite type over $\mathcal O_S(V)$, using the definition of locally finite type. Replace $X,S,\mathcal F$ by $U,V,\mathcal F|_U$. This is a finite type morphism of affine schemes. The support in its fibre is the intersection of the original support with the open $U_s$, so its dimension at $x$ is still $n$: the neighbourhoods inside $U_s$ are cofinal among neighbourhoods of $x$ in the original support. An open immersion is etale, preserves residue fields, and restriction of a module is its pullback. At the end compose the constructed neighbourhoods with $U\hookrightarrow X$ and $V\hookrightarrow S$; etaleness is preserved by composition and the pullback composition isomorphism identifies the resulting sheaf with the original pullback.

Cited statements: def-weil-finite-type-morphism, def-kun-dimension, lem-weil-pbc-etale-composition-cancellation, lem-weil-pbc-open-immersion-module-pullback-restriction, def-pc-module-pullback.

Source: literature/stacks-project/flat.tex, Tag 057S, lemma-elementary-devissage, proof paragraph 1 (affine reduction).

### Original step 2: assigned to lem-trf-affine-fibre-support-model

Apply the supporting-subscheme lemma to get $j:Z\hookrightarrow X$ of finite presentation and a finite-type quasi-coherent $\mathcal H$ with $j_*\mathcal H\cong\mathcal F$ and $|Z_s|=\operatorname{Supp}(\mathcal F_s)$. The hypothesis on $x$ gives a unique point $z\in Z_s\subseteq Z$ mapping to $x$. The scheme $Z$ is affine because $j$ is a closed immersion into an affine scheme. On coordinate rings, if $X=\operatorname{Spec}B$ and $S=\operatorname{Spec}A$, then $Z=\operatorname{Spec}(B/J)$; the images of finitely many $A$-algebra generators of $B$ generate $B/J$. Thus $Z\to S$ is finite type. The displayed equality of underlying fibre spaces gives $\dim_zZ_s=n$ by the definition of dimension.

Cited statements: lem-trf-finite-type-sheaf-fp-support, def-weil-closed-immersion, def-weil-finite-type-morphism, def-kun-dimension.

Source: literature/stacks-project/flat.tex, Tag 057S, proof, general case: apply Tag 057Q (lemma-sheaf-lives-on-subscheme).

### Original step 3: assigned to existing local-structure lemma, parent step 2

Apply the geometric affine local structure theorem to $Z\to S$ and $z$. Obtain elementary etale pointed neighbourhoods $b:(W,w)\to(Z,z)$ and $a:(S_1,s_1)\to(S,s)$, a finite $\pi:W\to Y$ with $\pi^{-1}(\{y\})=\{w\}$, and $h:Y\to S_1$ smooth of relative dimension $n$, with geometrically integral fibres and $\kappa(y)/\kappa(s_1)$ purely transcendental. Here $W,Y,S_1$ are affine and $pb=ah\pi$. This uses the local structure theorem for the scheme $Z$, rather than applying a module-devissage assertion to $\mathcal H$.

Cited statements: lem-trf-etale-finite-smooth-local-structure.

Source: literature/stacks-project/flat.tex, Tag 057S, proof paragraphs 2--3: Tags 057K and 057L applied to the supporting scheme $Z$.

### Original step 4: assigned to lem-trf-pointed-etale-ambient-lift

Put $T=X\times_SS_1$ and $D=Z\times_SS_1$. These are affine by the affine fibre-product formula. The map $D\to T$ is a closed immersion: writing $T=\operatorname{Spec}C$ with $C=B\otimes_A\mathcal O(S_1)$, its coordinate algebra is $C\otimes_B(B/J)=C/JC$. The affine finite-presentation criterion supplies a finite presentation of $B/J$ over $B$. Its base change is again finitely presented: a presentation $B/J=B[t_1,\ldots,t_r]/(q_1,\ldots,q_m)$ base changes to the finite presentation $C[t_1,\ldots,t_r]/(q_1,\ldots,q_m)$. The maps $b:W\to Z$ and $h\pi:W\to S_1$ define $v:W\to D$. The projection $D\to Z$ is etale, being the base change of $a$. Since its composite with $v$ is the etale map $b$, etale cancellation shows that $v$ is etale.

Cited statements: lem-weil-pbc-fibre-product-affine-spectra, def-weil-closed-immersion, def-sbc-locally-finite-presentation, def-pc-fibre-product, lem-weil-pbc-etale-scheme-base-change, lem-weil-pbc-etale-composition-cancellation, lem-weil-pbc-lfp-affine-opens-finite-presentation.

Source: literature/stacks-project/flat.tex, Tag 057S, proof, diagram $Z\prime	o Z	imes_SS\prime	o X	imes_SS\prime$ and the paragraph following it.

### Original step 5: assigned to lem-trf-pointed-etale-ambient-lift

Apply affine etale lifting to the closed immersion $D\hookrightarrow T$ and the affine etale $v:W\to D$. It supplies an affine scheme $X\prime$ and an etale map $q:X\prime\to T$ such that $W\cong D\times_TX\prime$. The two fibre-product universal properties identify this with $Z\times_XX\prime$, compatibly with both projections: a map to either object is a pair of maps to $Z$ and $X\prime$ with equal composites to $X$. Set $Z\prime=W$ and let $i:W\to X\prime$ be its closed immersion. Explicitly its coordinate ring over an affine $X\prime=\operatorname{Spec}C\prime$ is $C\prime\otimes_B(B/J)=C\prime/JC\prime$; base changing the finite presentation used in the preceding step gives finite presentation of $i$.

Cited statements: lem-weil-pbc-affine-etale-closed-immersion-lift, def-pc-fibre-product, lem-weil-pbc-fibre-product-affine-spectra, def-weil-closed-immersion, def-sbc-locally-finite-presentation.

Source: literature/stacks-project/flat.tex, Tag 057S, proof, application of Tag 057R (lemma-lift-etale) after the base change to $S\prime$.

### Original step 6: assigned to lem-trf-pointed-etale-ambient-lift

Let $x\prime=i(w)$, $s\prime=s_1$, and $f\prime:X\prime\xrightarrow{q}T\to S_1$. Let $g:X\prime\xrightarrow{q}T\to X$. The second arrow in $g$ is etale by base change of $a$, so $g$ is etale by composition. The cartesian square implies $g(x\prime)=j(z)=x$ and $fg=af\prime$. For both closed immersions $j$ and $i$, the induced residue-field maps are isomorphisms. The elementary neighbourhood $b$ induces $\kappa(z)\cong\kappa(w)$. The equality $gi=jb$ on $W$ therefore gives that $\kappa(x)\to\kappa(x\prime)$ is an isomorphism, since its composite with the isomorphism $\kappa(x\prime)\to\kappa(w)$ is the composite of the two isomorphisms $\kappa(x)\to\kappa(z)\to\kappa(w)$. Moreover $f\prime i=h\pi$, so $\pi$ is a map over $S\prime$: by the cartesian square $qi$ is the composite of $v:W\to D$ with $D\hookrightarrow T$, and the projection of $D$ to $S_1$ composed with $v$ is $h\pi$ by the definition of $v$. Also $a(s_1)=ah\pi(w)=pb(w)=s$. Thus $g$ and $a$ are the required elementary pointed neighbourhoods.

Cited statements: lem-weil-pbc-etale-scheme-base-change, lem-weil-pbc-etale-composition-cancellation, lem-weil-pbc-closed-immersion-residue-field-iso.

Source: literature/stacks-project/flat.tex, Tag 057S, proof, last paragraph: choose $x\prime$ corresponding to $z\prime$.

### Original step 7: assigned to existing module-transport lemmas, parent step 4

Set $\mathcal G=b^*\mathcal H$ on $Z\prime=W$. Pullback preserves quasi-coherence and finite type, so $\mathcal G$ has the required module properties. Apply affine pushforward base change to the affine closed immersion $j:Z\to X$, the morphism $g:X\prime\to X$, and the quasi-coherent module $\mathcal H$ on $Z$. For the cartesian square constructed above it gives $g^*j_*\mathcal H\cong i_*b^*\mathcal H$. Composing with $j_*\mathcal H\cong\mathcal F$ yields $i_*\mathcal G\cong g^*\mathcal F$. Take $z\prime=w$ and $y\prime=y$. The finite map, singleton fibre, purely transcendental residue extension and smooth geometrically integral family are exactly the maps and points obtained in step 3, which have not been restricted or replaced. Together with the affine $X\prime$, this proves every asserted clause.

Cited statements: lem-weil-pbc-module-pullback-quasi-coherent, lem-weil-pbc-module-pullback-finite-type, lem-weil-pbc-affine-pushforward-base-change.

Source: literature/stacks-project/flat.tex, Tag 057S, proof, final completed diagram; module identification made explicit using coherent.tex Tag 02KG (lemma-affine-base-change).

## Dry-run correction

The first dry run rejected the short, though verbatim, pullback-composition quotation because the citation gate requires at least 40 characters. I expanded it to the full concluding sentence of def-pc-module-pullback, which explicitly contains the composition isomorphism. The proof itself needed no change.

## Final dry-run result

The required deliver.py --no-push invocation exited 0 and printed OK (not pushed), preflight passed, at 433e8ecb850. This ran the server delivery checks, including DAG and split review. Two new unsplit nodes, zero new Mathlib leaves; parent proof length 2070 characters. The delivery is now submitted using the required push invocation.
