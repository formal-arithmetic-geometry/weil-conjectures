# Repair of lem-sfb-normal-stein-constant-field

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-normal-stein-constant-field.json: statement unchanged; split, three assembly steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-normal-stein-model.json: statement; unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-normal-sections-algebraic-constants.json: statement; unsplit; no Mathlib match.
- citations.json: one exact statement quote for every cited node in every parent step.

## Attachments

None. There is no exact declaration under lean/WeilConjectures for the blueprint tag or the combined theorem. The project's Sheaf/AlgebraicGeometry/NormalSteinConstantField.lean theorem AlgebraicGeometry.exists_normal_stein_constant_field (line 91) has a sorry, so it is not an attachment. Its statement is compatible with the unchanged parent.

## WANTED

WANTED: de Jong, Families of curves and alterations, Lemma 5.2 proof, printed p.613, local publisher PDF, for inherited contextual provenance of lem-sfb-normal-stein-constant-field. The repair uses the locally available Stacks texts and does not depend on fetching this PDF.

## Returned point and its repair

The return asks for at least two comparable separate work items, a parent assembly of at most 3000 characters, and preservation of every old argument. This delivery adds exactly two unsplit statements with empty proof and proof_deps and null proof_origin. The parent assembly is 1725 characters. The old normal Stein geometry (steps 1--4, 3363 characters including setup) and the old constant-field calculation (steps 5--7, 2438 characters) become separately claimable arguments. They are comparable in size; neither moves the whole item into one node.

The geometric work item is stated for integral Noetherian schemes with no chosen base field and has no function-field conclusion. The constants work item is stated for an arbitrary dominant map to the spectrum of a domain, requires finite global sections explicitly, has no properness or finite-type hypothesis and constructs no Stein scheme. These are independent arguments with different inputs. The elementary finite-type-over-k deduction stays in the parent. This is the human-requested re-split of the already reviewed proof, not a replacement of its route or a shortened version of its hard arguments.

The sandbox initially held only dispatcher .brief files, not node files, a report, citations or a search log. The current shared-repository node was copied as the repair baseline. Its old searches, statement, source, provenance, audit and Lean metadata are retained. No repository or launcher files were written and no git or compiler command was run there.

## Argument allocation for the new workers

For lem-sfb-noetherian-normal-stein-model, start from the original steps 1--4 transcribed below. Noetherianity is now a hypothesis, so the field-specific first sentence is handled by parent step 1. Properness gives qcqs. Relative normalization gives the global scheme, dominant first map and integral source preservation, and identifies its affine rings with the integral closure of A in R. Integral global sections make that closure R itself. The normal-stalk theorem applies because T is locally Noetherian. The original Noetherian kernel induction proves coherence of O_T, so coherent cohomology in degree zero makes every R finite over A. Its affine charts prove q finite. Affine Stein gives properness and geometric connectedness of g on the charts, and target-local properness glues it. Dominance of q follows from f=qg. The polynomial-over-k algebra-generation paragraph belongs to parent step 2, not to this field-free statement. The original germ-injectivity observations also provide the embeddings used by the constants worker. Every lemma used by this plan is named in the verbatim original steps below; the new node itself remains statement-only.

For lem-sfb-normal-sections-algebraic-constants, use the original steps 5--7, with X in place of U, and finite R over A as a hypothesis. The maps A to R to E are injective: dominance gives the function-field inclusion for A, and the germ map for R is injective by injectivity on every nonempty affine open plus the sheaf axiom. The image of any section on a nonempty affine open determines it on all X, since affine overlaps are nonempty in an integral scheme. Finite R over A is integral (the determinant trick: multiplication by r on finite module generators gives a monic polynomial annihilating R, and apply it to 1). Then S^(-1)R over F is an integral domain integral over a field, hence a field and equal to Frac R, exactly as the old step 5 spells out. Its finite spanning family proves finite degree. For the reverse inclusion preserve the exact coefficient calculation in old step 6: if d clears the c_i, the coefficient of (da)^(n-i) is d^i c_i, which lies in A. Normality in every local ring places da in that ring, and the cited sections-glue statement makes it a single global section. The same polynomial and gluing prove the additional explicit denominator conclusion. The old finite-spanning-family proof in step 7 proves algebraic closedness in E, without a separability hypothesis. No assertion about properness is needed in this new work item.

## Complete original argument retained verbatim

The following is the returned seven-step proof, not proof steps in either new unsplit node. Keeping it here ensures that all arguments remain available to the workers assigned the new statements, including the coherence induction, polynomial coefficients and finite-spanning-family transitivity proof.

### Original step 1

Both $T$ and $B$ are Noetherian by [lem-weil-pbc-finite-type-over-noetherian], applied to their finite-type structure maps to the spectrum of the Noetherian field $k$. For any affine open $V=\operatorname{Spec}A\subseteq B$ put $U=f^{-1}V$ and $R_V=\Gamma(U,\mathcal O_T)$. The restriction $f_V:U\to V$ is proper by [lem-weil-pbc-proper-fp-permanence](b). When $V$ is nonempty, dominance gives $U\ne\varnothing$. The germ maps embed $A$ and $R_V$ into $E$: on any nonempty affine open of the integral source, injectivity is [lem-sc-integral-function-field-affine-fraction], and the sheaf axiom extends injectivity to arbitrary opens. Under these embeddings $\operatorname{Frac}(A)=F$, with the given inclusion $F\subseteq E$.

Uses: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-proper-fp-permanence, lem-sc-integral-function-field-affine-fraction. Source: literature/stacks-project/more-morphisms.tex, theorem-stein-factorization-Noetherian (03H0), Noetherian setup; morphisms.tex, lemma-finite-type-noetherian (01T6) and lemma-integral-scheme-rational-functions (01RV).

### Original step 2

Form the relative normalization $T\xrightarrow{g}B_0\xrightarrow{q}B$ by [lem-weil-pbc-relative-normalization]; properness supplies quasi-compactness and quasi-separatedness. Its statement gives integrality of $B_0$, dominance of $g$, and the following description on every affine $V$: $q^{-1}V=\operatorname{Spec}A'_V$, where $A'_V$ is the integral closure of $A$ inside $R_V$, and the map from $U$ is induced by $A'_V\hookrightarrow R_V$. By [lem-weil-pbc-stein-integral-global-sections], every element of $R_V$ is integral over $A$, so $A'_V=R_V$. Thus this normalization is exactly $\underline{\operatorname{Spec}}_B(f_*\mathcal O_T)$, with the chart and evaluation map required in the statement, not a different finite model. Since $T$ is locally Noetherian and normal, [lem-sbc-relative-normalization-normal-stalks] gives normality of $B_0$.

Uses: lem-weil-pbc-relative-normalization, lem-weil-pbc-stein-integral-global-sections, lem-sbc-relative-normalization-normal-stalks. Source: literature/stacks-project/more-morphisms.tex, lemma-stein-universally-closed (03GY), construction as relative normalization; morphisms.tex, definition-normalization-X-in-Y (035H), lemma-characterize-normalization (035I), lemma-normal-normalization (035L).

### Original step 3

The structure sheaf on the Noetherian scheme $T$ is coherent in the kernel sense of [pqf-def-coherent]. Indeed on a Noetherian affine chart $\operatorname{Spec}C$, a map $\mathcal O^n\to\mathcal O$ has kernel associated to a submodule of $C^n$ (localize the module kernel on basic opens using [lem-weil-pbc-localization-module-exact]), and this submodule is finitely generated: induct on $n$, projecting to the last coordinate, whose image is a finitely generated ideal, and adjoining lifts of its generators to generators of the kernel of that projection. This verifies locally the finite-type kernel condition; $\mathcal O$ itself has generator $1$. Consequently [lem-pc-coherent-hi] in degree zero, applied to each proper $f_V$ over the Noetherian ring $A$, makes $R_V$ a finite $A$-module. By [def-weil-finite-integral-morphism] the affine map $q$ is finite. Taking a finite affine cover of the finite-type $k$-scheme $B$ by finitely generated $k$-algebras $A$, each $R_V$ is generated as a $k$-algebra by generators of $A$ together with finitely many $A$-module generators of $R_V$; hence $B_0$ is of finite type over $k$. Finally $q$ is dominant, since $f=qg$ is dominant and its image is contained in the image of $q$.

Uses: pqf-def-coherent, lem-pc-coherent-hi, def-weil-finite-integral-morphism, def-weil-finite-type-morphism, lem-weil-pbc-localization-module-exact. Source: literature/stacks-project/more-morphisms.tex, theorem-stein-factorization-Noetherian (03H0), finiteness paragraph; coherent.tex, proposition-proper-pushforward-coherent (02O5), lemma-proper-over-affine-cohomology-finite (02O6); local coherence verified directly.

### Original step 4

On $U\to q^{-1}V=\operatorname{Spec}R_V$, the chart description in step 2 is the canonical affine Stein factorization of $f_V$. Therefore [lem-weil-pbc-stein-factorization-affine] gives properness and geometrically connected fibres on each such chart. The opens $q^{-1}V$ cover $B_0$, so [lemma-nagata-projective-target-local] gives properness of $g$. A fibre of $g$ over a point of $q^{-1}V$, after any field extension of that point's residue field, is exactly the corresponding fibre of this restricted morphism. Thus every fibre of $g$ is geometrically connected.

Uses: lem-weil-pbc-stein-factorization-affine, lemma-nagata-projective-target-local. Source: literature/stacks-project/more-morphisms.tex, theorem-stein-factorization-general (03H2), property (1), restricted to affine base charts; morphisms.tex, lemma-proper-local-on-the-base (01W2).

### Original step 5

Fix a nonempty affine $V=\operatorname{Spec}A\subseteq B$, and write $R=R_V$. Since $B_0$ is integral, [lem-sc-integral-function-field-affine-fraction] on its nonempty affine open $q^{-1}V$ identifies $k(B_0)$ with $L=\operatorname{Frac}R$. The embedding $R\subseteq E$ from step 1 therefore identifies $L$ with a subfield of $E$, and the evaluation description of $g$ makes this exactly its induced function-field inclusion. The integral extension $A\subseteq R$ gives $S^{-1}R$, $S=A\setminus\{0\}$, integral over the field $F$. It is a domain, hence a field: for $0\ne r$ a monic polynomial of least degree over $F$ has nonzero constant term, and its equation expresses $r^{-1}$ as an $F$-linear combination of powers of $r$. Therefore $S^{-1}R=L$. The finite $A$-module generators of $R$ span $L$ over $F$, so $[L:F]<\infty$, and every element of $L$ is algebraic over $F$.

Uses: lem-sc-integral-function-field-affine-fraction. Source: literature/stacks-project/properties.tex, lemma-normal-integral-sections (0358), fraction-field viewpoint; elementary localization of the finite integral domain extension established in steps 2 and 3.

### Original step 6

Conversely, let $a\in E$ be algebraic over $F=\operatorname{Frac}A$. Choose an equation $a^n+c_1a^{n-1}+\cdots+c_n=0$ with $c_i\in F$, and choose a nonzero common denominator $d\in A$ with $dc_i\in A$ for every $i$. Multiplying by $d^n$ shows that $b=da$ satisfies the monic equation $b^n+(dc_1)b^{n-1}+(d^2c_2)b^{n-2}+\cdots+d^nc_n=0$ over $A$. For each $x\in U$, the image of $A$ is contained in $\mathcal O_{T,x}$, so $b$ is integral over that local ring. Its fraction field is $E$: take a nonempty affine neighbourhood $W=\operatorname{Spec}C$ of $x$, use [lem-sc-integral-function-field-affine-fraction] to get $E=\operatorname{Frac}C$, and then $\mathcal O_{T,x}=C_{\mathfrak p_x}$ has the same fraction field. Normality of $T$ implies $b\in\mathcal O_{T,x}$ for all $x\in U$. The statement of [lem-sc-function-field-sections-glue] now gives $b\in\Gamma(U,\mathcal O_T)=R$. Since $d\ne0$ belongs to $A\subseteq R$, we obtain $a=b/d\in L$.

Uses: lem-sc-integral-function-field-affine-fraction, lem-sc-function-field-sections-glue. Source: literature/stacks-project/properties.tex, lemma-normal-integral-sections (0358), local integrality and gluing argument adapted to a polynomial over the fraction field of the base.

### Original step 7

Steps 5 and 6 give $L=\{a\in E:a\text{ is algebraic over }F\}$, the field defined in [def-weil-relative-algebraic-closure], and step 5 already proves its finiteness over $F$. It is algebraically closed in $E$: if $z\in E$ is algebraic over $L$, then $L[z]$ is spanned over $L$ by finitely many powers of $z$; multiplying these powers by a finite $F$-spanning family of $L$ makes $L[z]$ finite-dimensional over $F$. The powers of $z$ are consequently $F$-linearly dependent, so $z$ is algebraic over $F$ and belongs to $L$ by step 6. This completes all the assertions without assuming separability or normality of $B$.

Uses: def-weil-relative-algebraic-closure. Source: literature/stacks-project/fields.tex, lemma-algebraic-elements (09GI); elementary finite-spanning-family proof of algebraic transitivity.

## Search review

Whole-DAG searches by 03H0, 0358, 035L and by Stein, relative algebraic closure, algebraic sections and normal sections were inspected. The blueprint search ran for Stein, algebraic closure, normal integral, normal Stein, algebraic constant and algebraic over; no blueprint statement gives either new result. The nearest blueprint ancestor command prints None, agreeing with the inherited null from.node. No imported blueprint ancestry was fabricated.

The new Mathlib searches ran only with msearch.py, with each new node's precise statement in mind. Full printed outputs are in each node's mathlib_searches; searches.jsonl is the command's unchanged log. Both first semantic searches and both Loogle searches succeeded. The second natural-language phrasings were actually tried but hit LeanSearch's global rate limit and are recorded unavailable. Grep ran for each statement and then targeted the missing conclusions. Normalization.lean (especially lines 200--240 and 341--360), Morphisms/Proper.lean lines 151--179, and FunctionField.lean lines 45--120 were read. The hits give normalization's integral charts, dominance and integral scheme instances, global-section finiteness only over a field, and function-field fraction-ring instances. They do not give the whole normal finite Stein theorem over a Noetherian base or the algebraic rational-function/global-section equality in one line. IsIntegrallyClosed is a local algebra ingredient, not the scheme gluing assertion. No Mathlib leaf was manufactured from a multi-step argument.

## Review by Q135

I read Stacks more-morphisms.tex, theorem-stein-factorization-Noetherian (03H0), including its construction via relative normalization and coherent pushforward; morphisms.tex, lemma-normal-normalization (035L), including its hypotheses and normal integral components argument; properties.tex, lemma-normal-integral-sections (0358), including local integrality and gluing; coherent.tex, proposition-proper-pushforward-coherent and lemma-proper-over-affine-cohomology-finite; and fields.tex, lemma-algebraic-elements (09GI). These support the two new work items as described above. The relative algebraic-function version of 0358 is explicitly marked an agent adaptation, not falsely attributed as its verbatim statement. The parent's inherited de Jong citation is contextual, with the missing local PDF recorded above.

Parent step 1 uses the finite-type-over-Noetherian statement with S=Spec k; the elementary ideal argument verifies this base is Noetherian. I read its statement: it actually concludes Noetherianity for each of T and B. The new Stein-model statement assumes precisely those Noetherian, integral, dominant and proper hypotheses and source normality already given; its conclusion explicitly includes finiteness, both dominant maps, normal integrality, properness, geometric connectedness, affine sections and evaluation. Thus parent step 1 takes none of these properties merely from a definition or a cited node's proof.

Parent step 2 uses exactly the finite-affine-cover characterization in def-weil-finite-type-morphism and the finite-module charts supplied by step 1. The finite list of module generators plus base algebra generators proves the stated algebra generation directly. No finiteness or Noetherianity theorem is hidden here.

Parent step 3 uses the new constants statement with X=U and A the section ring of the chosen nonempty base affine. Dominance ensures U is nonempty and its map to that affine is dominant; normality and integrality restrict to U by their local definitions. The finite-module hypothesis is an explicit conclusion of the Stein-model statement, not merely integrality. I read the affine-fraction node: it states injectivity and that the function field is the fraction field of the nonempty affine section ring, so it applies to both B and B_0, without dimension-one restrictions. The common generic stalk identifies k(U) with k(T), and the evaluation section map identifies the two embeddings of Frac R in E. The constants node's actual statement gives the equality, finite degree and algebraic closedness. Every parent citation has its exact full-statement quote in citations.json.

For the preserved geometry argument I opened every cited statement: relative-normalization gives its affine closure description and integral source preservation; integral-global-sections really asserts integrality; relative-normalization-normal-stalks requires local Noetherianity, which is present; coherent-hi requires coherence of O_T, which the original kernel induction proves rather than assumes; localization-module-exact supplies localization of that kernel; affine Stein supplies both properness and geometric connectedness, and target-local properness supplies the global assertion. For the preserved constants argument the affine-fraction statement supplies the fraction fields, while function-field-sections-glue gives a section from membership in all stalks. Algebraic transitivity is the explicit finite-spanning-family argument retained below the new worker's plan. These generic tools do not replace the blueprint's alteration/direct-image route.

I tested identity maps on a normal integral base (R=A), normalization of the cusp k[t^2,t^3] inside k[t] (the base may be nonnormal), projective space over a normal base (the constants do not change), a finite purely inseparable extension of fields (finite degree holds without separability), and a proper normal variety over a field (global sections form the constant field). The empty scheme cannot violate either statement because integral includes nonempty. In the constants statement A is a domain, so d is nonzero in E by dominance and every division performed is legitimate. Noetherianity is not silently imposed there. Dropping the finite-module hypothesis would fail for X=Spec F(t) over F, which is why it is explicit. I checked that no parent step is longer than 2000 characters; the parent is below the 3000-character repair bound. Both new nodes contain no proof sketches, proof steps or proof dependencies. No SGA source is used. The parent statement was not disputed or changed.

## Not duplicates

- lem-sfb-noetherian-normal-stein-model vs lem-sbc-dvr-generic-galois-normalization: concerns normalizing a DVR base in finite Galois generic spectra, a different source and no arbitrary normal scheme section field.

- lem-sfb-noetherian-normal-stein-model vs lem-sbc-finite-normal-dense-open-comparison: compares two already supplied finite covers extending an isomorphism on a dense open; it constructs no Stein model.

- lem-sfb-noetherian-normal-stein-model vs lem-sbc-integral-closure-finite-normal-product: is an algebraic normal-stalk assertion for an integral closure in a product, not either scheme theorem here.

- lem-sfb-noetherian-normal-stein-model vs lem-sbc-normal-finite-stage-diagram: constructs an approximation diagram and compatible cone, not the relative spectrum of proper direct-image sections.

- lem-sfb-noetherian-normal-stein-model vs lem-sbc-normal-finite-stage-universal: constructs universal finite approximation stages of a normal inverse limit; it does not concern a proper morphism or Stein fibres.

- lem-sfb-noetherian-normal-stein-model vs lem-sbc-normal-sections-finite-product: decomposes sections as a finite product of normal domains; it neither constructs a finite Stein morphism nor identifies algebraic rational constants over a base domain.

- lem-sfb-noetherian-normal-stein-model vs lem-sbc-normalization-algclosed-field: normalizes an affine target inside an algebraically closed field; it requires that special source and gives no finite Stein model or relative constants assertion.

- lem-sfb-noetherian-normal-stein-model vs lem-sbc-relative-normalization-normal-stalks: gives normality of relative-normalization stalks only; it neither proves finite Stein geometry nor identifies algebraic functions with fractions of global sections.

- lem-sfb-noetherian-normal-stein-model vs lem-sbc-root-normalization-stalk-principal-ideal: proves a maximal ideal is principal at a selected root-normalization stalk, not a Stein factor or global constants field.

- lem-sfb-noetherian-normal-stein-model vs lem-sbc-stalk-normalization-normal-dense: gives normality and density after a specific smooth/etale stalk normalization, with no finite Stein base or algebraic constants equality.

- lem-sfb-noetherian-normal-stein-model vs lem-sbc-stalk-normalization-normal-part: asserts normality after a particular stalk base change of an etale normalization, with no Stein finiteness or constants calculation.

- lem-sfb-noetherian-normal-stein-model vs lem-sfb-normal-stein-constant-field: is the returned parent over a field and includes both geometry and the function-field identification; this new node isolates one independent argument with the broader inputs described above, as explicitly requested by the re-split return.

- lem-sfb-noetherian-normal-stein-model vs lem-trf-no-isolated-contracted-fibre-component: rules out contracted isolated components of nodal families; it constructs no normal Stein model.

- lem-sfb-noetherian-normal-stein-model vs lem-trf-stein-smooth-generic-curve: requires an excellent base and a smooth irreducible generic curve and proves additional separability and smoothness; the new geometric theorem applies in arbitrary dimension to a normal source without those hypotheses.

- lem-sfb-noetherian-normal-stein-model vs lem-weil-pbc-constructible-finite-pushforward-noetherian: embeds a constructible torsion sheaf into finite pushforwards and makes neither new scheme conclusion.

- lem-sfb-noetherian-normal-stein-model vs lem-weil-pbc-normalization-in-residue-field-extension: normalizes in a specified finite residue-field extension and constructs a generic point model, not a Stein model for a proper normal source.

- lem-sfb-noetherian-normal-stein-model vs lem-weil-pbc-normalization-normal-stalks: gives only normality of the relative normalization, no finite Stein geometry or algebraic rational-function/global-section equality.

- lem-sfb-normal-sections-algebraic-constants vs def-weil-relative-algebraic-closure: defines the intermediate field of algebraic elements but does not identify it with finite global sections or give the denominator property.

- lem-sfb-normal-sections-algebraic-constants vs lem-sbc-normal-sections-finite-product: decomposes sections as a finite product of normal domains; it neither constructs a finite Stein morphism nor identifies algebraic rational constants over a base domain.

- lem-sfb-normal-sections-algebraic-constants vs lem-sbc-relative-normalization-normal-stalks: gives normality of relative-normalization stalks only; it neither proves finite Stein geometry nor identifies algebraic functions with fractions of global sections.

- lem-sfb-normal-sections-algebraic-constants vs lem-weil-pbc-normalization-normal-stalks: gives only normality of the relative normalization, no finite Stein geometry or algebraic rational-function/global-section equality.

Other close statements read: thm-weil-pbc-stein-inputs requires a henselian pair and does not assert the arbitrary normal Stein model or the relative constant-field equality; lem-trf-proper-normal-geometric-connectedness assumes a normal base and trivial generic constants and does not construct the Stein scheme. The affine Stein node is reused in the geometric argument plan, but it has no finite-over-Noetherian or normal-integral-base conclusion. The new constants node does not assume or derive the Stein construction, so neither new statement depends on the parent or on the other new node.

## Unfinished work

Only the requested one-level split is done. The two new statements intentionally remain unsplit for other workers to prove in parallel. No Lean was written or compiled. Required server dry run and push are performed after this report is written.
