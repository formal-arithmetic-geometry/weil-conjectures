# Worker report: lem-sfb-proper-curve-bundle-pullback-degree

1. Files written:
   - `dag/nodes/sec-six-functors-basics/lem-sfb-proper-curve-bundle-pullback-degree.json`: statement and statement dependencies unchanged; four-step assembly, 1506 characters; no Mathlib match.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-proper-curve-finite-direct-image-rank.json`: new statement-only unsplit lemma, no Mathlib match; finite-map reduction, Noetherianity, coherent direct image and generic rank.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-finite-map-locally-free-euler-comparison.json`: new statement-only unsplit lemma, no Mathlib match; finite locally free projection, coherence, scalar-compatible cohomology and Euler comparison.
   - `citations.json`: five verbatim full-statement quotes, one for each step/node citation. Search evidence and `returned-node.json` are sandbox-only supporting files.
2. Attachments: none. The existing `AlgebraicGeometry.Scheme.Modules.proper_curve_bundle_pullback_degree` in `Sheaf/AlgebraicGeometry/ProperCurveBundlePullbackDegree.lean` has `sorry`. Searches of `WeilConjectures/` by blueprint tag and degree/pullback, finite curve, rank and cohomology terminology found no exact proved project theorem. `Scheme.Hom.degree_pullback` in Modules/Ample.lean:830 assumes ampleness and uses Hilbert degree; the divisor theorem in Curve/DivisorPullback.lean:259 assumes smooth curves over an algebraically closed field and finite flatness. Neither covers this item.
3. WANTED: none.
4. Fault repaired: the released 2026-10-22 stage-1 repair note explicitly requires at least two new comparable statement-only nodes and an assembly of at most 3000 characters. The old seven-step proof had 4128 characters. Its mathematics and statement remain intact; the work is now distributed between two independently stateable lemmas. This is not an unchanged re-push. No statement dispute or source error was found.
5. Unfinished: the two new lemmas deliberately remain unsplit for other workers. No Lean, compilers, Lake, repository writes or manual git commands were used. The initial sandbox held only dispatcher markers, so I reconstructed the delivered version from the live item and the retained Q26 and N0 reports; there was no split/report in the sandbox on which to run an initial dry run.

## Repair mapping and arguments for the next workers

The new nodes have no proofs or proof dependencies. The following arguments are retained here so that none of the old work disappears, while their statements describe exactly the independent tasks to formalize.

`lem-sfb-proper-curve-finite-direct-image-rank` carries old step 1, the Noetherian/structure-sheaf portion of step 2, and step 3. Use `lem-weil-pbc-proper-over-separated` to make f proper, hence locally of finite type. Apply `lem-trf-birational-curve-quasifinite`, whose statement actually allows every dominant finite-generic-extension map of integral separated finite-type dimension-one schemes, then `pqf-lem-proper-lqf-finite`; affineness is in `def-weil-finite-integral-morphism`. A field has just the ideals (0) and (1), both finitely generated; `lem-weil-pbc-finite-type-over-noetherian` gives Noetherian X and Y. Their structure sheaves are locally rank one and quasi-coherent, so `pqf-lem-coherent-ft-locnoeth` gives coherence. Finite pushforward coherence is precisely `lem-weil-pbc-finite-pushforward-coherent`. Finally the EXISTING `lem-sfb-finite-dominant-generic-pushforward-stalk` identifies F at eta_Y with k(X) as a k(Y)-algebra for the actual generic stalk map. Taking dimension and using `def-pc-field-tower` gives rank d. This new node does not duplicate the generic-stalk comparison: that comparison assumes finiteness and states neither the finite reduction nor coherence. It is an input to the new task, not rewritten.

`lem-sfb-finite-map-locally-free-euler-comparison` carries the invertible/coherent part of old step 2, all of steps 4--5, and the explicit Euler well-definedness that the old text left in its phrase “therefore defined”. Pullback of an invertible sheaf is `lem-weil-pbc-invertible-pullback-tensor` (1); for a finite locally free E the same free-basis pullback calculation gives finite local freeness, even with varying ranks. On a trivializing open, E is a finite direct sum of O and f*E is the same finite direct sum of O_X. Thus E, f*E and f*E tensor N are quasi-coherent of finite type; with local Noetherianity, `pqf-lem-coherent-ft-locnoeth` gives coherence. Use `lem-weil-pbc-finite-pushforward-coherent` on N and f*E tensor N. The projection map sends e tensor n to f*e tensor n. On a basis e_1,...,e_r it is the identity on (f_*N)^r. On overlaps let e'_i = sum_j a_ji e_j for an invertible matrix A over O_Y. Both descriptions then send the coefficient vector (n_i) to (sum_i f*(a_ji)n_i)_j; the inverse change uses A^{-1}. Hence these inverse maps agree and glue. For rank one A is a unit u, giving exactly the old overlap calculation; for rank zero both sides are zero. The tensor target is coherent because it is isomorphic to that coherent direct image. A finite map is affine, so `lem-weil-pbc-affine-morphism-cohomology-edge` gives the edge isomorphisms for the quasi-coherent N and f*E tensor N. Its statement is linear over Gamma(Y,O_Y), not just additive. Restrict scalars along k; f being a k-morphism makes the resulting scalar action on X the specified one. `lem-pc-euler-characteristic-well-defined` gives finite dimensions and finite support on both proper schemes for all coherent sheaves involved. Alternating dimensions and the projection isomorphism give both Euler identities. Tensor-unit identifications for N=O_X are ordinary unit maps, sending m tensor a to am.

Old step 6 remains assembly step 3: apply the existing `lem-trf-curve-euler-tensor-generic-rank` to Y, M and F of rank d, and substitute the two Euler identities. Old step 7 remains assembly step 4: subtract chi(X,O_X) and invoke `def-pc-degree-line-bundle`. Neither independent child concludes any pullback-degree equality; the essential degree identity still needs the existing Euler-twist theorem.

## Sources and searches

I read Stacks `varieties.tex`, Tag 0AYZ (`lemma-degree-pullback-map-proper-curves`, line 9896), with all four displayed equalities, and 0AYV (`lemma-degree-on-proper-curve`, line 9669). For the geometry node I read 0AB6 (`lemma-quasi-finite-in-codim-1`, varieties.tex:3188), Morphisms 01W6 (`lemma-image-proper-scheme-closed`, morphisms.tex:9949), 01T6 (`lemma-finite-type-noetherian`, morphisms.tex:2765), and More on Morphisms 02LS (`lemma-characterize-finite`, more-morphisms.tex:12544). For coherence and the comparison node I read 01XZ (`lemma-coherent-Noetherian`, coherent.tex:2225), 01Y6 (`lemma-finite-pushforward-coherent`, coherent.tex:2455), 089W (`lemma-relative-affine-cohomology`, coherent.tex:202), 01E8 (`lemma-projection-formula`, cohomology.tex:13843), and 0B8L (`lemma-pullback-invertible`, modules.tex:4143). Tags were checked against tags/tags, not inferred from section numbering.

Before creating nodes I searched the whole DAG by 0AYZ, 01E8, 089W, 01Y6, 01XZ, 01T6, 0AB6, 02LS, generic rank/stalk/function-field/pushforward, projection formula and finite Euler comparison. I opened the nearby statements listed below, including the finite-ideal-twist and integral-filtration Euler comparisons. Blueprint searches ran for “finite curve”, “generic rank”, “Euler characteristic”, “0AYZ”, “projection formula”, and “finite locally free”. There is no blueprint node stating either extracted task. `blueprint_refs.py ancestor` returns None, agreeing with the item's inherited null ancestor; both children inherit it and prepend the item to via. I read the current main-20261015 direct-images proof (3), as well as the chapter/unit records; no chapter or unit route was changed. These are generic algebraic-curve tools in the inherited auxiliary chain.

The exact successful msearch queries and outputs are recorded in the nodes and searches.jsonl. Each new node has LeanFinder twice, Loogle, LeanSearch and Mathlib grep; additional broader finite-locally-free searches are also logged. I read the returned infrastructure near-matches: Mathlib FunctionField.lean:36--66 defines function fields and injective germ maps, Spec.lean:366--406 gives a localized direct-image stalk map, Proper.lean:161 gives a finite GLOBAL section field for a proper integral scheme over a field. None gives the full geometry node. Modules/Sheaf.lean:187 gives pullbackPushforwardAdjunction; it supplies an adjunction, not the projection/cohomology/Euler statement. Other semantic hits concern finite fibres, rational maps, or sheaf-category isomorphisms. The item's grep hits in Polynomial/Splits.lean:104 concern polynomial leading coefficients, and the ChevalleyComplexity hits are comments; neither is a line-bundle degree theorem. No Mathlib leaf is claimed. All older item searches are preserved.

## Not duplicates

lem-sfb-proper-curve-finite-direct-image-rank vs lem-trf-fibre-degree-ample-criterion: the existing statement is an ampleness criterion from positive degrees on normalized components; it has neither this finite/coherent preparation nor this cohomology comparison.

lem-sfb-proper-curve-finite-direct-image-rank vs lem-sfb-proper-curve-bundle-pullback-degree: the item concludes a degree equality; the new lemma provides only the finite/coherent/generic-rank preparation, with no line bundle or Euler equality.

lem-sfb-proper-curve-finite-direct-image-rank vs lem-sfb-finite-dominant-generic-pushforward-stalk: the existing lemma assumes finiteness and identifies a generic algebra stalk on arbitrary integral schemes; the new lemma proves finiteness and coherence from proper-curve hypotheses and gives the numeric rank, using that existing comparison.

lem-sfb-finite-map-locally-free-euler-comparison vs lem-trf-finite-ideal-twist-cohomology-comparison: the existing statement concerns invertible powers and an ideal multiple H; the new lemma treats arbitrary finite locally free E (including rank zero and varying ranks), and additionally pins k-linearity, cohomology finiteness and Euler identities over proper k-schemes.

lem-sfb-finite-map-locally-free-euler-comparison vs lem-sc-picard-pullback-local-ranks: the existing node assumes universally invertible structure-sheaf units and a descent presentation to conclude local ranks; the new node has no such assumptions and states projection and cohomology comparison.

lem-sfb-finite-map-locally-free-euler-comparison vs lem-sc-tensor-unit-open-localization: the existing statement localizes the pullback-adjunction unit to open slices; the new node asserts finite-map projection, coherence and Euler comparison.

lem-sfb-finite-map-locally-free-euler-comparison vs lem-sc-finite-locally-free-tensor-unit: the existing lemma assumes an invertible unit on O_Y and concludes unit invertibility on a finite locally free module; the new node does not require that assumption and concerns a projection map and k-linear cohomology.

lem-sfb-finite-map-locally-free-euler-comparison vs lem-sc-picard-pullback-base-change: the existing statement is base-change invertibility under universally invertible structure units and descent data; the new lemma neither assumes these nor states base change.

lem-sfb-finite-map-locally-free-euler-comparison vs lem-sc-picard-pullback-evaluation: the existing lemma concludes a Picard rank condition and counit invertibility under descent and universal unit hypotheses; it does not give finite-map Euler comparison.

lem-sfb-finite-map-locally-free-euler-comparison vs lem-weil-pbc-formal-functions-finite-quotient-maps: the existing statement concerns formal-functions or graded cohomology comparisons for quotient towers or graded pieces, not finite locally free projection with k-linear Euler comparison; its full statement was read in the source-tag duplicate search.

lem-sfb-finite-map-locally-free-euler-comparison vs lem-weil-pbc-formal-functions-finite-quotient-comparison: the existing statement concerns formal-functions or graded cohomology comparisons for quotient towers or graded pieces, not finite locally free projection with k-linear Euler comparison; its full statement was read in the source-tag duplicate search.

lem-sfb-finite-map-locally-free-euler-comparison vs lem-weil-pbc-affine-morphism-cohomology-edge: the existing node gives affine edge isomorphisms linear over target global sections; it states no finite locally free projection isomorphism, coherence or finite-dimensional Euler comparison.

lem-sfb-finite-map-locally-free-euler-comparison vs def-weil-pbc-formal-functions-finite-pullback: the existing statement concerns formal-functions or graded cohomology comparisons for quotient towers or graded pieces, not finite locally free projection with k-linear Euler comparison; its full statement was read in the source-tag duplicate search.

lem-sfb-finite-map-locally-free-euler-comparison vs def-weil-pbc-formal-functions-local-comparison: the existing statement concerns formal-functions or graded cohomology comparisons for quotient towers or graded pieces, not finite locally free projection with k-linear Euler comparison; its full statement was read in the source-tag duplicate search.

lem-sfb-finite-map-locally-free-euler-comparison vs lem-weil-pbc-formal-functions-finite-quotient-iso-b: the existing statement concerns formal-functions or graded cohomology comparisons for quotient towers or graded pieces, not finite locally free projection with k-linear Euler comparison; its full statement was read in the source-tag duplicate search.

lem-sfb-finite-map-locally-free-euler-comparison vs lem-weil-pbc-formal-functions-local-dictionary: the existing statement concerns formal-functions or graded cohomology comparisons for quotient towers or graded pieces, not finite locally free projection with k-linear Euler comparison; its full statement was read in the source-tag duplicate search.

lem-sfb-finite-map-locally-free-euler-comparison vs lem-weil-pbc-formal-functions-finite-quotient-iso: the existing statement concerns formal-functions or graded cohomology comparisons for quotient towers or graded pieces, not finite locally free projection with k-linear Euler comparison; its full statement was read in the source-tag duplicate search.

lem-sfb-finite-map-locally-free-euler-comparison vs lem-weil-pbc-formal-functions-local-stalk-comparison: the existing statement concerns formal-functions or graded cohomology comparisons for quotient towers or graded pieces, not finite locally free projection with k-linear Euler comparison; its full statement was read in the source-tag duplicate search.

lem-sfb-finite-map-locally-free-euler-comparison vs lem-weil-pbc-graded-finiteness-cohomology: the existing statement concerns formal-functions or graded cohomology comparisons for quotient towers or graded pieces, not finite locally free projection with k-linear Euler comparison; its full statement was read in the source-tag duplicate search.

lem-sfb-finite-map-locally-free-euler-comparison vs lem-weil-pbc-formal-functions-finite-quotient-iso-r: the existing statement concerns formal-functions or graded cohomology comparisons for quotient towers or graded pieces, not finite locally free projection with k-linear Euler comparison; its full statement was read in the source-tag duplicate search.

## Review by Q10

I checked the actual node statements and the source places above, including the old Q26 proof and N0 Lean-statement report. The imported statement is the rank-one case of 0AYZ and remains verbatim. X and Y are integral proper dimension-one finite-type schemes over the same arbitrary field; neither geometric integrality nor smoothness is present. The actual generic field map is retained. The return's sole demand is now met by TWO new independent statement-only tasks of comparable size (1332 and 1942 characters), not a shortened proof alone. The complete old proof is copied below and mapped above; none of its arguments was removed.

Assembly step 1 cites only `lem-sfb-proper-curve-finite-direct-image-rank`. Its statement explicitly gives finite f, locally Noetherian X,Y, coherent O_X and F, and numeric generic rank d, under precisely the item hypotheses. It does not rely on the proof of the old generic-stalk node without citing it: that existing lemma is explicitly identified as the input for the child worker in the argument map. Assembly step 2 cites `def-sc-invertible-module`, whose statement really gives quasi-coherence and local rank one, and the new finite-map comparison, whose statement explicitly gives invertibility/coherence and BOTH Euler identities. I checked N=O_X is coherent by step 1; f is finite by step 1, X,Y locally Noetherian by step 1, and both are proper by hypothesis. Tensor-unit identification is multiplication, with inverse m mapped to m tensor 1, so it hides no theorem. Step 3 cites `lem-trf-curve-euler-tensor-generic-rank`, whose displayed formula is exactly chi(M tensor F)=r deg(M)+chi(F). It permits arbitrary coherent F, including a non-locally-free one; integrality/properness/dimension one hold for Y, invertibility for M, coherence and r=d by step 1. Substitution is arithmetic. Step 4 cites the actual degree definition and is only subtraction; the pullback is invertible by step 2. Five full-statement quotes in citations.json substantiate all five citations verbatim. Proof dependency union is exact. No non-elementary step exceeds 2000 characters.

For the first child I checked finiteness does not require separability or flatness: 0AB6 (1) and 02LS apply after properness supplies local finite type. Its coherence conclusion requires local Noetherianity, obtained from finite type over k; it is not being asserted for arbitrary non-Noetherian schemes. Generic rank is not local freeness. For the second child I checked finite local rank may vary, the rank-zero case has zero projection source and target, and the overlap matrix commutes with the same multiplication on the source module. Coherence uses local Noetherianity; properness over k, coherence and finite type implicit in properness ensure finite-dimensional, eventually vanishing coherent cohomology. The k-morphism hypothesis is needed to compare the correct scalar actions. No clause assumes that finite morphisms are flat.

Small cases: identity maps give rank one and identity projection; Frobenius on P1 over F_p gives rank p and keeps its inseparability; finite normalization of an integral singular proper curve gives generic rank one with potentially nonflat direct image. M=O, negative-degree bundles and arbitrary base fields all retain the formula. For the comparison child, empty schemes, E=0, N=0 and rank variation on disconnected proper schemes give the zero or componentwise formulas; no connectedness is needed. A finite field extension Spec L -> Spec K verifies the scalar restriction and finite-dimensional Euler identity directly. The first child excludes empty/zero-dimensional objects through its curve hypotheses, while the second deliberately allows them. Non-dominant constant curve maps are excluded only where the first child needs dominance.

I checked B1--B10: each child is self-contained, every object introduced and every notion defined inline or cited, proof/proof_deps empty and proof_origin null, status unsplit, source tags/labels read, single TeX escapes after JSON decoding, actual logged searches, no Mathlib-match claim, complete blueprint metadata. C1--C8: the item uses only what each cited statement says; the retained argument maps list the actual existing inputs for the future child splits. The sole off-unit item proof input is the existing generic Euler-twist theorem, declared in split_report.tool_uses. D1--D5: neither child states the item's degree conclusion, and the two children do independent geometry and module-cohomology work; the parent still combines them with 0AYV. E1--E7: hypotheses and objects/scalars were checked as above; no invalid “transport” replaces the projection overlap calculation. No SGA source or new route is used.

Corrections made during this repair: I separated the curve finite/coherent preparation from projection/cohomology; generalized the latter from a single invertible bundle to finite locally free E and arbitrary coherent N to state the independent comparison argument; retained the invertible pullback clause needed by the parent; explicitly included finite cohomology support and base-field linearity so that taking alternating dimensions is justified. The new files remain statement-only, and all argument text is in this report. The server-only preliminary review_split returned PASS. The required full delivery dry run is recorded after completion.

## Retained returned proof, verbatim

### Old step 1

Since $X$ is proper over $k$ and $Y$ is separated over $k$, [lem-weil-pbc-proper-over-separated] applied to the commuting structure maps shows that $f$ is proper, in particular locally of finite type. Both schemes are integral separated finite-type curves of dimension one by [def-pc-curve]. Dominance and the finite function-field extension are precisely the remaining hypotheses of [lem-trf-birational-curve-quasifinite] (despite its id, its statement does not assume birationality). It follows that $f$ is quasi-finite at every point, hence locally quasi-finite. Apply [pqf-lem-proper-lqf-finite] to obtain that $f$ is finite, and thus affine by [def-weil-finite-integral-morphism].

Uses: lem-weil-pbc-proper-over-separated, def-pc-curve, lem-trf-birational-curve-quasifinite, pqf-lem-proper-lqf-finite, def-weil-finite-integral-morphism.

### Old step 2

A field is Noetherian: its only ideals are $(0)$ and $(1)$, generated by $0$ and $1$. Thus $\operatorname{Spec}k$ is Noetherian, and [lem-weil-pbc-finite-type-over-noetherian] makes $X,Y$ Noetherian. By [lem-weil-pbc-invertible-pullback-tensor] the sheaf $f^*\mathcal M$ is invertible. An invertible module is quasi-coherent and locally generated by one element, by [def-sc-invertible-module]; the structure sheaf has the same properties. Consequently [pqf-lem-coherent-ft-locnoeth] shows that $\mathcal O_X$, $\mathcal M$, and $f^*\mathcal M$ are coherent on their respective schemes. The coherent Euler characteristics of these sheaves on $X$ and $Y$ are therefore defined.

Uses: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-invertible-pullback-tensor, def-sc-invertible-module, pqf-lem-coherent-ft-locnoeth.

### Old step 3

Put $\mathcal F=f_*\mathcal O_X$. Step 1 gives finiteness of $f$ and Step 2 gives local Noetherianity of $Y$ and coherence of $\mathcal O_X$. Hence [lem-weil-pbc-finite-pushforward-coherent] makes $\mathcal F$ coherent. By [lem-sfb-finite-dominant-generic-pushforward-stalk], applied to the integral schemes $X,Y$ and the finite dominant map $f$, $\mathcal F_{\eta_Y}\cong k(X)$ as $k(Y)$-algebras for the actual generic stalk map of $f$. Therefore its generic rank is $\dim_{k(Y)}\mathcal F_{\eta_Y}=\dim_{k(Y)}k(X)=d$, where the last equality is the definition of field degree [def-pc-field-tower].

Uses: lem-weil-pbc-finite-pushforward-coherent, lem-sfb-finite-dominant-generic-pushforward-stalk, def-pc-field-tower.

### Old step 4

The canonical map $\alpha:\mathcal M\otimes_{\mathcal O_Y}\mathcal F\to f_*f^*\mathcal M$ sends $m\otimes a$ to $a f^*m$. It is defined from the pullback unit [def-pc-module-pullback] and the sheaf tensor product [def-pur-sheaf-tensor-product]. On any open $V$ with a basis $e$ for $\mathcal M|_V$ [def-sc-invertible-module], it is the identity map on $(f_*\mathcal O_X)|_V$ after writing $e\otimes a\mapsto a f^*e$. The local inverses agree on overlaps: replacing $e$ by $u e$ for a unit $u$ multiplies both expressions by $f^*u$. These inverses glue, proving $\alpha$ is an isomorphism. This is the rank-one, underived projection formula, proved directly in a local basis.

Uses: def-pc-module-pullback, def-pur-sheaf-tensor-product, def-sc-invertible-module.

### Old step 5

By [lem-weil-pbc-finite-pushforward-coherent], $f_*f^*\mathcal M$ is coherent as well, since $f^*\mathcal M$ is coherent and $Y$ is locally Noetherian. Since a finite morphism is affine, [lem-weil-pbc-affine-morphism-cohomology-edge] applies to $\mathcal O_X$ and $f^*\mathcal M$, both quasi-coherent by Step 2. It gives cohomology isomorphisms in every degree between each sheaf on $X$ and its direct image on $Y$. They are $k$-linear: the stated global-section scalar compatibility restricts along $k\to\Gamma(Y,\mathcal O_Y)$, since $f$ is a $k$-morphism. Taking the alternating sums of dimensions in [def-pc-euler-characteristic], and then using $\alpha$ from Step 4, gives
$$\chi(X,f^*\mathcal M)=\chi(Y,f_*f^*\mathcal M)=\chi(Y,\mathcal M\otimes\mathcal F),\qquad \chi(X,\mathcal O_X)=\chi(Y,\mathcal F).$$

Uses: lem-weil-pbc-finite-pushforward-coherent, lem-weil-pbc-affine-morphism-cohomology-edge, def-pc-euler-characteristic.

### Old step 6

Apply [lem-trf-curve-euler-tensor-generic-rank] to $C=Y$, the invertible sheaf $\mathcal M$, and the coherent module $\mathcal F$. The required integrality, properness and dimension one are hypotheses on $Y$; coherence and generic rank $d$ were proved in Step 3. The theorem yields
$$\chi(Y,\mathcal M\otimes\mathcal F)=d\deg_k(\mathcal M)+\chi(Y,\mathcal F).$$
Together with Step 5 this becomes $\chi(X,f^*\mathcal M)=d\deg_k(\mathcal M)+\chi(X,\mathcal O_X)$.

Uses: lem-trf-curve-euler-tensor-generic-rank.

### Old step 7

Subtract $\chi(X,\mathcal O_X)$ from both sides of the last equality of Step 6. By [def-pc-degree-line-bundle], the left hand side is $\deg_k(f^*\mathcal M)$; hence $\deg_k(f^*\mathcal M)=d\deg_k(\mathcal M)$, as claimed.

Uses: def-pc-degree-line-bundle.

## Delivery verification

The full required `deliver.py Q10 lem-sfb-proper-curve-bundle-pullback-degree --no-push` exited 0 and printed `OK (not pushed)` at d758b60058d: server preflight passed. The statement is unchanged, the assembly is 1506 characters, and the two new nodes are unsplit with empty proof fields. The final report includes this result; the same dry-run check is repeated for the final packet before pushing. No local DAG/preflight checker was run.
