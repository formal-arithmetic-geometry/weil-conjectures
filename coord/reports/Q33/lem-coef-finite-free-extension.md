# Repair report: lem-coef-finite-free-extension

## Files written

- dag/nodes/sec-six-functors/lem-coef-finite-free-extension.json: existing statement; short assembly, status split.
- dag/nodes/sec-six-functors/lem-sf-finite-free-derived-scalar-calculus.json: statement, unsplit; no Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep.
- dag/nodes/sec-six-functors/lem-sf-finite-free-image-comparison.json: statement, unsplit; no Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep.
- dag/nodes/sec-six-functors/lem-sf-finite-free-exceptional-mate.json: statement, unsplit; no Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep.
- dag/nodes/sec-six-functors/lem-sf-finite-free-comparison-transitivity.json: statement, unsplit; no Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep.
- dag/nodes/sec-six-functors/lem-sf-ramified-reduction-comparison-square.json: statement, unsplit; no Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep.
- dag/nodes/sec-six-functors/lem-sf-finite-free-etale-proetale-transport.json: statement, unsplit; no Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep.
- dag/nodes/sec-six-functors/lem-sf-finite-free-comparison-isomorphism-naturality.json: statement, unsplit; no Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep.

## Attachments

None. The exact upstream blueprint tag is absent from lean/WeilConjectures. The retained Sheaf.Paper.FiniteFreeCoefficientExtension declaration finite_free_coefficient_extension, lines 1288-1322, ends with sorry; it is not an attachment. The nearby upstream ScalarExtension files have finite-free scalar results and Frobenius-form hypotheses, but no declaration giving every clause of this item.

## WANTED

None. All sources used are present.

## What was wrong and what changed

The batch5 return asks to distribute the 16102-character proof among at least five independent statement-only tasks, leaving an assembly of at most 3000 characters. This delivery creates seven tasks, with empty proof, empty proof_deps and null proof_origin. The item has eight assembly steps totaling 2146 characters. Its statement, stmt_deps, source, all blueprint/import fields, and Lean record are unchanged. No Lean was written and no compiler was run.

The sandbox initially held only dispatcher markers, with no delivered node, report or search log. I recovered the 18-step returned proof from the current read-only repository, whose text and step lengths agree with the return. The complete text is preserved below, including every original citation and source, rather than compressed into vague proof hints. New source locations identify the precise argument blocks. The item retains all original Mathlib search records; all new searches are actual msearch.py invocations with full saved output and searches.jsonl. The delivery tool supplies the current-base overlay and rebase; no git command was run in the shared repository.

Two already-existing results must not be duplicated: lem-sfb-local-field-integral-basis already states the arithmetic basis conclusion of old steps 1-2, and lem-sf-ringed-finite-free-hom-base-change already states the evaluation-normalized unbounded internal-Hom comparison of old steps 7-8. Their arguments and the elementary double-dual assembly of old step 9 are retained below and cited in assembly steps 1 and 4. The remaining substantial arguments are distributed as follows.

## Argument allocation (complete returned proof preserved below)

| Returned steps | Task carrying the argument | Scope |
|---|---|---|
| 1-2 | Existing lem-sfb-local-field-integral-basis, lem-weil-l-adic-extension-absolute-value and lem-weil-l-adic-extension-integers-dvr | Integral basis, positive ramification factorization and quotient basis. The alternative complete-ring argument is preserved verbatim below; a second integral-basis node would duplicate the existing theorem. |
| 3 | lem-sf-finite-free-derived-scalar-calculus | Exact scalar/restriction adjunction, conservative restriction, K-flat extension, balancing maps, constructibility and unchanged Tor window. |
| 4-5 | lem-sf-finite-free-image-comparison | Unbounded K-injective restriction comparison, identification of the projection map by basis inclusions, inverse finite-sum matrices, open stalk calculation and compact-support comparison. |
| 6 | lem-sf-finite-free-exceptional-mate | Six Hom bijections, representing isomorphism, the actual exceptional counit transpose, finite-sum coordinates and inverse, basis independence. |
| 7-9 | Existing lem-sf-ringed-finite-free-hom-base-change and lem-weil-duality-pairing; assembly step 4 | Derived tensor-Hom transposition, evaluation-normalized Hom comparison, Verdier composite, evaluation and double-dual equation. |
| 10 | lem-sf-finite-free-comparison-transitivity | Identity and composition laws for actual projection/counit/evaluation maps, with their common transposes. Multiplication of ramification exponents remains explicit in assembly step 5. |
| 11-15 | lem-sf-ramified-reduction-comparison-square | Derived quotient balancing, all five quotient comparisons, mate-pasted mixed squares, finite-Tor dualizing and dual-input typing, evaluation and double-dual compatibility. |
| 16-17 | lem-sf-finite-free-etale-proetale-transport | Actual-map transport through the canonical site comparisons, no ambient pro-etale adjunction, etale quotient recovery and faithfulness descent. |
| 18 | lem-sf-finite-free-comparison-isomorphism-naturality and elementary final assembly | Scheme/base isomorphism reindexing and unique counit-compatible right-adjoint transport; Frobenius with base automorphism. The directed-tail proof of cofinality is still written in assembly step 8. |

The seven tasks correspond to separate arguments of comparable work (roughly 1300-2500 characters of the returned proof each); none restates the entire item. Existing results handle the arithmetic and Hom portions instead of spawning duplicates. A future worker has both a self-contained statement with the normalization equations and the unabridged argument below.

## Not duplicates

- lem-sf-finite-free-derived-scalar-calculus vs def-sfb-derived-extend-levelwise-adjunction: the latter states the derived scalar adjunction in condensed module-object notation, not the constant finite-coefficient sheaf calculus, conservative restriction, unchanged Tor interval and constructible realization asserted here.
- lem-sf-finite-free-derived-scalar-calculus vs lem-sfb-ind-finite-free-scalar-model: that theorem constructs an ind-finite-free termwise scalar model; it does not give this two-site constructibility and Tor-window assertion or the scalar/restriction tensor adjunction.
- lem-sf-finite-free-derived-scalar-calculus vs lem-sf-ringed-finite-free-tensor-complex: that node states the ordinary tensor chain isomorphism and preservation of K-flatness only, not the exact derived scalar adjunction and constructibility statement.
- lem-sf-finite-free-image-comparison vs lem-coef-finite-direct-image: the existing theorem assumes bounded constructible finite-Tor input. The new task states the unbounded finite-free case, the restriction comparison and the precise basis-coordinate normalization, and the compact-support result for a fixed compactification.
- lem-sf-finite-free-image-comparison vs lem-pur-finite-free-compact-composition: that theorem assumes the current item as a statement dependency and proves compatibility with composition/refinements; it cannot supply the unbounded image calculation here without a cycle.
- lem-sf-finite-free-image-comparison vs lem-coef-finite-free-compact-composition: it assumes the current item and concerns geometric composition in coherent systems, whereas this task is the unbounded single-morphism finite-free calculation.
- lem-sf-finite-free-image-comparison vs lem-finite-compact-support-scalar-transport: that theorem identifies an intrinsic/pro-etale transpose with a transported etale comparison on bounded-below origin witnesses, not the ordinary unbounded finite-free finite-sum construction.
- lem-sf-finite-free-exceptional-mate vs lem-coef-finite-closed-shriek: the existing theorem concerns constructible finite-Tor closed-immersion functors for coefficient stages. The new task treats arbitrary specified additive adjunctions on unbounded module derived categories, including compact-support right adjoints, and states the six-bijection and finite-sum normalization.
- lem-sf-finite-free-exceptional-mate vs lem-trf-adjoint-mate: uniqueness between right adjoints to isomorphic left functors does not prove invertibility of a coefficient mate with non-equivalence vertical scalar functors. The new statement requires and exploits the finite-free restriction coordinates.
- lem-sf-finite-free-comparison-transitivity vs lem-sf-constructible-exceptional-coefficient-coherence: that theorem assumes a normalized CoefficientConstruction already containing invertible comparisons and concerns its restricted multi-stage compact-support/exceptional functors. This task identifies the ordinary ambient finite-free projection, dualizing, Hom and Verdier comparisons for arbitrary unbounded inputs.
- lem-sf-finite-free-comparison-transitivity vs lem-sfb-flat-scalar-tower-coherence: scalar associativity is the endpoint identification here, not the equality of the five derived counit/evaluation maps.
- lem-sf-finite-free-comparison-transitivity vs lem-coef-finite-direct-image: its coefficient-chain clause covers the direct-image component under bounded constructible finite-Tor hypotheses, not the five ambient unbounded finite-free maps.
- lem-sf-ramified-reduction-comparison-square vs lem-coef-finite-closed-shriek: that pro-etale theorem contains successive-stage compatibility for one functor, not the simultaneous ordinary etale five-map mixed square, quotient dualizing/Hom normalization and dual-input typing.
- lem-sf-ramified-reduction-comparison-square vs thm-coef-finite-hom: it covers quotient chains inside a single coefficient field, not a mixed square with ramified horizontal extension.
- lem-sf-ramified-reduction-comparison-square vs cor-coef-finite-verdier: that theorem gives a same-field quotient cocycle and duality compatibility; it does not give this mixed four-ring equation.
- lem-sf-ramified-reduction-comparison-square vs lem-sfb-scalar-hom-chain-coefficient-coherence: that theorem gives equations of ordinary product Hom complexes, not the derived finite-stage geometric comparisons and dualizing inputs.
- lem-sf-finite-free-etale-proetale-transport vs lem-weil-finite-duality-site-comparison: that theorem identifies objects, evaluation and double-dual morphisms at one fixed coefficient stage; this task identifies all five actual coefficient-change maps across two stages and their mixed reduction diagrams.
- lem-sf-finite-free-etale-proetale-transport vs lem-coef-finite-etale-descent: that existing theorem recovers the closed-exceptional quotient component only; this task includes coefficient extension and the other four map identifications, with no unrestricted pro-etale adjunction.
- lem-sf-finite-free-etale-proetale-transport vs lem-pur-exceptional-mate-site-comparison: that theorem compares mates of geometric compact-support base change in a Cartesian scheme square; this task concerns finite-free coefficient-change and quotient squares.
- lem-sf-finite-free-comparison-isomorphism-naturality vs lem-weil-isomorphism-comparison-scalar-extension: that theorem compares two completed integral pullback/scalar maps, not the five finite-coefficient projection/counit/evaluation maps.
- lem-sf-finite-free-comparison-isomorphism-naturality vs lem-pur-isomorphism-inverse-image-tensor-hom: that theorem is an underived pro-etale tensor/Hom transport statement; this task includes derived images, exceptional counits and dualizing maps with scheme and base transported together.
- lem-sf-finite-free-comparison-isomorphism-naturality vs lem-pod-derived-automorphism-hom-evaluation: that theorem identifies the one-stage derived Hom pullback transpose; this task concerns coefficient-change naturality for all five operations and transported adjunction counits.

I searched the whole DAG by finite-free, coefficient extension/reduction, scalar adjunctions, evaluation, mate, and scheme-isomorphism concepts; searched blueprint_refs for finite free, finite-free, coefficient extension, mate, double-dual, restriction of scalars, coefficient reduction and scheme isomorphism; and read the nearby statements listed above. The only matching blueprint entry for the complete coefficient statement is the item itself. Existing nodes with integral or condensed coefficients, or which assume this item, were not silently identified with these finite ordinary coefficient categories.

## Review by Q33

I read the full returned item, its 18 steps, the current sk-thm-sf-compatibility unit (clause 7) and sec-six-functors chapter, the master source lem-coef-finite-free-extension.md, and the corresponding main-20261015 proof file under sec-smooth-purity/sk-lem-sp-tower. The main proof has the same three paragraphs: finite freeness and image functors; evaluation-defined internal Hom and Verdier; and coefficient coherence, scheme-isomorphism transport and cofinality. The seven new source fields name which sentences they make precise. These are agent-written extracted arguments, not claims that the blueprint separately states the auxiliary lemmas. The short assembly stays within that route. The unit is not itself this item and its realized fields are not changed.

For the arithmetic portion I opened the statement and proof of lem-sfb-local-field-integral-basis and the extending-absolute-value and DVR statements. The absolute value is normalized to extend the Q_l value, so its restriction really agrees on E; a uniformizer of E is a nonzero element of positive valuation in L. The DVR factorization therefore has positive exponent, and reducing a single integral basis gives exactly the ramified levels en. The old completeness proof invokes Stacks 031D, algebra.tex label lemma-finite-over-complete-ring: I read its three hypotheses (complete R, separated M, finite M/IM), as well as the old norm-ball verification preserved below. I have not replaced this route by an unsupported assumption that equal numerical levels agree. The existing basis theorem makes an additional arithmetic task a duplicate.

For the scalar task I read sites-modules.tex Tag 03CZ, label lemma-adjointness-tensor-restrict, and the exact/termwise adjunction nodes used by returned step 3. The new statement explicitly includes the derived adjunction, exactness and conservative restriction, the two inverse balancing maps and the K-flat condition used to preserve the Tor interval. Its constructibility clause uses finite coefficient rings and a Noetherian scheme, so a finite local system stays finite on the same finite stratification. Tor testing is against ALL degree-zero B-module sheaves, restricted exactly to A, not only constant modules. For the image task I read derived.tex Tag 08BJ, label lemma-adjoint-preserve-K-injectives: its right adjoint must have an exact left adjoint. That hypothesis is provided by finite-free scalar extension. I checked the new task states the actual counit-defined projection map and its j-th basis component, and states the open zero/off-open formula used in compact support. The proper/open argument is not hidden in the item.

For the mate task I checked all six Hom groups and their coefficient/site endpoints. Its left comparison is explicitly invertible and normalized after restriction; an arbitrary invertible square does NOT have an invertible mate. The finite-free sum coordinates and conservative U are the extra reason here. Its concluding counit equation is precisely the one needed in assembly step 3. F_A= i_* and F_A=Ra_X! have the ordinary etale right adjoints stated by lem-exc-closed-ambient and thm-amb-etale-exceptional-adjoint. The latter permits finite commutative rings and a compactification between Noetherian schemes, not a pro-etale ambient adjunction. Noetherian and compactifiable conditions hold for the separated finite-type schemes over the field; the original Nagata and finite-type checks remain preserved in the image task allocation.

Assembly step 4 uses the exact statement of lem-sf-ringed-finite-free-hom-base-change, which I opened: it applies to arbitrary unbounded P,Q on a small site and specifies the transpose of extended evaluation, with no perfectness assumption. I also read its source place in sites-cohomology.tex Tag 08J9, lemma-internal-hom. It already contains the tensor-Hom assertion needed in returned steps 7-8, so I created no new Hom node. The statement of lem-weil-duality-pairing says evaluation transposes to delta, without assuming biduality. Composing its evaluation with u and transposing once more gives exactly the displayed beta_D T(delta)=D(beta) delta equation; both sides land in D_B(TD_AK). This short assembly is retained explicitly.

The tower task states the actual common transposes, rather than only existence of functor isomorphisms. I checked the source/target of the exceptional transpose F_C(TG_A M) -> T F_A G_A M -> T M, and that the intermediate unit/counit cancels by the triangle identity. For the internal-Hom component, tensor reassociation identifies the two evaluations before transposition. The mixed-square task retains B_n tensor^L A_m=B_m and the nonflat quotient maps; it does not infer flatness of A_m/A_n. I opened the statements of all five existing quotient comparisons and lem-weil-verdier-preservation-strata: dualizing objects are duals of the rank-one constant objects, and all dual inputs are finite-Tor constructible. I checked the mixed task states both input Hom extension, the exceptional-counit recovery and the evaluation/double-dual clauses. These are separate work from the finite-free tower task, because the vertical quotients need not be flat.

For the site task I opened lem-weil-pbc-comparison-direct-image-canonical-mate, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-weil-finite-duality-site-comparison and lem-coef-finite-etale-descent. The first supplies the normalized direct-image counit comparison on bounded-below inputs, not arbitrary unbounded ones; the new task accordingly restricts to bounded finite-Tor constructible inputs. The duality site comparison requires first input finite-Tor and second bounded constructible, including omega; that typing is retained. The etale descent theorem supplies BOTH finite-Tor outputs, the exact pulled-back closed-counit map, and faithfulness to descend equality. It is applied separately at (n,m) over E and (en,em) over L. The pro-etale exceptional functor is transported and no global pro-etale adjunction is assumed.

For the last task I read lem-trf-adjoint-mate and the nearby isomorphism tensor/Hom and integral scalar statements. They do not state the simultaneous finite-coefficient image/counit/evaluation transport, so the new task gives that assertion with the base isomorphism present. Its semilinear Frobenius is id times Spec(gamma), where gamma has an inverse, not absolute Frobenius of an arbitrary scheme. The final cofinality argument is still explicit in the parent: n=m works because e>=1, and the qualifying n form a directed tail.

Citations were checked against the statement of EACH node used by each assembly step: step 1 takes unique extending absolute values, DVR uniformizer factorization and the integral basis; step 2 takes the scalar task; step 3 takes the image and mate tasks plus the two named adjunction existence statements; step 4 takes the evaluation-defined finite-free Hom theorem and the double-dual transpose definition; step 5 takes the five-map tower equations; step 6 takes the five mixed-square equations and their typing; step 7 takes the actual-map site transport and etale recovery; step 8 takes isomorphism transport and writes cofinality itself. citations.json records the complete verbatim statements, so it cannot disguise a missing hypothesis with an unrelated short quotation. The nonexistent generic reference def-weil-pbc-adjunction in an early draft of the new mate statement was corrected to the explicit natural-bijection and triangle-identity definition.

I checked B-E with the JSON and sources open. Every new task introduces its objects and maps, has statement dependencies for all bracketed notions, proof=[], proof_deps=[], proof_origin=null and status unsplit. There is no parent dependency in a new statement, and the comparison nodes that themselves depend on the item are excluded as proof tools. I checked small cases: identity E=L and e=1, n=m, m=1, totally ramified degree-two extensions (B_n/A_n still has the reduced integral basis), empty schemes and zero input complexes. The exact scalar and image arguments also permit a rank-zero finite-free algebra, where all B-objects and the finite sums are zero. The generic mate statement keeps its normalizations for rank zero. The double-dual identity does not require delta to be invertible. No new statement introduces a false perfectness, dimension, smoothness or unramifiedness condition.

Mathlib results were read from the actual saved answers in both semantic phrasings. ModuleCat.extendRestrictScalarsAdj is an ordinary module adjunction, not the two-site derived constructibility/Tor theorem. CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive (AdditiveFunctor.lean:203) and mapBiproduct are the matrix ingredient, not the named coefficient projection comparison. Adjunction.rightAdjointUniq and rightAdjointUniq_hom_counit (Unique.lean:102,136) compare adjoints in the same categories; they do not make a general scalar mate invertible. conjugateEquiv and the pasting laws are foundational infrastructure, already represented in the DAG, not the five normalized coefficient equations. The other semantic hits concern condensed modules, ordinary scheme O_X-modules, adic evaluation or algebraic etaleness; none states one of the seven full tasks or specializes to it in one line. No service failure was recorded as absence.

## What remains

The seven new tasks intentionally remain statement-only for other workers to split in parallel. No required part of this stage-1 decomposition is intentionally omitted. The delivery and server-check results are recorded after the tool exits.

## Returned argument, verbatim (handoff material, not proof fields of new nodes)

### Returned step 1 — Existing valuation and integral-basis statements; assembly step 1

The restriction of $|\cdot|_L$ to $E$ equals $|\cdot|_E$ by uniqueness [lem-weil-l-adic-extension-absolute-value]; hence $\mathcal O_E=E\cap\mathcal O_L$ and $0<|\varpi_E|_L<1$. Apply the uniformizer factorization in [lem-weil-l-adic-extension-integers-dvr] in $L$: $\varpi_E=u\varpi_L^e$ for a unit $u$ and a positive integer $e$, the ramification index. Consequently $\varpi_E^n\mathcal O_L=\varpi_L^{en}\mathcal O_L$ for all $n$. The quotient $\mathcal O_L/\varpi_E\mathcal O_L$ is finite by [lem-weil-valued-dvr-finite-quotients] at exponent $e$ in $L$. It is therefore a finitely generated module over $\mathcal O_E/\varpi_E$: the images of all its finitely many elements are a generating set.

Original uses: lem-weil-l-adic-extension-absolute-value, lem-weil-l-adic-extension-integers-dvr, lem-weil-valued-dvr-finite-quotients.
Original source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-free-extension.md; Proof.

### Returned step 2 — Existing integral-basis statement; alternative complete-ring proof retained

The ring $R=\mathcal O_E$ is $(\varpi_E)$-adically complete. Indeed, for a compatible sequence of residues choose lifts $x_n\in R$; then $x_{n+1}-x_n\in\varpi_E^nR$, so $(x_n)$ is Cauchy and converges by [lem-weil-l-adic-extension-complete]. Its limit is in $R$ and has the prescribed residues because $\varpi_E^nR=\{x:|x|_E\le |\varpi_E|_E^n\}$ is closed. The intersection of these balls is zero, so the lift is unique, proving the definition [def-weil-pbc-adically-complete-ring]. If $y\in\bigcap_n\varpi_E^n\mathcal O_L$, then $|y|_L\le |\varpi_E|_L^n$ for every $n$. Since $0<|\varpi_E|_L<1$, this forces $|y|_L=0$, hence $y=0$. Apply [lem-weil-pbc-finite-over-complete-ring] to $R$, $I=(\varpi_E)$ and $M=\mathcal O_L$ using the finite residue module of step 1. Thus $\mathcal O_L$ is finite over $R$. It is torsion-free since it is a subring of the field $L$ and $R\hookrightarrow L$ is injective; $R$ is a DVR by [lem-weil-l-adic-extension-integers-dvr]. Hence [lem-sc-dvr-fg-torsionfree-free] gives an $R$-basis $b_1,\ldots,b_r$ of $\mathcal O_L$. Reducing this basis gives $B\cong A^{\oplus r}$ as $A$-modules.

Original uses: lem-weil-l-adic-extension-complete, def-weil-pbc-adically-complete-ring, lem-weil-pbc-finite-over-complete-ring, lem-weil-l-adic-extension-integers-dvr, lem-sc-dvr-fg-torsionfree-free.
Original source: literature/stacks-project/algebra.tex; Tag 031D, lemma-finite-over-complete-ring; application after the explicit completeness check.

### Returned step 3 — lem-sf-finite-free-derived-scalar-calculus

On either coefficient site write $T_W=-\otimes_A B_W$ and $U_W$ for restriction of scalars [def-pc-sheaf-restrict-scalars]. Apply [lem-weil-pbc-ringed-topoi-module-adjunction] to the identity topos and $A_W\to B_W$: $T_W\dashv U_W$. By [lem-pur-change-of-rings-tensor-comparison] and the basis in step 2, $U_WT_WN\cong N^{\oplus r}$. Thus $T_W$ is exact; $U_W$ is exact and reflects zero objects because it leaves the underlying abelian sheaf unchanged. The exact functors descend termwise by [lem-weil-pbc-exact-functor-derived-factorization]. The termwise unit and counit of [lem-weil-pbc-termwise-adjunction-homotopy] descend as well and retain their triangle identities, so $T_W\dashv U_W$ also on derived categories, and $U_W$ reflects isomorphisms (apply it to the cohomology of a cone). The exact derived $T_W$ is the derived change of rings of [lem-pur-derived-change-of-rings]. Tensor extension preserves bounded constructibility: it is exact, and on each stratum a finite locally constant $A$-module becomes a finite locally constant $B$-module. It preserves any Tor interval $[a,b]$ because $(T_WK)\otimes_B^L N\cong K\otimes_A^L U_WN$, on K-flat tensor complexes [lem-weil-pbc-site-derived-tensor-descent]: the balanced maps are $(p\otimes b)\otimes n\mapsto p\otimes bn$ and $p\otimes n\mapsto(p\otimes1)\otimes n$. They are inverse chain maps; extension of a K-flat $A$-complex is K-flat over $B$, since this formula identifies its tensor with an acyclic $B$-complex with tensor against that complex restricted to $A$, which is acyclic because $U$ is exact.

Original uses: def-pc-sheaf-restrict-scalars, lem-weil-pbc-ringed-topoi-module-adjunction, lem-pur-change-of-rings-tensor-comparison, lem-weil-pbc-exact-functor-derived-factorization, lem-weil-pbc-termwise-adjunction-homotopy, lem-pur-derived-change-of-rings, lem-weil-pbc-site-derived-tensor-descent, def-weil-pbc-constructible-complexes, def-weil-finite-torsion-constructibility, def-weil-finite-tor-amplitude.
Original source: literature/stacks-project/sites-modules.tex; Tag 03CZ, lemma-adjointness-tensor-restrict; exact finite-free specialization and passage to complexes.

### Returned step 4 — lem-sf-finite-free-image-comparison

First work etale. For a $B$-complex $N$ the canonical comparison $U_XRf_{*,B}N\cong Rf_{*,A}U_TN$ is [lem-sbc-canonical-restrict-scalars-functor-comparisons] on bounded-below objects. For a finite-free extension the same comparison is available on unbounded objects directly: a $B$-K-injective resolution remains $A$-K-injective by [lem-weil-pbc-right-adjoint-preserves-kinjective], since $T_T$ is exact, and direct image commutes sectionwise with $U$. Under this identification the underlying map of the projection comparison $c_f:T_XRf_{*,A}K\to Rf_{*,B}T_TK$ [def-kun-projection-formula-map] is the finite-sum comparison $(Rf_{*,A}K)^{\oplus r}\to Rf_{*,A}(K^{\oplus r})$. To verify the map, precompose with its $j$-th summand: the projection map is adjoint to the inverse-image counit, and the component is $Rf_*$ applied to the inclusion $k\mapsto k\otimes b_j$; these are exactly the finite-sum inclusions. Any additive functor $F$ preserves this finite sum explicitly: applying $F$ to projections $p_j$ and inclusions $s_j$ preserves $p_js_h=\delta_{jh}$ and $\sum_js_jp_j=1$, giving inverse comparison matrices. Apply this to $Rf_{*,A}$. Thus $U_Xc_f$, and hence $c_f$, is invertible. This proves the first displayed comparison without any cohomological-dimension hypothesis.

Original uses: lem-sbc-canonical-restrict-scalars-functor-comparisons, lem-weil-pbc-right-adjoint-preserves-kinjective, def-kun-projection-formula-map.
Original source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-free-extension.md; Proof, first paragraph: finite-free direct-image case (with the finite-sum calculation written out).

### Returned step 5 — lem-sf-finite-free-image-comparison

For compact supports, factor the chosen morphism as an open immersion followed by a proper morphism. A separated finite-type morphism between our schemes is compactifiable by [thm-nagata-compactification], and the schemes in the compactification are Noetherian by [lem-weil-pbc-finite-type-over-noetherian]: a field has only the zero and unit ideals, so $\operatorname{Spec}k$ is Noetherian, and each scheme here is finite type over it. For a fixed $f:T\xrightarrow{j}\overline T\xrightarrow{p}X$ with $\overline T$ finite type over $X$, the etale functor is $F_A=Rp_{*,A}j_!$ [def-amb-etale-compact-support]. Extension by zero commutes with coefficient extension and restriction: off the open its stalk is zero, and on the open it is the given stalk [lem-weil-pbc-extension-by-zero-stalks, lemma-weil-pbc-geometric-stalk-conservative]; the comparison is the map induced by $m\otimes b\mapsto m\otimes b$. Combining this with step 4 for $p$ gives $c^!_f:T_XF_A\xrightarrow{\sim}F_BT_T$, natural in all objects. After restriction it is the finite-sum comparison, whose components are $F_A$ of the inclusions $m\mapsto m\otimes b_j$. This construction also applies to the structure morphism $a_X$.

Original uses: thm-nagata-compactification, lem-weil-pbc-finite-type-over-noetherian, def-amb-etale-compact-support, lem-weil-pbc-extension-by-zero-stalks, lemma-weil-pbc-geometric-stalk-conservative.
Original source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-free-extension.md; Proof, first paragraph: counit-defined dualizing comparison; compact-support finite-free calculation.

### Returned step 6 — lem-sf-finite-free-exceptional-mate

Apply extension and restriction of scalars to the two exceptional adjunctions. Let $F_A\dashv G_A$ and $F_B\dashv G_B$ be either $i_*\dashv Ri^!$ [lem-exc-closed-ambient], or $Ra_{X!}\dashv a_X^{\times}$ [thm-amb-etale-exceptional-adjoint]. Their left functors have the comparison $c:T F_A\xrightarrow{\sim}F_BT$ of steps 4 and 5 (for $i_*$ use its derived direct image). For a $B$-object $N$ and an $A$-test object $P$, the successive adjunctions give
$$\operatorname{Hom}_A(P,UG_BN)=\operatorname{Hom}_B(TP,G_BN)=\operatorname{Hom}_B(F_BTP,N)=\operatorname{Hom}_B(TF_AP,N)=\operatorname{Hom}_A(F_AP,UN)=\operatorname{Hom}_A(P,G_AUN).$$
The bijections are natural in $P,N$; they therefore identify $UG_BN$ with $G_AUN$: evaluate the bijection and its inverse at identity maps to obtain inverse morphisms. Define $b_M:TG_AM\to G_BTM$ to be adjoint to $(T\varepsilon_{A,M})c_{G_AM}^{-1}$. Under the preceding identification and $UTM=M^{\oplus r}$, $Ub_M$ is the map $(G_AM)^{\oplus r}\to G_A(M^{\oplus r})$ whose $j$-th component is $G_A$ of the $j$-th inclusion; this follows by transposing that component, which gives precisely $\varepsilon_{A,M}$ followed by that inclusion. The finite-sum matrix calculation of step 4 makes this an isomorphism. Since $U$ reflects isomorphisms, $b_M$ is an isomorphism. The two choices of $F,G$ give the closed-exceptional comparison and, at $M=A_s$, the dualizing comparison $u:T\omega_{X,A}\xrightarrow{\sim}\omega_{X,B}$. By definition they obey $\varepsilon_{B,TM}F_B(b_M)=(T\varepsilon_{A,M})c_{G_AM}^{-1}$, which is the required counit identity.

Original uses: lem-exc-closed-ambient, thm-amb-etale-exceptional-adjoint.
Original source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-free-extension.md; Proof, first paragraph: exceptional and dualizing maps defined by their counits; explicit finite-free adjunction argument.

### Returned step 7 — Existing finite-free Hom theorem; assembly step 4

The derived tensor--Hom adjunction is the composite $$\operatorname{Hom}(L,H_A(K,N))\cong H^0(\mathcal C,H_A(L,H_A(K,N)))\cong H^0(\mathcal C,H_A(L\otimes_A^LK,N))\cong\operatorname{Hom}(L\otimes_A^LK,N),$$ using [lem-pur-rhom-global-sections] and [lem-weil-pbc-ringed-internal-hom-exact-restriction]. Its counit is evaluation, so the comparison $v_{K,M}$ is the transpose of scalar-extended evaluation pairing.

Original uses: lem-pur-rhom-global-sections, lem-weil-pbc-ringed-internal-hom-exact-restriction.
Original source: literature/stacks-project/derived.tex; Tag 08BJ, lemma-adjoint-preserve-K-injectives; combined with sites-modules Tag 03CZ and the displayed Hom-complex calculation.

### Returned step 8 — Existing finite-free Hom theorem; assembly step 4

For the finite-free constant ring extension of step 2, [lem-sf-ringed-finite-free-hom-base-change] gives an isomorphism $$T H_A(K,M)\xrightarrow{\sim}H_B(TK,TM)$$ whose defining transpose is exactly the evaluation pairing from the preceding step. Therefore this isomorphism is the map $v_{K,M}$, and it requires no perfectness hypothesis on $K$.

Original uses: lem-sf-ringed-finite-free-hom-base-change, lem-pur-derived-change-of-rings.
Original source: literature/stacks-project/derived.tex; Tag 08BJ, lemma-adjoint-preserve-K-injectives; combined with sites-modules Tag 03CZ and the displayed Hom-complex calculation.

### Returned step 9 — Explicit duality assembly step 4

Define $\beta_K$ as $v_{K,\omega_{X,A}}$ followed by $R\mathcal Hom_B(TK,u)$. Steps 6 and 8 make it an isomorphism $TD_{X,A}K\to D_{X,B}TK$. Its evaluation identity is
$$u\,T(\mathrm{ev}_{A,K})=\mathrm{ev}_{B,TK}(\beta_K\otimes1),$$
where tensor reassociation is understood. Indeed, both sides send a functional tensored with $k$ and coefficient $b$ to its value multiplied by $b$, followed by $u$; this is exactly the defining transposition in step 7. The double-dual map is the transpose of evaluation [lem-weil-duality-pairing], so transposing this identity once more gives
$$\beta_{D_AK}\,T(\delta_{A,K})=D_B(\beta_K)\,\delta_{B,TK}.$$
This is the double-dual compatibility (both sides land in $D_B(TD_AK)$). In particular, it does not presume biduality in order to prove compatibility.

Original uses: lem-weil-duality-pairing.
Original source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-free-extension.md; Proof, second and third paragraphs: evaluation and the double-dual transpose.

### Returned step 10 — lem-sf-finite-free-comparison-transitivity

The basis was used only to test invertibility. All five maps were defined before choosing a basis by projection, counit or evaluation. For $E\subset L\subset H$, put $d=e(H/L)$ and $C=\mathcal O_H/\varpi_E^n\mathcal O_H=A_{H,den}$. The factorization $\varpi_E=u\varpi_L^e$ and $\varpi_L=v\varpi_H^d$ gives $\varpi_E=uv^e\varpi_H^{de}$ with a unit coefficient, so the iterated coefficient stage is exactly $C$. Compare the maps for $A\to B\to C$ with that for $A\to C$, using $(K\otimes_A B)\otimes_B C\cong K\otimes_A C$. This reassociation and its action on morphisms can be checked on K-flat tensor complexes [lem-weil-pbc-site-derived-tensor-descent]. For direct image, under the inverse-image adjunction both composite maps have transpose $f^*Rf_*K\otimes_A C\to K\otimes_A C$, the inverse-image counit tensored with $C$. For exceptional and dualizing maps, their transposes are respectively $F_C(T_{A,C}G_AM)\xrightarrow{(c_{A,C})^{-1}}T_{A,C}F_AG_AM\xrightarrow{T_{A,C}\varepsilon_A}T_{A,C}M$; expanding either composite gives this formula, since the intermediate $F_B\dashv G_B$ unit followed by counit cancels by its triangle identity. For internal Hom the transpose of either composite is $T_{A,C}(\mathrm{ev}_A)$ after tensor reassociation. Adjunction is a bijection on morphisms, so equality of these displayed transposes proves each composition law, and composition proves the Verdier law. For the identity extension the same transposes are the original counit/evaluation, giving the identity comparisons.

Original uses: lem-weil-pbc-site-derived-tensor-descent.
Original source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-free-extension.md; Proof, third paragraph: transposes for identity and successive field extensions.

### Returned step 11 — lem-sf-ramified-reduction-comparison-square

Write $A_n=A_{E,n}$, $B_n=A_{L,en}$ and similarly $A_m,B_m$, with $1\le m\le n$. Since $B_n$ is free over $A_n$ by step 2, $$B_n\otimes^L_{A_n}A_m=B_n/\varpi_E^mB_n=B_m.$$ The K-flat reassociation of [lem-weil-pbc-site-derived-tensor-descent] identifies both iterated scalar extensions in the reduction square with tensoring directly to $B_m$; the balanced map is $(p\otimes a)\otimes b\mapsto p\otimes ab$.

Original uses: lem-weil-pbc-site-derived-tensor-descent.
Original source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-free-extension.md; Proof, third paragraph: quotient followed by extension, with the actual coefficient square and transposes.

### Returned step 12 — lem-sf-ramified-reduction-comparison-square

Apply [lem-coef-finite-direct-image], [lem-coef-finite-closed-shriek], [lem-coef-finite-dualizing], [thm-coef-finite-hom] and [cor-coef-finite-verdier] to the same-field quotient maps $(A_n\to A_m)$ and $(B_n\to B_m)$. Step 3 supplies finite-Tor constructibility after extension to $B_n$, and $en\ge em\ge1$, so all five comparisons have the required inputs and outputs. The closed-exceptional comparison is first obtained on the pro-etale realization.

Original uses: lem-coef-finite-direct-image, lem-coef-finite-closed-shriek, lem-coef-finite-dualizing, thm-coef-finite-hom, cor-coef-finite-verdier.
Original source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-free-extension.md; Proof, third paragraph: quotient followed by extension, with the actual coefficient square and transposes.

### Returned step 13 — lem-sf-ramified-reduction-comparison-square

The coefficient-reduction squares for direct image, closed exceptional image, and the dualizing object commute by the mate-pasting identities [lem-weil-pbc-mate-pasting]. Their mates are respectively the direct-image counit, the exceptional counit, and the compact-support counit tensored to $B_m$; intermediate unit/counit pairs cancel by the triangle identities. The finite-Tor hypotheses for dualizing inputs are supplied by [lem-weil-verdier-preservation-strata].

Original uses: lem-weil-pbc-mate-pasting, lem-coef-finite-dualizing, lem-weil-verdier-preservation-strata.
Original source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-free-extension.md; Proof, third paragraph: quotient followed by extension, with the actual coefficient square and transposes.

### Returned step 14 — lem-sf-ramified-reduction-comparison-square

The constant rank-one complexes $A_X$ and $B_X$ are finite-Tor constructible, and their duals are $\omega_{X,A}$ and $\omega_{X,B}$. Hence [lem-weil-verdier-preservation-strata] gives finite-Tor constructibility for these dualizing objects and every dual input in the quotient comparisons.

Original uses: lem-weil-verdier-preservation-strata.
Original source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-free-extension.md; Proof, third paragraph: quotient followed by extension, with the actual coefficient square and transposes.

### Returned step 15 — lem-sf-ramified-reduction-comparison-square

For internal Hom use [lem-weil-pbc-mate-pasting] on the tensor–Hom adjunction from step 7. Tensor reassociation identifies the pasted left squares; both right mates have transpose evaluation tensored to $B_m$. [thm-coef-finite-hom] identifies the quotient maps with precisely these evaluation transposes at $(n,m)$ over $E$ and $(en,em)$ over $L$. Thus the internal-Hom reduction square commutes. Composing it with the dualizing square gives the Verdier square [cor-coef-finite-verdier]. The evaluation identity and its double-dual transpose from step 9 persist after derived tensor; [lem-weil-verdier-preservation-strata] verifies finite-Tor constructibility for the dual inputs in these quotient comparisons.

Original uses: lem-weil-pbc-mate-pasting, thm-coef-finite-hom, cor-coef-finite-verdier, lem-weil-verdier-preservation-strata.
Original source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-free-extension.md; Proof, third paragraph: quotient followed by extension, with the actual coefficient square and transposes.

### Returned step 16 — lem-sf-finite-free-etale-proetale-transport

These comparisons give the finite-coefficient pro-étale assertions. Direct image commutes with comparison pullback by [lem-weil-pbc-comparison-direct-image-canonical-mate]: $f$ is qcqs and its input bounded below. Tensor pullback commutes with derived tensor by [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. The exceptional functor is the transported étale functor [def-weil-exceptional-inverse-image]. The dualizing and internal-Hom identifications, including evaluation and double-dual, are [lem-weil-finite-duality-site-comparison] at each finite coefficient stage: its first input is finite-Tor, its second bounded constructible, including the dualizing objects established above.
To identify the maps, paste the site-comparison and coefficient squares using [lem-weil-pbc-mate-pasting]. The canonical-mate counit normalization identifies the pulled-back inverse-image counit with the pro-étale counit. After tensor comparison the pulled-back projection transpose is therefore that counit tensored with $B$. For internal Hom the transpose is pulled-back evaluation; for the exceptional map it is the transported étale exceptional counit. Consequently these are the named coefficient maps on the pro-étale realization, and the functor carries all previously proved map identities to it.

Original uses: lem-weil-pbc-comparison-direct-image-canonical-mate, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, def-weil-exceptional-inverse-image, lem-weil-finite-duality-site-comparison, lem-weil-pbc-mate-pasting.
Original source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-free-extension.md; Proof, all paragraphs: finite constructible realization on the two sites.

### Returned step 17 — lem-sf-finite-free-etale-proetale-transport

The remaining recovery of the étale closed-exceptional quotient map is [lem-coef-finite-etale-descent], applied over $E$ at $(n,m)$ and over $L$ at $(en,em)$. Its input is finite-Tor constructible on the étale site by the hypotheses and step 3. It places both étale outputs in the same finite-Tor constructible category and identifies its pulled-back counit-defined map with [lem-coef-finite-closed-shriek]. Its faithfulness clause then descends the pro-étale mixed reduction square just proved. Thus this use of the pro-étale closed coefficient theorem recovers exactly the étale map and square, with their required output typing.

Original uses: lem-coef-finite-etale-descent, lem-coef-finite-closed-shriek.
Original source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-free-extension.md; Proof, all paragraphs: finite constructible realization on the two sites.

### Returned step 18 — lem-sf-finite-free-comparison-isomorphism-naturality; elementary cofinality in assembly step 8

Finally, transport a diagram along scheme isomorphisms (and the base isomorphism when present). The induced site equivalences identify module sheaves by inverse reindexing; their inverse transports are actual inverses up to the canonical pullback identifications. The formula for tensor, scalar extension, the Hom differential, and evaluation is unchanged under this reindexing. Transport the left adjunction and its unit/counit as well. The transported right adjoint is the original right adjoint under the unique counit-compatible identification; after bringing both functors into the same categories this uniqueness is [lem-trf-adjoint-mate]. Consequently the transported comparison is the comparison on the transported diagram: both have exactly the projection-counit or evaluation transposes displayed in steps 4, 6, 7 and 9. This includes the semilinear Frobenius isomorphism of [def-weil-global-geometric-frobenius] because $\gamma$ is a field automorphism with inverse. Lastly $e\ge1$ and for every $m\ge1$ there is $n\ge1$ with $en\ge m$ (take $n=m$); the set of such $n$ is a nonempty tail and hence directed. Thus the indices $en$ are cofinal for the inverse tower. The ideal equality in step 1 identifies exactly those levels with $B_n$; changing either uniformizer by a unit does not change these ideals or quotient maps.

Original uses: lem-trf-adjoint-mate, def-weil-global-geometric-frobenius.
Original source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-free-extension.md; Proof, final paragraph: scheme-isomorphism naturality, Frobenius transport, and cofinal levels.

