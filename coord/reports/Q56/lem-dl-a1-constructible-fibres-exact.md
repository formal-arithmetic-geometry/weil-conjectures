# Worker report: Q56 / lem-dl-a1-constructible-fibres-exact

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-constructible-fibres-exact.json`: repaired split; statement and statement dependencies unchanged; 2507 characters of assembly proof.
- `dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-point-fibre-stage-exact.json`: statement; unsplit; no Mathlib match after two semantic phrasings, Loogle, source grep and LeanSearch.
- `dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-heart-connected-lisse-strata.json`: statement; unsplit; no Mathlib match after two semantic phrasings, Loogle, source grep and LeanSearch.
- `dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-finite-stage-fibre-vanishing.json`: statement; unsplit; no Mathlib match after two semantic phrasings, Loogle, source grep and LeanSearch.
- `dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-local-heart-cover-defects.json`: statement; unsplit; no Mathlib match after two semantic phrasings, Loogle, source grep and LeanSearch.
- `report.md` and `citations.json`: this review, the complete returned proof, the allocation map, and verbatim evidence for every assembly citation. Search outputs, `searches.jsonl`, `query-plan.json`, `returned-node.json` and the two repair scripts are sandbox research artifacts, not repository files.

## Attachments

None. The project search for the blueprint id and constructible-fibre notions found the landed `WeilConjectures.dlConstructibleFibresExact` in `lean/Sheaf/Paper/DlConstructibleFibresExact.lean:174`, whose proof ends with `sorry`. It is not an attachment. The declarations under `lean/WeilConjectures/` about constructible hearts and the two-colimit t-structure do not state all the specified fibre, Weil and locality assertions. No Lean was written or compiled.

## WANTED

None: Bhatt–Scholze, the current blueprint, and the needed Stacks source files are present locally. No SGA source is used.

## What was wrong and what changed

The released stage-1 repair note of 2026-10-22 explicitly reopens the previously reviewed split and requires at least three independent new nodes, with the parent's proof at most 3000 characters. The sandbox initially had only dispatcher marker files, not a retained node, report, searches, or active delivery. I copied the live returned node, whose twelve steps match the return's lengths, and retained its source, citations, searches, blueprint references and all maintainer metadata. This is a mathematical re-split, not an unchanged re-push. The statement is unchanged; no STATEMENT-DISPUTED correction was necessary.

The new nodes have complete quantified statements and are all `unsplit`, with empty `proof` and `proof_deps` and null `proof_origin`. Their proof work is preserved below for the next workers. There are four tasks of distinct kinds: the specified point-sections functor and coefficient-stage calculus; the continuous realization and adapted strata; rank evaluation and finite-stage vanishing; and locally defined heart defects without a global field of definition. No node duplicates the whole parent or its full geometric exactness/conservativity/Weil/locality package.

I considered a separate immersion-exactness node and searched for it, but did not create it: `lem-sf-immersion-completed-pullback-comparison` and `lem-per-adic-stratified-pullback-texact` already supply the relevant results. The parent keeps the original immersion-specific argument with its original integral-category comparison and rational transport. This preserves the original proof route. Generic abelian-category reflection, images and fixed-pair kernel/cokernel constructions remain in the assembly rather than becoming new elementary nodes.

## Allocation of every returned argument

| Returned steps | Work assigned | Retained details |
| --- | --- | --- |
| 1–2 | Assembly step 1, using the existing immersion and integral-category nodes | Noetherian finite-type setting; arbitrary Spec k map reduced by a base automorphism; separated section is closed; completed versus exact inverse image; identification of the two integral categories; rationalization preserves the standard halves. |
| 3–4 | lem-dl-a1-point-fibre-stage-exact | Exact sections at Spec k; exact coefficient localization; finite-dimensionality; t-exact triangulated point functor; finite common-stage diagrams; H^0 representatives, cone kernels and cokernels; scalar-extension coherence and the actual Qbar fibre. |
| 5–6 | lem-dl-a1-heart-connected-lisse-strata | Integral-category bridge for J; continuous coefficients, not a discrete constant ring; exact scalar extension and standard halves; lisse realization of stratum restrictions; good refinement; reduced strata; finitely many open connected components; Nullstellensatz points; constant finite ranks. |
| 7–8 | lem-dl-a1-finite-stage-fibre-vanishing | Pullback/fibre identification for the actual point-section functor; a trivializing affine pro-etale cover of Spec k splits by the w-contractible criterion; sections have dimension equal to rank; rank-zero sheaves vanish; cover locality and the equivalence J; finite open–closed induction including the empty scheme. The faithful finite-to-Qbar vector-space scalar extension remains explicit in assembly step 2. |
| 9–10 | Assembly step 3, existing homology and reflection nodes | Kernel/cokernel test for isomorphisms, image test for zero arrows, and exact conservative-family reflection of short exactness. |
| 11 | Assembly step 4 | Frobenius preserves truncations; inverse structure maps give inverse actions on kernel and cokernel; forgetting is faithful and creates these two objects, so it is exact and reflects exactness. |
| 12 | lem-dl-a1-local-heart-cover-defects | Cartesian local-data abelianness and componentwise defects; finite affine subcover on each separated finite-type test open; comparison with continuous module sheaves; coefficient-field enlargement for finitely many zero restrictions; arbitrary non-quasi-compact total space, with no global field required. |

## Review by Q56

I read the current `p-dl-a1-exact.proof.md`, its unit and chapter, and the twelve returned steps. The current blueprint's Step 1 ends by reducing the obstruction to geometric stalks; Step 5 detects the zero connecting map. The repair supplies exactly this generic detection tool and leaves the weight-gap route intact. The parent is not the unit's key statement, so no unit realization fields are changed. The released keep-plan repair is honored: coefficient categories, point functor, statements and the sections/continuous-realization proof route are preserved.

For the literature I read Bhatt–Scholze §6.8: Lemma 6.8.2, Definition 6.8.3 (lisse is locally free of finite rank), Definition 6.8.6 (constructible after a finite stratification), Proposition 6.8.14(2) (raw integral rationalization identifies with rational constructible complexes), and Remark 6.8.15 (naive pullback for closed/etale immersions). The common-stage and standard-heart refinements are the project's explicit constructions, not claims that the paper states them in this notation. I also read Stacks 03PU, `etale-cohomology-theorem-exactness-stalks`, and kept its etale-only scope: it does not by itself give conservativity on arbitrary pro-etale sheaves. I read 04MF, `topology-lemma-locally-Noetherian-locally-connected`; 00FV, `algebra-theorem-nullstellensatz`; and 04TQ, `sites-lemma-glue-maps`. The source tags and labels are written in the applicable new source fields. The new nodes are the precise intermediate assertions extracted from the retained argument, with the entire argument recorded below, rather than proof sketches inside their statements.

Assembly step 1: I opened `lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-section-separated-closed-immersion`, `lem-sf-immersion-completed-pullback-comparison`, `lem-weil-pbc-integral-stratified-perfect-characterization`, and `prop-weil-pbc-rational-transport`. Respectively these give Noetherianity, closedness of a section of a separated map, ordinary exact inverse image with completed-pullback comparison and integral constructibility, agreement of the two precise integral categories, and extension of a supplied exact integral functor to raw rational coefficients. The characterization requires Noetherian finite dimension and invertible ell: all hold for the separated finite-type k-schemes and their strata, with ell different from p. The point-stage node states both t-exactness and exact finite-dimensional heart values for the specified sections functor. The self-embedding of the algebraic closure is an automorphism since each finite subfield is permuted; it is not assumed k-linear. This is why the immersion comparison is used, rather than an arbitrary-flatness assertion. Every non-elementary fact here is cited, including rational transport which I explicitly restored to the shortened assembly.

Assembly step 2: I checked the actual new statements: the point-stage node supplies finite-stage heart representatives and its Qbar fibre identification; the strata node starts with the same raw rational category as the parent and identifies it with the source of J, then supplies degree-zero lisse restrictions and good finite strata; the vanishing node states rank evaluation using the same sections fibre and the finite-stage conclusion F=0. They do not merely refer to one another's proofs. A nonzero E-vector has a nonzero extension of a basis vector, so passage from zero Qbar fibres to zero E-fibres is elementary and needs no additional node. Reduced structures on strata do not impose reducedness on T. Empty T, rank zero, disconnected strata, and nontrivial local systems are allowed. Rank r is computed after pulling a local basis to s and splitting a trivializing cover there; no global basis or global lattice on a connected component is assumed.

Assembly step 3: I opened `lem-sp-exact-functor-preserves-homology`: clauses (a) and (b) give precisely the kernel, cokernel and image identifications used. I opened `lem-weil-pbc-jointly-reflect-short-exact`: its hypotheses are abelian source/targets, preserved zero arrows and finite limits/colimits, and joint isomorphism reflection. These come from step 1 and the explicit kernel/cokernel argument using step 2. The image argument treats zero arrows separately from invertibility, so neither is taken from a definition or presumed from conservativity alone. The short-complex condition gf=0 is part of the parent's statement.

Assembly step 4: I read `prop-constructible-truncations`, `def-weil-weil-sheaf-complex`, and `def-weil-endofunctor-fixed-pair-category`. The first supplies automorphism pullback/truncation commutation, the others the fixed-pair arrow equation and faithful forgetting. For a kernel inclusion k, apply the autoequivalence to its universal property and use the equivariance square to obtain the structure map on the kernel; inverse Frobenius structures yield its inverse. Dualize for the cokernel. Thus this is a short universal-property argument on an abelian heart, correctly marked elementary with the exact definitions it uses. It is not an assertion that forgetting derived fixed pairs is faithful. After forgetting, steps 1–3 apply to the resulting constructible objects and arrows.

Assembly step 5: the local-defects node states abelianness of the precise cartesian local-data category, exact evaluations, the three specified defects, and cover detection for any separated finite-type open covering. Those are exactly what the assembly uses. The remaining equivalence between short exactness and vanishing of the three defects is the definition in an abelian category. I corrected the draft's phrase that a single evaluation 'creates kernels' to the accurate assertion that kernels are computed componentwise in the local-data category and evaluations are exact; a single component does not by itself determine the whole object. For a finite-type affine test V, its intersections with covering members are open in the Noetherian separated V and hence quasi-compact separated finite type; choose a finite subcover, rather than claiming the whole covering is finite. Common-stage zero equalities require only this finite diagram. This verifies both nonseparated ambient T and an infinite covering, without requiring a global E.

For the four new nodes, each object is introduced in its own statement, and definitions are cited or the needed notion is defined inline (good strata, lisse rank, cartesian data, the three defects). The J comparison is stated as a derived-category isomorphism, not merely per-degree equalities. All proof and proof-dependency lists are empty. The new sources name the actual finite-coefficient point, completed rings and raw/common-stage categories, so they do not switch coefficient meanings. The preserved old arguments are sufficiently detailed to restart each task independently.

I searched the whole DAG for the tags and point/immersion/continuous-realization/rank/local-exactness notions, opened the closest candidate statements, and searched the whole blueprint with `tools/blueprint_refs.py search` using 'point fibre', 'locally closed immersion', 'lisse rank', 'local exactness', 'continuous realization', 'point sections', 'connected components', 'cartesian local', 'geometric fibres' and 'constructible heart'. The nearest blueprint ancestor is `p-dl-a1-exact`; every new node has `via: [lem-dl-a1-constructible-fibres-exact]`. No blueprint node states one of these exact intermediate assertions. General tool results are reused; the differences from close DAG candidates are explicit below.

For Mathlib, every query in every new `mathlib_searches` was actually run through `msearch.py` and is present unchanged in `searches.jsonl`; full raw outputs are preserved as `.search.txt` files and in the JSON results fields. I read both semantic phrasings, Loogle, grep and LeanSearch hits. I inspected the close source candidates `TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero` (Topology/Sheaves/Abelian.lean:90), `AlgebraicGeometry.Scheme.isZero_ellAdicSheaf_of_isEmpty` (AlgebraicGeometry/Sites/ElladicCohomology.lean:71), and `Module.isLocallyConstant_rankAtStalk` (RingTheory/Spectrum/Prime/FreeLocus.lean:224). The first is for topological stalks, the second only the ell-adic coefficient sheaf on an empty scheme, and the third ranks of finitely presented flat modules over an ordinary ring's spectrum. None supplies the actual sections-and-localization point functor or the continuous-realization/common-stage comparisons in the new statements. The local-defects searches returned generic ShortComplex homology constructions and module-sheaf presentations, not cartesian local common-stage adic hearts. No node is claimed to be a Mathlib leaf.

I checked delivery-errors B–E against the files: quantified hypotheses and definition references, actual source labels, single TeX escaping; no proof hidden in an unsplit statement; exact citation statements (all assembly uses have a verbatim quote); no unlisted non-elementary assembly fact; no new elementary stand-alone kernel/image/fixed-pair node; no whole-parent restatement; no cycles introduced; correct coefficient rings and scheme maps; and empty/rank-zero/non-quasi-compact/infinite-cover cases as described above. Every non-elementary assembly step is below 2000 characters. The unchanged original statement remains the full claim to be proved. I found no false imported statement. The source does not assert that arbitrary pro-etale objects are detected by geometric points, and neither does this repair.

## Not duplicates

- lem-dl-a1-heart-connected-lisse-strata vs lem-sbc-fibre-component-neighbourhood: gives an open neighbourhood within a fibre component of a locally finite-type morphism; it has no adic heart, continuous realization or lisse strata.
- lem-dl-a1-heart-connected-lisse-strata vs lem-sc-fg-domain-positive-dimension-infinite-maximals: asserts infinitely many maximal ideals of a positive-dimensional finite-type domain; it does not realize a rational heart or construct lisse strata.
- lem-dl-a1-heart-connected-lisse-strata vs lem-sfb-noetherian-connected-components-open: only gives finitely many open components in a Noetherian space; the new assertion additionally concerns the actual rational realization, derived stratum restrictions, lissity and ranks.
- lem-dl-a1-heart-connected-lisse-strata vs lem-sfb-normal-scalar-extension-geometric-orbits: concerns semilinear finite-group orbits after normal field extension; it has no continuous-coefficient sheaves or constructible heart.
- lem-dl-a1-heart-connected-lisse-strata vs lem-weil-pbc-isolated-prime-finite-type-algebra-residue-finite: gives finiteness of the residue field of an isolated prime; it has no heart realization or lisse rank assertion.
- lem-dl-a1-heart-connected-lisse-strata vs lem-weil-pbc-normal-nagata-monogenic-n1: is the N-1 property for a monogenic extension of a normal Nagata domain; it is unrelated to adic sheaf strata.
- lem-dl-a1-heart-connected-lisse-strata vs lem-weil-pbc-zero-dimensional-singleton-neighbourhoods: constructs singleton opens and strict henselian local rings on zero-dimensional schemes; the new node allows arbitrary dimension and describes J and its lisse strata.
- lem-dl-a1-heart-connected-lisse-strata vs lem-weil-pbc-zariski-lemma: says a field finitely generated as a k-algebra is finite over k; it only supplies the residue-field ingredient, not the adic realization theorem.
- lem-dl-a1-heart-connected-lisse-strata vs new-zdbp-fibres-point: gives singleton field-extension fibres of zero-dimensional finite-type schemes; no constructible object is present.
- lem-dl-a1-heart-connected-lisse-strata vs lem-weil-pbc-finite-type-over-field-prime-intersection-maximal: states the Jacobson property of a finite-type algebra; it does not state the continuous realization or stratum lissity assertion.
- lem-dl-a1-heart-connected-lisse-strata vs new-zdbp-geometry: is finite-discrete topology and rational residue fields for a zero-dimensional scheme; the new node is an arbitrary-dimensional adic-heart realization assertion.
- lem-dl-a1-heart-connected-lisse-strata vs lem-weil-pbc-closed-point-residue-field-base: identifies residue fields at closed points over an algebraically closed field; no J, coefficient category or lissity is asserted.
- lem-dl-a1-heart-connected-lisse-strata vs lem-weil-pbc-lft-over-field-isolated-point-residue-finite: gives a finite residue extension at an isolated point; it has no derived rational realization.
- lem-dl-a1-heart-connected-lisse-strata vs lem-weil-pbc-zero-dim-integral-point: identifies an integral zero-dimensional finite-type scheme with Spec k; the new node permits arbitrary T and works with adic sheaves.
- lem-dl-a1-heart-connected-lisse-strata vs lem-weil-pbc-zero-dimensional-base-change-points: gives discrete topology and bijection of points under extension of the base field in dimension zero; the new node describes stratification of a rational heart object.
- lem-dl-a1-heart-connected-lisse-strata vs lem-weil-pbc-zero-dimensional-base-change-geometric-points: constructs points and a point equivalence after field extension for a zero-dimensional scheme, with no sheaf assertion.
- lem-dl-a1-local-heart-cover-defects vs lem-pe-set-sheaf-cover-descent: glues sheaves of sets and maps on one site; it does not compute kernels and homology in cartesian local adic hearts with varying finite fields.
- lem-dl-a1-local-heart-cover-defects vs lem-trf-fppf-scheme-data-sheaf-gluing: glues fppf-representable set-sheaf data into scheme data; no rational constructible heart or exactness defects occur.
- lem-dl-a1-local-heart-cover-defects vs def-trf-fine-log-etale-descent-datum: defines log-etale descent data rather than proving local adic-heart abelianness or defect detection.
- lem-dl-a1-local-heart-cover-defects vs lem-trf-fppf-local-representations-fully-faithful: gives full faithfulness of local fppf representations of set-sheaves; it does not prove componentwise abelian operations in the specified heart.
- lem-dl-a1-local-heart-cover-defects vs lem-sfb-sheaf-cover-local-isomorphism: gives a generic arbitrary-category sheaf cover criterion, used after finite-stage continuous realization; it alone does not supply adic common-stage defects or their cartesian restriction data.
- lem-dl-a1-local-heart-cover-defects vs lem-sfb-locally-prescribed-modules-small: proves essential smallness of locally prescribed module sheaves on a small site; no abelian local adic data or exactness defects are asserted.
- lem-dl-a1-local-heart-cover-defects vs lem-pur-clopen-ringed-module-gluing: concerns a finite disjoint clopen cover and one fixed ring sheaf; the new node uses arbitrary overlapping and infinite open covers and only locally chosen finite coefficient fields.
- lem-dl-a1-local-heart-cover-defects vs lem-pur-degree-zero-derived-map-gluing: concerns gluing morphisms between finite constant-coefficient complexes concentrated in degree zero; it does not state local adic-heart abelianness or rational coefficient-stage defect detection.
- lem-dl-a1-local-heart-cover-defects vs lem-pur-sheaf-hom-is-sheaf: states the sheaf condition for internal Hom on a single ringed site; it does not compute exactness defects for local adic hearts.
- lem-dl-a1-local-heart-cover-defects vs lem-pur-vector-frame-integration-site-descent: glues finite-coefficient vector-bundle integration/trace maps and frame compatibilities; no common-stage locally constructible adic heart occurs.
- lem-dl-a1-local-heart-cover-defects vs lem-pur-sheaf-hom-cover-gluing: glues module-sheaf arrows over a fixed ringed site; it does not provide the adic heart or varying-coefficient stage comparisons needed here.

- lem-dl-a1-point-fibre-stage-exact vs lem-weil-point-rational-fibre-exact: the existing node states triangulated exactness of the rational point functor; the new assertion includes preservation of the standard halves, finite-dimensional heart values, finite diagrams of heart representatives, and canonical scalar/common-stage compatibility.
- lem-dl-a1-point-fibre-stage-exact vs lem-per-adic-normalized-fibre-comparisons: that node specifies normalized inverse-limit lattice fibres at arbitrary geometric points; the new assertion is about the particular sections-and-localization functor on Spec k and its standard halves. Identifying the two functors is not a one-line specialization supplied by that statement.
- lem-dl-a1-heart-connected-lisse-strata vs lem-per-continuous-rational-derived-realization: that node supplies the general raw rational category's ambient t-exact realization; the new statement includes the specific identification with the other integral category used by the heart, the specified J comparison, good reduced strata, lisse-heart restrictions, connected-component ranks and k-points. The old Steps 5–6 constitute this comparison/adaptation task, not a new generic stratification lemma.
- lem-dl-a1-heart-connected-lisse-strata vs det-lem-coefficient-heart-common-stratification: the existing statement concerns already-constructible module sheaves and exact restrictions; the new node starts from the project's rationalized standard heart and must establish its realization as such a degree-zero module sheaf with the specified comparisons.
- lem-dl-a1-finite-stage-fibre-vanishing vs lem-per-intrinsic-constructible-fibre-exactness: that node is for the different intrinsic fibre functor of def-per-adic-normalized-fibre-data; the new statement computes the dimension of the actual Spec k sections fibre by a split pro-etale chart and detects vanishing using only k-rational points, not every geometric point with arbitrary algebraically closed residue extension.
- lem-dl-a1-finite-stage-fibre-vanishing vs lem-weil-pbc-noetherian-stratum-detection: that node detects vanishing from actual inverse images to every stratum and its cover; it does not identify sections at Spec k with lisse rank or show rational-point fibre vanishing implies vanishing on a stratum.
- lem-dl-a1-local-heart-cover-defects vs def-dl-a1-locally-constructible-adic-heart: the existing node defines cartesian data, componentwise arrows and zero maps; it does not assert abelianness, exact evaluation, existence of cartesian defects or cover detection.

## Complete retained proof material

The following is the full returned proof, verbatim, with all original citations and source places. It is kept as the work specification for the statement-only nodes and as evidence that no argument was discarded during re-splitting. It is not inserted as proof text in any new unsplit node.

### Returned step 1

Work first at a finite coefficient field $E$. The scheme $Y$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian], since it is of finite type over a field. A $k$-linear point $y:s=\operatorname{Spec}k\to Y$ is a section of the separated structure morphism, so is a closed immersion by [lem-weil-pbc-section-separated-closed-immersion]. Every map $s\to Y$ in the statement has this form up to an automorphism of $s$: its map on the base field is a self-embedding of $k=\overline{\mathbf F}_q$, hence an automorphism, because it permutes each finite subfield. A scheme automorphism is itself a locally closed immersion. Thus it suffices for exactness to treat locally closed immersions.

Uses: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-section-separated-closed-immersion.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Remark 6.8.15 (closed immersions); elementary reduction to closed k-points.

### Returned step 2

For a locally closed immersion $a:S\to Y$, [lem-sf-immersion-completed-pullback-comparison] identifies completed integral pullback with ordinary exact inverse image and says it preserves integral constructibility. Since every scheme here is of finite type over $k$, hence Noetherian and finite-dimensional with $\ell$ invertible, [lem-weil-pbc-integral-stratified-perfect-characterization] says that the integral category of [def-weil-derived-complete-integral-detailed] used by the constructible heart is exactly the category of [def-weil-pbc-bounded-constructible-complete], with the same completed ring sheaf; the two raw rationalizations therefore coincide. Its exact rationalization is [prop-weil-pbc-rational-transport]. It preserves each half of the rational standard pair: represent an object in that half by an integral object in the corresponding half, as in [def-weil-constructible-standard-tstructure], and apply the exact integral inverse image. Consequently $La^*$ is $t$-exact. In particular this applies to $y:s\to Y$ and to every stratum immersion used below.

Uses: lem-sf-immersion-completed-pullback-comparison, prop-weil-pbc-rational-transport, def-weil-constructible-standard-tstructure, lem-weil-pbc-integral-stratified-perfect-characterization, def-weil-derived-complete-integral-detailed, def-weil-pbc-bounded-constructible-complete.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Remark 6.8.15: inverse image under locally closed immersions is naive inverse image.

### Returned step 3

At $s$, [lem-weil-point-proetale-sections-exact] gives $H^r\Gamma(s,K)=\Gamma(s,\mathcal H^rK)$ at the integral stage. Tensoring these module complexes with $E$ is exact by [lem-weil-pbc-localization-module-exact]. Hence the point-fibre functor of [def-weil-finite-coefficient-point] preserves both halves of the rational standard pair. Its values are bounded complexes with finite-dimensional cohomology by [lem-weil-point-sections-finiteness]. Together with Step 2 this makes $\operatorname{Fib}_sLy^*$ a triangulated, $t$-exact functor whose restriction to the heart takes values in finite-dimensional $E$-vector spaces. The short-exact/triangle correspondence in [lem-weil-heart-short-exact-triangles], applied before and after this functor, proves that this restriction is exact.

Uses: lem-weil-point-proetale-sections-exact, lem-weil-pbc-localization-module-exact, def-weil-finite-coefficient-point, lem-weil-point-sections-finiteness, lem-weil-heart-short-exact-triangles.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 6.8.14(2), Remark 6.8.15; evaluation on Spec k and passage to E.

### Returned step 4

Pass to $\Qlb$ using the actual common-stage category, rather than a discrete constant-coefficient category. By [prop-weil-pbc-common-stage-calculus], every finite diagram of objects, arrows and asserted equalities has a representative at a common finite field. By [prop-constructible-truncations], truncations commute with finite scalar extension and with the coefficient transitions. Thus heart objects may be replaced by $H^0$ of their representatives; kernels and cokernels are obtained from cones by the formulas in [lem-weil-heart-short-exact-triangles], and are represented at the same stage. The immersion pullbacks of Step 2 preserve the two halves stagewise. The point-fibre scalar comparisons of [lem-weil-point-sections-scalar-extension] and [def-weil-finite-coefficient-point] make Step 3 independent of representatives. Finally [lem-weil-cohomology-commutes-scalar-extension] identifies its degree-zero value with the finite-stage vector space tensored with $\Qlb$. The short-exact/triangle criterion again proves exactness of every fibre functor on $\Sh_c(Y,\Qlb)$.

Uses: prop-weil-pbc-common-stage-calculus, prop-constructible-truncations, lem-weil-heart-short-exact-triangles, lem-weil-point-sections-scalar-extension, def-weil-finite-coefficient-point, lem-weil-cohomology-commutes-scalar-extension.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 6.8.14 and the common-stage coefficient construction.

### Returned step 5

To prove zero-object detection, take $F\in\Sh_c(Y,\Qlb)$ represented by a heart object $F_E$ over one finite field, as in Step 4. Use the equivalence $J_Y$ of [lem-weil-pbc-condensed-e-realization]; its source category is the raw rationalization of [def-weil-pbc-bounded-constructible-complete], which is the category $D^b_c(Y,E)$ containing $F_E$ by the identification of integral categories in [lem-weil-pbc-integral-stratified-perfect-characterization] (Step 2). Its coefficient ring is the sheaf of continuous $E$-valued functions, and it is induced by derived extension of scalars from the completed integral ring, not by extension to a discrete constant sheaf. That extension is exact by [lem-weil-pbc-continuous-integral-scalar-exact]; it therefore preserves cohomology by [lem-sp-exact-functor-preserves-homology]. The definitions of the rational standard pair imply that $J_Y$ sends both halves into the ambient standard halves. Thus $J_Y(F_E)$ is a sheaf in degree zero. The same realization lemma says its cohomology is stratified locally free of finite rank over the continuous coefficient sheaf. The essential-image assertion of [lem-tw-lisse-rational-realization] identifies these locally free sheaves with the lisse subcategory of the rational heart, so $F_E$ restricts to a lisse $E$-sheaf on each stratum. The pullback comparisons in that lemma identify these restrictions with $J_S(La^*F_E)$.

Uses: lem-weil-pbc-condensed-e-realization, lem-weil-pbc-continuous-integral-scalar-exact, lem-sp-exact-functor-preserves-homology, def-weil-constructible-standard-tstructure, lem-tw-lisse-rational-realization, lem-weil-pbc-integral-stratified-perfect-characterization, def-weil-derived-complete-integral-detailed, def-weil-pbc-bounded-constructible-complete.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 6.8.14(2), Definition 6.8.6; finite-stage realization bridge.

### Returned step 6

Refine the partition of Step 5 to a good stratification using [lem-sfb-noetherian-good-stratification-refinement]; the realized sheaf $L_S=J_S(La^*F_E)$ is still lisse on each refined stratum $S$, by restriction. Give $S$ its reduced subscheme structure: it is a separated finite-type $k$-scheme whose underlying space is Noetherian [lem-weil-pbc-finite-type-over-noetherian]. By [lem-sfb-noetherian-connected-components-open] its connected components $C$ are finitely many and open, so they form a finite Zariski open covering of $S$ by nonempty connected separated finite-type $k$-schemes. Each $C$ has a $k$-point $x:s\to C$: a nonempty affine open $\operatorname{Spec}A\subset C$ has $A\ne0$ finitely generated over $k$, and a maximal ideal of $A$ has residue field $k$ by [lem-wf-affine-nullstellensatz-vanishing](1). Its composite $s\to C\to S\to Y$ is a point tested by the hypothesis. By [det-lem-stratified-lattice-rank] the rank loci of the lisse sheaf $L_S|_C$ are open and closed in $C$; since $C$ is connected, $L_S|_C$ has one constant rank $r_C\ge0$, i.e. it is pro-etale locally isomorphic to $E_C^{\oplus r_C}$.

Uses: lem-sfb-noetherian-good-stratification-refinement, lem-weil-pbc-finite-type-over-noetherian, lem-sfb-noetherian-connected-components-open, lem-wf-affine-nullstellensatz-vanishing, det-lem-stratified-lattice-rank.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Definition 6.8.3 and Definition 6.8.6 (lisse = locally free of finite rank on strata); Stacks 04MF and the Nullstellensatz; reviewer repair of the point-fibre argument.

### Returned step 7

Suppose every displayed fibre of $F$ is zero; fix a component $C$ of a stratum $S$ and its $k$-point $x$ from Step 6, and let $b:C\to Y$ be the immersion. By Steps 3 and 4, $\operatorname{Fib}_sLx^*Lb^*F_E$ is an $E$-vector space in degree zero whose extension to $\Qlb$ is the fibre of $F$ at $bx$, hence zero; so it is zero, since scalar extension of a nonzero vector space contains an extended basis vector. By [lem-tw-lisse-rational-realization] for $x:s\to C$ (its comparisons hold for all scheme morphisms of finite-type $k$-schemes), this fibre is the sections at $s$ of the ordinary pullback $x^*L_C$ of the realized lisse sheaf $L_C=L_S|_C$, which the pullback comparisons of [lem-weil-pbc-condensed-e-realization] identify with $J_C(Lb^*F_E)$; and $x^*$ sends a local basis to a local basis, so $x^*L_C$ is pro-etale locally $E_s^{\oplus r_C}$. Take a nonempty affine member $W=\operatorname{Spec}B$ of such a trivializing covering of $s$. The one-point space $s$ is w-local with extremally disconnected component space and $k$ is strictly henselian [def-weil-pbc-w-local, def-weil-pbc-henselian-terminology], and $k\to B$ is faithfully flat weakly etale, so [lem-weil-pbc-wcontractible-geometric-criterion] gives a retraction, i.e. a section $\sigma:s\to W$ over $s$. The sections of $x^*L_C$ at $s$ equal those of its restriction to $W$ at $(s,\sigma)$, namely $E_s(s)^{\oplus r_C}=E^{\oplus r_C}$, using the continuous-function description of the coefficient ring in [lem-weil-pbc-condensed-e-realization]. Hence $r_C=0$, so $L_C$ is pro-etale locally zero and therefore zero. The components cover $S$, so [lem-sfb-sheaf-cover-local-isomorphism], applied to $0\to L_S$, gives $L_S=0$. Since $J_S$ is an equivalence [lem-weil-pbc-condensed-e-realization], $La^*F_E=0$, i.e. $F_E|_S=0$ for every stratum.

Uses: lem-tw-lisse-rational-realization, lem-weil-pbc-condensed-e-realization, def-weil-pbc-w-local, def-weil-pbc-henselian-terminology, lem-weil-pbc-wcontractible-geometric-criterion, lem-sfb-sheaf-cover-local-isomorphism.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Definition 6.8.3 (lisse E-sheaves locally free of finite rank) and Proposition 6.8.14(2); evaluation at the weakly contractible point Spec k; reviewer repair.

### Returned step 8

A finite good stratification has a stratum open in the union of the remaining strata: choose one maximal in the closure order; its complement is a finite union of closed strata-closures. Remove such an open stratum successively. At each stage [prop-sf-open-closed-triangle-all-stages] gives $j_!j^*F_E\to F_E\to i_*i^*F_E\to$. The restriction to the removed stratum is zero by Step 7, and the restriction to its closed complement is zero by induction on the number of strata. Thus both outer terms are zero, and $F_E=0$. On the empty scheme the empty covering and the sheaf axiom force every module to be zero; this is the zero-stratum base case. Therefore $F=0$. This proves joint zero-object detection without any assertion about arbitrary pro-etale sheaves.

Uses: prop-sf-open-closed-triangle-all-stages.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Definition 6.8.6, finite stratification devissage using open-closed triangles.

### Returned step 9

For a morphism $u:F\to G$, exactness of the fibres (Step 4) identifies the fibres of $\ker u$ and $\operatorname{coker}u$ with the corresponding vector-space kernel and cokernel, by [lem-sp-exact-functor-preserves-homology](a). If every fibre map is an isomorphism, both objects have zero fibres, hence are zero by Step 8, so $u$ is an isomorphism. This is joint conservativity. If every fibre map is zero, [lem-sp-exact-functor-preserves-homology](b) gives zero fibres of $\operatorname{im}u$; Step 8 gives $\operatorname{im}u=0$, hence $u=0$.

Uses: lem-sp-exact-functor-preserves-homology.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.8.7; elementary kernel, cokernel and image argument.

### Returned step 10

Apply [lem-weil-pbc-jointly-reflect-short-exact] to the abelian constructible heart and the family of geometric coefficient fibres. Step 4 supplies preservation of finite limits and colimits and zero morphisms (exact additive functors), and Step 9 supplies joint reflection of isomorphisms. Its conclusion is precisely the claimed equivalence between short exactness in the heart and short exactness of every sequence of finite-dimensional fibres.

Uses: lem-weil-pbc-jointly-reflect-short-exact.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Finite-stage stalk criterion (Stacks Tag 03PU), transferred to the constructible heart.

### Returned step 11

For Weil sheaves, Frobenius pullback preserves the standard truncations by [prop-constructible-truncations], and is an autoequivalence. In the fixed-pair description [def-weil-weil-sheaf-complex, def-weil-endofunctor-fixed-pair-category], the kernel of an equivariant arrow inherits its structure isomorphism by the kernel universal property, applied to the commuting square; its inverse is induced by the inverse Frobenius structures. The identical cokernel construction gives a cokernel fixed pair. Thus kernels and cokernels are created in the underlying heart, and the faithful forgetful functor is exact and reflects exactness and zero arrows. Steps 4, 9 and 10 therefore give all the stated Weil-sheaf assertions after forgetting structure.

Uses: prop-constructible-truncations, def-weil-weil-sheaf-complex, def-weil-endofunctor-fixed-pair-category.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Weil structures: fixed pairs; Proposition 6.8.14 and ordinary heart operations.

### Returned step 12

Finally, on a locally finite-type $k_0$-scheme use separated finite-type affine opens. Restriction to an open is exact by the immersion argument of Step 2, locally at a finite coefficient stage. For a short complex form its kernel at the left, its middle homology and its cokernel at the right; [lem-sp-exact-functor-preserves-homology] says these restrict to the corresponding three defects. A locally constructible defect which restricts to zero on the covering is zero: it suffices to test this on every affine open $V$ of finite type, which is separated, so that $V$ is covered by its finitely many separated finite-type intersections with members of the covering; realize the defect on $V$ by Step 5 as a continuous-coefficient module sheaf and apply [lem-sfb-sheaf-cover-local-isomorphism] to its zero map. A finite subcover suffices there, so all required diagrams and their zero restrictions can be taken at a common finite coefficient stage by [prop-weil-pbc-common-stage-calculus]. Hence the three defects vanish globally exactly when they vanish on the covering. This proves the locality clause; no global finite coefficient field on a non-quasi-compact scheme is required.

Uses: lem-sp-exact-functor-preserves-homology, lem-sfb-sheaf-cover-local-isomorphism, prop-weil-pbc-common-stage-calculus.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Remark 6.8.15 and sheaf locality for open covers.

## What remains unfinished

Only the four new statement-only nodes remain to be split by future workers, as required by the repair order. No Lean proof is claimed. All required stage-1 repair work, searches, statement checks and citation evidence are present. The delivery tool performs the server checks; validation outcomes are recorded below.

## Validation

Server check_dag on the initial overlay: OK, no finding introduced by the sandbox or its nodes; unrelated existing route advisories only. Full deliver.py --no-push exited 0: OK (not pushed) at 7bc55551ff5, preflight passed. The direct-delivery brief authorizes the worker to push after this success; no second worker is required.
