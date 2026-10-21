# Worker report: lem-pe-successive-quotient-linear-triangle

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-pe-successive-quotient-linear-triangle.json`: retained the statement verbatim; replaced the 4954-character proof by a 2024-character assembly in five steps.
- `dag/nodes/sec-proetale-coefficients/lem-pe-successive-quotient-flat-complex-sequence.json`: new statement, status `unsplit`, no Mathlib match. Owns the coefficient maps and their exactness, and the flat-term tensor cochain sequence with the middle quotient action.
- `dag/nodes/sec-proetale-coefficients/lem-pe-restricted-kflat-tensor-identification.json`: new statement, status `unsplit`, no Mathlib match. Owns the scalar-first/sheafified tensor comparison, exact derived restriction comparison, the K-flat computation of each term, and its compatibility with coefficient maps which need not be ring maps.
- `citations.json`: one verbatim statement quotation for each cited node in each assembly step.
- `searches.jsonl`: actual msearch.py records; the two new nodes each record five searches, with semantic searches in two phrasings, Loogle and grep. No search was fabricated or reported as absent when unavailable.

## Attachments

None. I searched the live `lean/WeilConjectures/` by notion and blueprint tag. The retained `lean/Sheaf/Algebra/Homology/SuccessiveQuotientLinearTriangle.lean` ends in `SheafOfModules.successive_quotient_linear_triangle := sorry`; its earlier declarations only package the terms, maps and conclusion. These do not prove the item or either new assertion. I wrote no Lean and ran no compiler.

## WANTED

None. The current blueprint and the relevant Stacks source files are present.

## What was wrong and what was repaired

This is the deliberate 2026-10-21 re-split, despite the live item's older reviewed split and recorded Lean statement. The problem is granularity, not its mathematical statement: its proof carried 4954 characters of work. There was no item/report in the retained sandbox, only four launcher markers; I copied the current live node, including its searches, citations in the text, Lean metadata and prior reviews. The deliver tool retains current maintainer-owned metadata when packaging. I did not change its statement, statement dependencies, chapter, unit, existing Lean record or the unit's route.

The two new nodes are independent jobs, neither a derived triangle nor an assertion of the entire item. The first can be proved without K-flatness, derived scalar extension or any SES-to-triangle theorem. The second has no regular element, principal quotient, exact coefficient sequence or triangle; it works for an arbitrary coefficient map and arbitrary A-linear coefficient-module maps. In particular it applies to the multiplication arrow, which is not a ring morphism. Their arguments are of comparable size: the former owns the original steps 1 and 3 plus the tensor-map construction of step 2; the latter owns the substantive identifications and arrow comparison of step 5. Existing lem-pc-kflat-resolution owns resolution existence and lem-weil-pbc-complex-ses-triangle owns passage to the derived triangle. The item now only assembles these results and explicitly conjugates the connecting map.

## What remains

No part of the item's assembly is left as an unspecified argument. The two new nodes are intentionally statement-only jobs for other stage-1 workers: `proof: []`, `proof_deps: []`, `proof_origin: null`, `status: unsplit`. The source and the retained argument below give each a precise handover. They do not depend on this item and do not form a cycle.

## Review by Q33

I read the chapter and unit records and the current main-20261015 integral-criterion-reductions proof, second paragraph. It uses the successive coefficient exact sequence, followed by derived tensor, precisely the route retained here. I also read the complete five-step live proof and the corresponding Lean theorem/docstring. The item has no changed statement or statement dispute. The read clone's already reviewed status does not supersede this explicit human re-split assignment.

For the first new node I read `sites-modules.tex` Tag 03DA (lemma-abelian, kernels/cokernels and exactness of the forgetful functor), Tag 03EK (section-tensor-product, sectionwise balanced tensor followed by sheafification), and Tag 03ER (definition-flat, item (3), exactness of the SHEAF tensor functor). I checked the two quotient ring maps against def-pe-principal-power-ring-quotients, the local formula for a and b, and the actions on the endpoint tensors. The proof retained below cancels t only using the explicit injectivity assumption, locally after quotient lifts. Kernels are sectionwise but quotient sections lift only on a cover; no point of the site or global lifting is assumed. Its cochain differentials are 1 tensor d_P; all displayed maps commute with them. Flatness is used in each degree as exactness of sheaf tensor, never inferred from flatness of modules of sections. Exactness over R_n and B refers to the same underlying abelian sheaf sequence.

For the second new node I read `sites-cohomology.tex` Tags 06YY (lemma-derived-base-change, including the K-flat computation) and 06YT (lemma-derived-tor-quasi-isomorphism-other-side), together with 03EK for the scalar-first/scalar-last exchange. I checked its comparison against the full statement of lem-pur-derived-change-of-rings, particularly clause (2), rather than merely citing the name. A,B,S are commutative ring sheaves on the SAME small site. S tensor_B P has the S-action on S, P tensor_B S has it on S in the second factor; the swap is S-linear. Local balanced-tensor maps and their inverses respect restrictions and sheafification, and the coefficient is in degree zero, so there is no Koszul sign. Restriction retains the underlying abelian sheaves and differential; cohomology kernels/cokernels and the negative differential on the shift therefore give preservation of quasi-isomorphisms and the stated shift comparison. The displayed composite fixes which object isomorphism is used: canonical K-flat computation composed with F(e inverse), followed by its inverse under exact restriction. The coefficient-map square is asserted for A-linear module maps, not only algebra maps; this is needed for a. It adds the actual scalar-first comparison and its module-map compatibility, which the existing change-of-rings theorem does not state. It is thus a separate comparison job, rather than relabeling that theorem.

I opened every node cited by the five assembly steps. Step 1 uses lem-pc-kflat-resolution: its statement gives a K-flat complex with flat terms mapping quasi-isomorphically to ANY complex, so unbounded G is permitted. Step 2 uses the full statement of lem-pe-successive-quotient-flat-complex-sequence: n>1, regular t and flat P are exactly its hypotheses, and its conclusion supplies the degreewise SES over R_n plus both formulas, not merely a definition of flatness. Step 3 uses def-weil-sheaf-of-modules-category for abelianness under the stated site size and lem-weil-pbc-complex-ses-triangle for a distinguished triangle whose first two arrows are Q(alpha), Q(beta). Both statements explicitly give these conclusions. Step 4 uses lem-pe-restricted-kflat-tensor-identification with B→A=B→R_n and v equal to q_minus, identity or q_1. The quotient-composition equations needed there are given in the first new node. The multiplication and quotient maps are R_n-linear, so its A-linear coefficient-map equation gives exactly the requested second-factor arrows. Step 5 cites the distinguished-triangle definition in def-weil-abstract-derived-category: writing all three conjugations, including i_minus[1] delta i_1 inverse, exhibits a triangle isomorphism. This final step is elementary, and the previous steps are marked non-elementary. Each citation has a verbatim supporting statement quote in citations.json; no step borrows an unpublished construction from a cited proof.

I checked the small cases: n=2 over Z with t=p, the zero complex, t a unit (all three quotients zero), and the zero ring. With t=0 the regularity hypothesis forces B=0; it is not an accidentally vacuous proof for a nonzero ring. Without regularity, B=Z/4, t=2, n=3 has noninjective first coefficient arrow. Without flat terms, B=Z, t=2, n=2 and P=Z/2 in degree zero makes the first tensor arrow zero and nonmonic. The first new statement correctly assumes both hypotheses. The second comparison also works for h=0, S=T and h identity, and for coefficient maps which are not flat. Unboundedness is harmless because every tensor here has the coefficient in degree zero and step 3 is the unbounded SES triangle. No completeness assumption entered either new statement.

I checked delivery-errors B–E: both new statements introduce all their objects, cite the notions used, have TeX with single mathematical escapes, and contain no proof sketches or proof dependencies. Sources use the actual Stacks tags/labels and the current blueprint place. Searches before creation covered the whole DAG, blueprint and project Lean source; no exact or more general pre-existing statement supplies either whole new construction. Mathlib hits were read in their source: Flat/CategoryTheory.lean lines 41/46 are ordinary ring-module tensor exactness, Regular/Category.lean line 51 is the ordinary regular multiplication sequence, and Sheaf/ChangeOfRings.lean line 36 only defines underived restriction. None yields either new statement by one-line specialization. The new nodes do not restate a clause of the triangle and cannot prove the item without each other and the SES-triangle theorem. No step exceeds 2000 characters; the assembly totals 2024 characters, below the required 3000. No SGA source or route was used.

The generic off-unit tool lem-pc-kflat-resolution remains declared in split_report.tool_uses. Derived-change-of-rings is still a statement dependency and occurs in the second new node's statement, but the assembly now cites that node for the actual comparison instead of using change-of-rings as a proof dependency. The chapter/unit route is unchanged.

## Not duplicates

- lem-pe-restricted-kflat-tensor-identification vs lem-sc-hom-tensor-reverse-pair: the latter curries an ordinary tensor pairing into internal Hom; it has no K-flat derived extension or restriction-localization comparison.
- lem-pe-restricted-kflat-tensor-identification vs def-pd-proetale-section-module-functors: the latter defines pro-etale internal/section module functor comparisons for condensed coefficients, not this arbitrary small-site scalar-first derived model and its A-linear coefficient-map square.
- lem-pe-restricted-kflat-tensor-identification vs def-pd-section-module-operations-data: the latter records existing scheme pullback/direct-image operations and local tensor conventions, not the K-flat derived scalar extension comparison.
- lem-pe-restricted-kflat-tensor-identification vs lem-pd-ringed-direct-image-pairing-lax: the latter constructs the lax monoidal structure on ordinary direct image; it has no derived change-of-rings computation or exchange of tensor-factor conventions.
- lem-pe-successive-quotient-flat-complex-sequence vs lem-weil-pbc-exact-faithful-torsion: the latter reflects torsion through a fully faithful functor, not the principal-power coefficient sequence or its termwise flat tensor exactness.

- lem-pe-restricted-kflat-tensor-identification vs lem-pe-internal-section-tensor-comparison: compares internal module objects with section modules, not the restricted scalar-first K-flat model of a ring-sheaf extension.
- lem-pe-restricted-kflat-tensor-identification vs lem-sf-completed-tensor-finite-shift: computes the signed shift of a two-complex finite coefficient tensor tower, not a restricted K-flat change-of-rings computation.
- lem-pe-restricted-kflat-tensor-identification vs def-zl-pbc-finite-raw-scalar-comparison: defines a finite coefficient-field/rationalization comparison, not this arbitrary ring-sheaf derived comparison.
- lem-pe-restricted-kflat-tensor-identification vs def-trf-singleton-site-operations: defines predicates on the one-object site and asserts no comparison theorem; the new node asserts one on any small site.
- lem-pe-restricted-kflat-tensor-identification vs lem-sc-hom-tensor-comparison-natural: asserts naturality of ordinary tensor/sheafification, with no K-flat model or derived restriction identification.
- lem-pe-restricted-kflat-tensor-identification vs lem-sc-hom-tensor-summand-restriction-ext: is an extensionality criterion for total-tensor internal Hom, not a derived scalar-extension comparison.
- lem-pe-restricted-kflat-tensor-identification vs lem-sc-internal-hom-coproduct-fan: concerns internal Hom of coproducts, not scalar extension or its tensor-factor comparison.
- lem-pe-restricted-kflat-tensor-identification vs lem-pc-sheaf-modules-tensor-closed: gives the closed symmetric monoidal structure, but not the derived localization comparison after scalar restriction.
- lem-pe-restricted-kflat-tensor-identification vs lem-sc-hom-tensor-section-natural: gives naturality of ordinary pure tensor sections, not a K-flat derived scalar comparison.
- lem-pe-restricted-kflat-tensor-identification vs lem-sc-hom-tensor-summand-localized-ext: tests equality on local tensor generators, without derived scalar extension or restriction.
- lem-pe-restricted-kflat-tensor-identification vs lem-pc-sites-sheaf-tensor-bilinear-universal: is the ordinary bilinear universal property, without the derived scalar computation and restriction comparison.
- lem-pe-restricted-kflat-tensor-identification vs lem-sc-internal-hom-product-fan: concerns internal Hom preserving products, not derived coefficient extension.
- lem-pe-successive-quotient-flat-complex-sequence vs lem-pe-left-module-comparison-vanishing-criterion: deduces vanishing of higher etale comparison direct images, not principal-quotient exactness or its flat-term tensor sequence.
- lem-pe-successive-quotient-flat-complex-sequence vs lem-coef-module-flat-cotorsion-foundation: constructs a flat/cotorsion pair and generator, not the successive principal-quotient coefficient and tensor sequence.
- lem-pe-successive-quotient-flat-complex-sequence vs lem-weil-pbc-diagram-site-module-equivalence: gives a diagram-site equivalence, not exactness of principal-power quotients.
- lem-pe-successive-quotient-flat-complex-sequence vs lem-weil-pbc-finite-perfect-adic-coefficient-limit: computes an adic coefficient/Roos limit with epimorphic transitions, not the injection by t and three-term flat tensor sequence.
- lem-pe-successive-quotient-flat-complex-sequence vs def-weil-pbc-derived-normalization-arrows: defines constant-sheaf and exact-restriction normalization arrows, not a principal-power coefficient SES.
- lem-pe-successive-quotient-flat-complex-sequence vs lem-weil-pbc-module-sheaves-colimits-forgetful: gives exact forgetfulness and small limits/colimits, not the regular-element quotient sequence or its tensor maps.
- lem-pe-successive-quotient-flat-complex-sequence vs lem-weil-pbc-proetale-ringed-filtered-colimits: concerns filtered-colimit preservation for closed-immersion direct image, not principal-quotient exactness.
- lem-pe-successive-quotient-flat-complex-sequence vs lem-weil-pbc-closed-immersion-pushforward-cokernel: concerns preservation of cokernels under a closed immersion, not multiplication/quotient coefficients.
- lem-pe-successive-quotient-flat-complex-sequence vs lem-weil-pbc-module-sheaves-enough-injectives: asserts enough injectives on an etale site, not the coefficient SES or flat tensor construction.
- lem-pe-successive-quotient-flat-complex-sequence vs lem-weil-pbc-graded-realization-local-generators-epi: proves a graded-generator map epimorphic, not the principal quotient coefficient sequence.
- lem-pe-successive-quotient-flat-complex-sequence vs lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits: concerns exact evaluation and colimits at weakly contractible affine objects, not a point-free coefficient/tensor SES.
- lem-pe-successive-quotient-flat-complex-sequence vs lem-weil-pbc-module-sheaves-grothendieck-abelian: asserts Grothendieck abelianness of constant-coefficient etale modules, not exactness of successive principal-power quotient tensors.

Additional notion/statement comparisons read beyond the shared-tag list:

- lem-pe-successive-quotient-flat-complex-sequence vs def-pe-principal-power-ring-quotients: the latter constructs the ring sheaves/projections and gives no regular-element short exact sequence or tensor exactness.
- lem-pe-successive-quotient-flat-complex-sequence vs def-pc-flat-sheaf-modules: the definition supplies exactness of sheaf tensor only after constructing the coefficient sequence; the new node also constructs that sequence, the R_n-actions and cochain maps.
- lem-pe-successive-quotient-flat-complex-sequence vs lem-pe-successive-quotient-linear-triangle: the new node is solely a cochain short exact sequence, with no K-flat assumption or derived triangle.
- lem-pe-restricted-kflat-tensor-identification vs lem-pur-derived-change-of-rings: the latter computes P tensor_B S in D(S); it does not state the scalar-first swap, derived restriction comparison or compatibility with arbitrary A-linear coefficient maps. The new statement fixes those comparisons simultaneously.
- lem-pe-restricted-kflat-tensor-identification vs lem-pe-kflat-scalar-tower-realization: the tower realization uses ring-map transitions and restricts all terms to the base ring; it does not cover an intermediate A and the multiplication-by-t coefficient MODULE map used here.
- lem-pe-restricted-kflat-tensor-identification vs lem-pur-compatible-coefficient-tower: the latter constructs ordinary strict tensor towers and restriction quasi-isomorphism tests; it does not identify a scalar-first tensor with the derived extension of K or allow non-ring coefficient transition maps.
- lem-pe-restricted-kflat-tensor-identification vs lem-pur-sheaf-ring-derived-coefficient-adjunction: the latter gives the derived adjunction and units/transposes, not the scalar-first tensor swap compatibility for arbitrary A-linear coefficient-module maps.
- lem-pe-restricted-kflat-tensor-identification vs lem-pe-successive-quotient-linear-triangle: the new lemma contains no principal quotients, regular element, exact sequence or triangle.

Whole-blueprint searches included “successive quotient linear triangle”, “coefficient exact”, “flat tensor”, “restriction scalars”, “tensor exchange”, “principal power” and “K-flat restriction”; the returned blueprint nodes concern different objects (universal-coefficient degree forms, cup/tensor pairings), not either new statement. Both new nodes have same_as empty and from.node det-prop-integral-criterion-reductions via this item.

## Retained original argument and allocation

The following is the original live proof verbatim, to preserve every argument from the returned 4954-character proof. It is handover material in this report, not a proof field of either unsplit node.

### Original step 1

Owner: lem-pe-successive-quotient-flat-complex-sequence.

Fix $n>1$. There are $R_n$-linear maps $a:R_{n-1}\to R_n$, $\bar b\mapsto\overline{tb}$, and $b:R_n\to R_1$, $\bar b\mapsto\bar b$, where the endpoint actions are restriction along the quotient ring maps. The first map is well-defined since $t(t^{n-1}c)=t^nc$; changing a lift of an $R_n$-scalar changes its action on $R_{n-1}$ by a multiple of $t^{n-1}$. Quotient sheaves have local representatives, so exactness can be checked after making such lifts on coverings, without using points. If $a(\bar c)=0$, locally $tc=t^nd$, hence $t(c-t^{n-1}d)=0$; injectivity of multiplication by $t$ gives $c=t^{n-1}d$, so $a$ is monic. If $b(\bar c)=0$, locally $c=td$, giving $\bar c=a(\bar d)$. Conversely $ba=0$, and $b$ is locally surjective by lifting a class in $R_1$ locally to $B$ and then taking its class in $R_n$. Kernels are sectionwise and cokernels are sheafified sectionwise cokernels, as specified in [def-weil-sheaf-of-modules-category]. Thus $0\to R_{n-1}\xrightarrow{a}R_n\xrightarrow{b}R_1\to0$ is short exact both as $B$-modules and as $R_n$-modules [def-pc-sheaf-restrict-scalars].

### Original step 2

Owner: lem-pc-kflat-resolution for resolution existence; lem-pe-successive-quotient-flat-complex-sequence for the tensor complexes and maps.

Represent $K$ by a cochain complex $G$. By [lem-pc-kflat-resolution] choose a quasi-isomorphism $P\to G$ with $P$ K-flat and every $P^i$ flat. No bound on $G$ is needed. For $j\in\{n-1,n,1\}$ put $C_j^i=R_j\otimes_B P^i$, with differential $1\otimes d_P^i$ and $R_j$-action on the first factor. This is a sheaf tensor product [def-pur-sheaf-tensor-product], and a complex since $(1\otimes d_P^{i+1})(1\otimes d_P^i)=0$ [def-weil-abstract-derived-category]. Regard all three complexes as $R_n$-complexes by the quotient actions [def-pc-sheaf-restrict-scalars]. Tensor the two maps of step 1 with the identity of $P^i$ to obtain cochain maps $\alpha:C_{n-1}\to C_n$ and $\beta:C_n\to C_1$: on local pure tensors they send $\bar c\otimes p$ to $\overline{tc}\otimes p$ and $\bar c\otimes p$ to $\bar c\otimes p$. These formulas commute with $1\otimes d_P$ and are $R_n$-linear.

### Original step 3

Owner: lem-pe-successive-quotient-flat-complex-sequence.

For each integer $i$, flatness in [def-pc-flat-sheaf-modules] means exactly that the sheaf functor $-\otimes_B P^i$ is exact. Apply this defining property to the $B$-module sequence of step 1. It gives $0\to C_{n-1}^i\xrightarrow{\alpha^i}C_n^i\xrightarrow{\beta^i}C_1^i\to0$ exact as $B$-module sheaves. It is exact as $R_n$-module sheaves too: by [def-weil-sheaf-of-modules-category], its kernels are the same sectionwise kernels and its cokernels the same sheafified sectionwise quotients, equipped with the inherited $R_n$-actions. The kernel-image equality and zero cokernel therefore concern the very same underlying abelian sheaves. Consequently $0\to C_{n-1}\xrightarrow{\alpha}C_n\xrightarrow{\beta}C_1\to0$ is a degreewise short exact sequence of $R_n$-complexes. This is a direct application of the exact-functor definition of flatness, not an inference from sectionwise flatness of $P^i(U)$.

### Original step 4

Owner: existing lem-weil-pbc-complex-ses-triangle; assembly step 3.

The site-size assumption makes $\operatorname{Mod}(R_n)$ abelian [def-weil-sheaf-of-modules-category]. Apply [lem-weil-pbc-complex-ses-triangle] to the degreewise short exact sequence from step 3 in this category. With $Q_n$ denoting its derived localization this gives a distinguished triangle $Q_nC_{n-1}\xrightarrow{Q_n\alpha}Q_nC_n\xrightarrow{Q_n\beta}Q_nC_1\xrightarrow{\delta}(Q_nC_{n-1})[1]$ in $D(R_n)$. In particular the connecting morphism is obtained in the category of $R_n$-modules itself; no lifting of a triangle from $D(B)$ is being asserted.

### Original step 5

Owner: lem-pe-restricted-kflat-tensor-identification for the comparisons; assembly step 5 for conjugating the connecting map.

For each $j$, symmetry of the sheafified balanced tensor gives an $R_j$-linear cochain isomorphism $C_j\cong P\otimes_B R_j$, sending $\bar c\otimes p$ to $p\otimes\bar c$; the inverse exchanges the factors back. The formulas respect balancing, restrictions and $1\otimes d_P$, so they extend from the presheaf tensors to their sheafifications [def-pur-sheaf-tensor-product]. By [lem-pur-derived-change-of-rings], $P\otimes_B R_j$ represents $K_j$ in $D(R_j)$ for the quotient $B\to R_j$. Termwise restriction to $R_n$ preserves quasi-isomorphisms: it retains the underlying abelian sheaf and maps [def-pc-sheaf-restrict-scalars], whose sectionwise kernels and sheafified cokernels compute cohomology [def-weil-sheaf-of-modules-category, def-weil-abstract-derived-category]. It also commutes with the shift because it retains the differential and its negative. Thus the three objects of step 4 identify in order with $\operatorname{Res}K_{n-1},K_n,\operatorname{Res}K_1$. Under the displayed tensor exchanges, $\alpha$ becomes $p\otimes\bar c\mapsto p\otimes\overline{tc}$ and $\beta$ becomes $p\otimes\bar c\mapsto p\otimes\bar c$, exactly the required second-factor maps. Conjugate $\delta$ by these object isomorphisms and their shifts. The resulting triangle is isomorphic to step 4, hence distinguished by the definition in [def-weil-abstract-derived-category]. The same construction works for any flat-term K-flat resolution, since only those two properties of $P$ were used. Neither completeness nor boundedness enters.

## Validation

Server srvcheck check_dag passed: no finding introduced by the sandbox or on its nodes. The first delivery dry run requested five further shared-tag comparisons against the server tree; I opened all five statements and added their explicit differences above. The repaired final dry run follows.
