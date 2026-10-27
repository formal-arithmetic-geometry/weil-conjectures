# Worker report: lem-sfb-noetherian-module-hom

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-module-hom.json: statement, split into ten steps; no Mathlib match; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-flat-coefficient-rhom-base-change.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-connective-perfect-sections-affine.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-ringed-site-nonpositive-derived-hom.json: statement, unsplit; no Mathlib match.
- citations.json: one entry for every step/node citation, quoting the cited statement verbatim.
- report.md and searches.jsonl: report and unmodified search-command audit log. Search-result text files retain the actual responses. The support-neighbourhood search was exploratory: no such node was created, since the reduction is elementary from existing statements.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag, module Hom representability, Noetherian and algebraic-space notions found no completed project declaration stating all clauses. Ordinary scheme module Hom declarations and unrelated cohomology declarations do not prove this representability theorem. No Lean files were written and no compiler was run.

## WANTED

None. All sources used are available in literature/stacks-project.

## Errors and changes

No statement dispute was found. The original statement matches Stacks Tag 08JY in quot.tex, in the situation of Tag 08JT. In particular it assumes relative flatness of G, not flatness or properness of f. Proper support is expressed using a proper closed carrier; the existing carrier/support comparison supplies the scheme-theoretic support convention used by the perfect-direct-image theorem.

The item was unsplit on arrival and there was no earlier sandbox proof or report. I retained its statement and inherited blueprint ancestry. The current blueprint literature/blueprint/latest (main-20261023-1620, commit 7284bb) places this in the direct-images proof's alteration prerequisite chain through stable curves, Hilbert and Quot. The item is not a key blueprint node. tools/blueprint_refs.py ancestor returns None for this deep prerequisite; the inherited from.node=null and its explicit from.place/via chain are retained, and the three new nodes extend that place with their precise use inside Tag 08JY. Searches by tag, notion, derived Hom, perfect complex and nonpositive found no equivalent blueprint statement, so same_as is empty. No unit realization was edited.

The reductions to a quasi-compact neighbourhood and to coherent modules were expanded in the proof instead of made into redundant new nodes. Existing perfect approximation, perfect duality and perfect tensor direct image are reused. The earlier affine-base Hom base-change node assumes f flat and does not supply the arbitrary relatively-flat-coefficient comparison needed here. I used the precise Tag 08JQ statement as a new unsplit prerequisite. The ringed-site Hom source was refined from broad section references to the exact statements Tags 06XS and 08JA. No SGA source or route was used.

## Unfinished work

The one-level split is complete. The three new genuine prerequisites intentionally remain statement-only unsplit nodes, as required for stage 1. Their proofs are not being claimed as completed Lean. There are zero Mathlib leaves.

## Mathlib and reuse searches

The command log contains the item's leanfinder, loogle, grep and leansearch searches, and five searches for each new prerequisite: two distinct leanfinder phrasings, loogle, grep and leansearch. The node records preserve the exact query text and actual responses. The item's previous creating-group search records are retained and my additional searches are recorded as well. All services answered; none was labelled unavailable. Hits were read: ordinary Scheme.Modules.Hom and scheme flatness/finite presentation do not represent relative Hom; LieAlgebra derived/baseChange is unrelated; affine spaces and ordinary module presentations do not represent a derived sections functor. DerivedCategory.TStructure orthogonality and single-complex results concern abstract morphisms, without the ringed-site internal-Hom bound and canonical comparison for an arbitrary nonpositive source. They do not specialize in one line to the full new statement.

Whole-DAG statement and Stacks-tag searches preceded creation, as did blueprint_refs searches and project Lean searches. No existing node carries Tag 08JQ or 08JX. The shared-tag candidates for the ringed-site lemma are distinguished individually below. The generic pro-etale lower-bound lemma has the right inequality but only on a scheme's pro-etale site, whereas the argument needs the small etale ringed site of an algebraic space. The two-term boundary lemma only handles a two-term source; P need not have that amplitude. The single fully faithful lemma handles sources concentrated in degree zero, and does not remove a negative tail.

## Review by NM

I read the entire proof of Stacks Tag 08JY in quot.tex and the situation Tag 08JT. For the new base-change node I read spaces-perfect.tex Tag 08JQ, including the precise displayed base-change map in its proof: the coefficient on the right is ordinary pullback. For the sections node I read quot.tex Tag 08JX and its proof, distinguishing clause (1)'s sections of the zeroth cohomology sheaf from clause (2)'s hypercohomology. Our node is clause (2) with an already perfect K. For the ringed-site node I read derived.tex Tag 06XS and sites-cohomology.tex Tag 08JA. Tag 06XS with a=b=0 identifies derived Hom with Hom of H0 and gives negative Ext vanishing; applying this after exact restriction to each site slice and using Tag 08JA gives the internal-Hom lower bound. This works for an arbitrary nonpositive source, with no projective resolution or lower boundedness assumption. The source's proof has a reversed inequality in its sentence about a truncated representative; its statement and the correct truncation calculation give terms zero above a, not below a. Our statement uses the correct cohomological inequalities.

I opened every statement in every step's uses list, not merely its source or title, and checked the following applications. citations.json quotes these actual statements without rewriting their hypotheses.

1. The affine-etale-cover and etale-open-image nodes give open quasi-compact chart images and the open subspaces used to choose U. The finite-type-support-pullback node gives closed support and its exact inverse-image behaviour after every test T. The proper carrier is quasi-compact over the quasi-compact base. Finitely many chart images cover it. The complement of the closed support and U_T form an open cover of X_T; maps glue uniquely with zero on the former. This checks restriction of Hom without a hidden extension-by-zero theorem and includes non-Noetherian T.
2. pqf-lem-locnoeth-lft is a scheme theorem: it is used only on the etale scheme charts in the locally-finite-type hypothesis. The qcqs-source-products node gives quasi-separated X and quasi-compact affine tests of f after the open restriction. The affine-chart-calculus node identifies finite-type modules with finite generated modules on charts. Over a Noetherian ring kernels of maps between finite free modules are finite generated, giving coherent and finitely presented F and G directly. B and the restricted X are qcqs; no unstated global finite-type assumption on the original X is introduced.
3. The Noetherian pseudo-coherent criterion applies to F[0], whose sole cohomology is coherent. The perfect-approximation node with a=-1 gives an isomorphism in every degree above -1. Thus H0(P)=F and all positive cohomology of P vanishes. I also read the approximation definitions and theorem Tags 08HI and 08HP in spaces-perfect.tex; the cited node really supplies the morphism, not just existence of an unrelated perfect object.
4. The strict-perfect definition supplies a local bounded finite-projective model. Its exact positive tail splits downwards from the highest nonzero projective term, leaving a nonpositive finite-projective model. The etale-module-functor definition specifies tensor pullback, whose right exactness identifies the cokernel in degree zero with h*F. This is the written local calculation rather than an assumed flat base change. It also proves preservation of perfectness directly and uses the canonical map from u, so identifications glue. I checked the sign at degrees -1,0.
5. The new nonpositive-derived-Hom node is applied with E=P_T and M=G_T. Step 4 verifies its positive-cohomology vanishing hypothesis; its statement supplies both the Hom bijection and the internal-Hom lower bound. The bijection is precomposition with the canonical map to H0, so it commutes with pulling back a module map and the approximation u.
6. Perfect duality explicitly states that P dual is perfect and RHom(P,G) is its derived tensor with G. The proper-carrier-support node equates our finite-type-carrier support condition with the support convention needed for the tensor-perfect node. The latter's statement allows f merely locally finite type and quasi-separated, and requires Noetherian B and a bounded coherent termwise relatively flat coefficient with proper support. G[0] satisfies every one of these hypotheses, by steps 1 and 2 and the original assumptions. I read Tag 0DKK and its reduction to Tags 08JJ and 0DKJ as well.
7. The new Tag 08JQ node requires qcqs f, perfect P, and relatively flat quasi-coherent G, all established. It permits arbitrary algebraic-space base change, hence every scheme test, and explicitly gives ordinary G_T on the right. No inference Lh*G=G_T is used.
8. The negative-vanishing node is about a left exact additive functor between Grothendieck categories on D+. The actual direct image is a right adjoint by the etale-module-functor statement, and module categories are Grothendieck by the K-injective-resolution-existence statement. The connective input from step 5 lies in D+, so the cited bound applies even though the surrounding notation is unbounded. It gives the universal bound needed for step 10.
9. The global-RHom-sections statement is the full H0RΓRHom=derived-Hom formula on any small ringed site. The enlarged-etale-ringed-site model supplies actual ringed-topos maps for these algebraic-space morphisms. The derived-pushforward-composition node allows arbitrary small ringed topoi and unbounded inputs, so applying it to f_T and global sections does not require a missing bounded or small-index colimit hypothesis. The canonical maps in these statements and in step 7 supply the natural isomorphism of functors, rather than only an equality of sets at each T.
10. The sections node applies to perfect K by step 6 and its universal negative-cohomology hypothesis by step 8. It gives both affine representability and finite presentation. Composing its bijections with the preceding canonical identifications gives all clauses for the original Hom functor, including tests before restriction to U.

I checked delivery-errors B through E against the written files. Every non-elementary input has a statement node in uses, proof_deps is its exact union, definitions supply only their stated constructions, and no new node repeats the item or one of its conclusions. The three nodes isolate distinct general inputs (arbitrary base change, standard-t-structure Hom, and perfect-complex sections); the item's proof still performs the approximation, perfectness argument and identifications. There is no long step exceeding 2000 characters. Each new node has explicit objects, scope, derived conventions, source and blueprint metadata. In particular the base-change node requires no properness, the sections node uses universal rather than merely basewise connectivity, and the nonpositive-Hom node is on arbitrary small ringed sites.

Small-case checks: if X is empty or F or G is zero, the Hom functor is the singleton represented by B, and the reductions and K=0 agree. For X=Spec A and F=A/(r), G=A, the functor is the annihilator of r after base change, represented by the affine finite-presentation equation rx=0; projectivity of F is not required. For E=A[1] the new Hom bijection has zero on both sides, while positive internal Ext degrees are allowed, confirming the shift direction. For E=[A --r--> A] in degrees -1,0 the degree-zero group is Hom(A/(r),M), not Hom(A,M). A nonflat test T is permitted: the local projective model computes P_T, and the base-change lemma uses ordinary G_T. Over k[t], K=(k[t]/(t))[0] fails the sections lemma's universal hypothesis after pullback to t=0 because H^-1 appears; this confirms the hypothesis is stronger than having no negative cohomology just on B. Finally a nonproper f such as an affine line with a coefficient supported at a proper closed point is allowed; the proof only needs properness of that support.

## Not duplicates
lem-sfb-ringed-site-nonpositive-derived-hom vs def-per-ordinary-kummer-first-chern: defines a Kummer Chern class for invertible modules with torsion coefficients; it has no arbitrary nonpositive-source Hom comparison.

lem-sfb-ringed-site-nonpositive-derived-hom vs def-sc-ext-sheaf: defines Ext using resolutions for two degree-zero modules on a scheme; our source E can have arbitrary negative cohomology on an arbitrary ringed site.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-pc-derived-pullback-evaluation-sections: compares pullback of evaluated derived sections under scheme maps; it asserts neither a t-structure lower bound nor reduction of a nonpositive source to H0.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-pc-derived-tensor-hom-sections-unit: identifies derived sections with morphisms from the tensor unit and normalizes currying, without the nonpositive-source reduction.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-pur-derived-internal-hom-shift-comparison: compares both argument shifts of internal Hom; it imposes no cohomological bound and proves no truncation bijection.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-pur-derived-internal-hom-shift-left: gives the left-shift isomorphism for RHom, without either vanishing or the H0-source Hom bijection.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-pur-derived-internal-hom-shift-right: gives the right-shift isomorphism for RHom, without either vanishing or the H0-source Hom bijection.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-pur-hom-complex-resolution-shift-comparison: compares shifts of functorial K-injective representatives, not truncation or t-structure bounds.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-sc-global-hom-shifted-hypercohomology: compares shifted global Hom and hypercohomology on schemes; it has no nonpositive-to-H0 comparison.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-sc-restricted-global-hom-shifted-equiv: compares scalar-restricted global Hom with shifted derived morphisms for schemes, without a cohomology-sheaf bound.

lem-sfb-ringed-site-nonpositive-derived-hom vs def-weil-pbc-adic-global-derived-hom: defines pro-etale global derived Hom and its scalar action; it asserts neither our vanishing nor our canonical truncation bijection.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-weil-pbc-derived-hom-sheaf-comparison-lisse: compares etale and pro-etale local derived Hom for bounded lisse sources and bounded-below targets; our lemma concerns any small ringed site and any nonpositive source.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-weil-pbc-derived-single-fully-faithful: only treats sources and targets both concentrated in degree zero; our source may have a nonzero arbitrarily long negative tail and we also bound internal Hom.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-weil-pbc-proetale-internal-hom-lower-bound: gives a more general inequality only on a scheme pro-etale site; it does not apply to an algebraic-space small etale site and does not state the canonical Hom-from-H0 bijection.

lem-sfb-ringed-site-nonpositive-derived-hom vs def-coef-hom-zero-cycle-class: defines the representative normalization of a zero-cycle class, without the nonpositive-source reduction or internal-Hom bound.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-coef-etale-hom-transpose-exact: proves shift/exactness coherence of an already given coefficient-Hom comparison, rather than a t-structure bound or truncation bijection.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-coef-scalar-hom-zero-compatibility: normalizes the external scalar Hom adjunction under comparison, rather than killing the negative tail of a nonpositive source.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-weil-boundary-evaluation-currying: proves evaluation/currying identities for exceptional inverse image and duality with finite coefficients; it gives no nonpositive-source t-structure statement.

lem-sfb-ringed-site-nonpositive-derived-hom vs def-sfb-space-affine-global-hom-cohomology: normalizes global Hom/cohomology comparisons over an affine base; it does not identify Hom(E,M) with Hom(H0E,M) or bound internal Hom.

lem-sfb-ringed-site-nonpositive-derived-hom vs def-sfb-space-affine-global-sections: defines scalar derived sections, its adjunction and cup product over an affine base, without our Hom vanishing and truncation result.

lem-sfb-ringed-site-nonpositive-derived-hom vs def-sfb-space-affine-hom-comparison: defines a global-Hom pullback arrow over affine bases and expressly claims no isomorphism; it supplies neither nonpositive-source truncation nor its vanishing.

lem-sfb-ringed-site-nonpositive-derived-hom vs def-sfb-space-affine-sections-compositors: specifies composition of derived sections and direct image, and the affine structure-module insertion; it is not a Hom t-structure lemma.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-sfb-component-slice-hom-comparison-test: tests component-pullback internal-Hom comparison over w-contractible schemes by local derived morphisms; it gives no Hom truncation or connective bound.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-sfb-derived-internal-hom-sections-model: gives K-injective Hom representatives and identifies their global cohomology with derived morphisms in every degree; it does not remove negative source cohomology or give the bound.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-sfb-module-object-ringed-site-derived-comparison: compares condensed module-object and ordinary ringed-site internal Hom on a pro-etale scheme; it is not a nonpositive-source truncation theorem.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-sfb-reduction-single-cohomology-normalization: normalizes multiplication-by-n derived scalar reduction and single-cohomology complexes; our arbitrary E can have multiple negative cohomology groups and no n is present.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-sfb-ringed-global-hom-cup-comparison: relates a cup-product comparison on global Hom to the action of global sections on derived morphisms, without cohomological bounds or a source truncation bijection.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-sfb-two-term-derived-hom-boundary: only handles the specific two-term source [M→F] in degrees -1,0 and its Ext1 boundary; our E may have arbitrary negative amplitude and we also bound internal Hom sheaves.

lem-sfb-ringed-site-nonpositive-derived-hom vs def-pur-external-rhom-pairing-interface: defines external pairings, representative models and signed-cone assertions, not the nonpositive-source truncation bijection.

lem-sfb-ringed-site-nonpositive-derived-hom vs def-pur-good-truncation-normalization: only defines the normalization for complexes with all cohomology except H0 zero; our E may have nonzero negative cohomology.

lem-sfb-ringed-site-nonpositive-derived-hom vs def-pur-ringed-site-zeroth-hypercohomology: defines H0 of derived global sections; it states neither a truncation bijection nor internal-Hom vanishing.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-pur-degree-zero-derived-map-gluing: glues maps of complexes locally concentrated in degree zero on schemes with constant finite coefficients; our E need only be nonpositive on any ringed site.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-pur-external-rhom-derived-braiding: proves the representative compatibility of derived tensor braiding; no t-structure or truncation Hom comparison is stated.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-pur-external-rhom-signed-cones: proves cone coherence for signed external pairings subject to a supplied shift structure; it gives neither of our conclusions.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-pur-global-hom-evaluation-model: identifies a global Hom representative and its evaluation transpose with bounded flat source on a scheme, without the H0-source reduction or internal-Hom lower bound.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-pur-good-truncation-exact-normalization: requires all cohomology except degree zero to vanish; our source may have arbitrary negative cohomology and need not be isomorphic to H0E.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-pur-hom-complex-global-homotopy: identifies ordinary Hom-complex H0 with morphisms in the homotopy category; our result is in the derived category and uses a nonpositive-source hypothesis.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-pur-hom-complex-hypercohomology: identifies hypercohomology of a K-injective-target Hom complex with homotopy morphisms, without truncation or a connective bound.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-pur-hom-kflat-into-kinjective: proves K-injectivity of an internal Hom representative, not t-structure vanishing or the Hom(H0E,M) bijection.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-pur-rhom-global-sections: identifies H0RΓRHom with derived Hom, but gives neither the Hom(H0E,M) bijection nor the internal-Hom lower bound.

lem-sfb-ringed-site-nonpositive-derived-hom vs lem-pur-vector-frame-integration-site-descent: glues coordinate traces for finite-coefficient vector-bundle integration, not arbitrary ringed-site nonpositive-source Hom.
