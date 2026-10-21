# Stage-1 delivery: lem-sbc-ringed-site-perfect-projection-formula

## Files written

- `dag/nodes/sec-smooth-base-change/lem-sbc-ringed-site-perfect-projection-formula.json`: item, statement, split. The statement and its statement dependencies are unchanged. Mathlib verdict: no match.
- `dag/nodes/sec-smooth-base-change/lem-sbc-ringed-topos-sheaf-slice-derived-comparison.json`: new statement-only, unsplit. Mathlib verdict: no match. Canonical derived restriction comparisons for an arbitrary geometric morphism and arbitrary coefficient map, on arbitrary sheaf slices; it asserts no perfect-coefficient projection isomorphism.
- `citations.json`: 14 verbatim statement excerpts, one per step/node citation.

There are 1 new node and 0 Mathlib leaves. No unit record is changed: this item is a generic tool below the unit's key statement, not the key node itself. No Lean file, compiler, Lake, repository git command, shared-repository file, or launcher script was written or run.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint id and for projection-formula, perfect-complex and strictly-perfect terminology. The project has projection formula results for scheme étale/pro-étale morphisms and coefficient-extension functors; none states this arbitrary ringed-topos, arbitrary ring-map, unbounded-E theorem. The item's audit is empty; it supplies no existing declaration to attach. I also searched for the new node's sheaf-slice comparison and the relevant localization tags. K-injective restriction declarations are only ingredients and do not state the new node.

## WANTED

None. All sources used are present in the read-only repository.

## Findings and changes

The item is exactly Stacks Tag 0944 (`sites-cohomology.tex`, `lemma-projection-formula`, lines 13665–13712, including the adjoint-of-counit construction immediately before the lemma). Its statement needs no correction or STATEMENT-DISPUTED annotation. Neither boundedness of E nor flatness of the structural ring map is assumed in Stacks.

I retained the imported statement, prior search records, source, created metadata, chapter, unit, and blueprint ancestry. The sandbox initially held only brief markers, so there was no prior split/report/search log to resume. New searches were made only with msearch.py and their actual returned records are preserved in searches.jsonl and in the corresponding nodes. Each statement was tried in two natural-language phrasings, plus Loogle, LeanSearch and source grep. I read the search hits. The monoidal-adjunction hits provide underived lax/oplax structures; zeroth-derived and Tor hits do not give an unbounded sheaf projection theorem. The slice hits give underived pullback/overFunctor, general derived comparison transformations and compatibility of a derived adjunction with its localization, but not invertibility of the slice comparison or the required geometric identification. I read PushforwardContinuous.lean at overFunctor (59–84), PullbackContinuous.lean at the ordinary pullback adjunction and composition, and the general derived-adjunction comparison declarations. None is a one-line specialization of either statement.

The real gap in the existing infrastructure is its scope. `lem-weil-pbc-ringed-derived-slice-localization` and `lem-weil-pbc-ringed-slice-pullback-mate-normalization` assume the original morphism is presented by a continuous functor between the given sites. `lem-weil-pbc-ringed-projection-restriction` additionally assumes scheme pro-étale sites and invertible coefficient pullback. This item explicitly does not impose these hypotheses. The new helper handles the inverse image of a sheafified representable as a sheaf, not as a representable object of the original source site. It is an infrastructure lemma with no perfectness hypothesis and no projection-invertibility conclusion, so it neither restates the item nor transfers the whole proof to a new node.

The proof of 0944 passes from summands to finite free complexes tersely. I instead use the given termwise splittings and stupid-tail triangles directly. No claim that the individual term splittings are chain maps, no global projectivity of free sheaves as objects, and no global bound on local perfect representatives enters the argument.

## Supporting argument for the new statement-only node

Source read for the new node: `sites-modules.tex`, Tag 04IF, `lemma-localize-morphism-ringed-topoi`, lines 2704–2772. It constructs the slice square for **every sheaf** A and proves the actual underived module identity f_A* r_X = r_Y f*. I also read the small element-site statement `lem-weil-pbc-ringed-sheaf-slice-adjunction`; it supplies small presentations, exact restriction and its exact additive left adjoint. Stacks `sites-cohomology.tex` Tag 08FI, `lemma-restrict-K-injective-to-open`, gives the K-injective restriction argument, and Tag 0D6G, `lemma-restrict-direct-image-open`, is the representative calculation for a site-induced morphism. Those calculations apply verbatim to the small element-site presentation and 04IF's module identity. Tags 07A4 (`lemma-pullback-tensor-product`) and 07A7 (`remark-base-change`) fix the canonical pullback square and exchange-mate conventions, rather than an arbitrary choice of isomorphisms.

Concretely, for B=f^{-1}A, restriction to either element site has exact extension by zero as a left adjoint. For an acyclic complex Z in the slice, its extension by zero is acyclic, so maps from Z to r_X I are the same, by the adjunction on complexes and homotopies, as maps from an acyclic complex into I. They are null-homotopic when I is K-injective. Thus r_X I is K-injective. The ordinary identity r_Y f_* I = f_A* r_X I consequently computes beta on arbitrary unbounded complexes. This proves invertibility without requiring f_* to preserve K-injectivity.

For theta, use the ordinary commutation sigma of the inverse-image/extension-of-scalars square of 04IF. Pullback along any ringed-topos morphism preserves flat-term K-flat complexes, by `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`; in particular this holds for the two exact restriction morphisms. For a flat-term K-flat T, both sides of theta are therefore computed by the ordinary complexes f_A* r_Y T and r_X f* T (here each star is the **pullback** star in theta). Their comparison is sigma_T, and is invertible. Deriving sigma, rather than choosing unrelated local isomorphisms, fixes theta.

Finally use the ordinary adjunction Hom(f* M,I) = Hom(M,f_* I), and its slice version, with the 04IF identities. Both routes through their restriction square send a map to its same adjoint, since the slice structural ring map is precisely restricted f-sharp (04IF gives this formula). Derive this commuting adjunction square using the canonical derived-adjunction unit and counit comparison equations: Stacks `sites-cohomology.tex`, `lemma-adjoint`, explicitly invokes the formal `derived-lemma-derived-adjoint-functors` theorem. The global and slice comparison transformations are normalized on their K-flat and K-injective resolving classes as above, so deriving the underived square gives the commuting derived adjunction square. This is descent of the adjunction transformation; it does not assume that ordinary Hom out of an arbitrary K-flat complex computes derived Hom. This says exactly that beta is the exchange mate of theta. Evaluating the commuting bijection on the counit gives the displayed formula r_X(epsilon_E) theta_(Rf*E) = epsilon^A_(r_X E) Lf_A*(beta_E). The formula has source Lf_A* r_Y Rf*E and target r_X E, so it is typed for nonflat coefficient maps too. All these comparisons are natural on complexes and descend through quasi-isomorphisms. This supporting argument is recorded here, while the new DAG node remains statement-only as required.

## Not duplicates

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-sfb-left-exact-left-adjoint-slices: the latter gives an underived categorical slice adjunction and finite-limit preservation, not unbounded module-derived comparisons or their canonical mate.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-weil-pbc-ringed-derived-slice-localization: the existing statement assumes a continuous functor between the original sites; the new statement allows arbitrary geometric morphisms and slices at any sheaf.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-weil-pbc-ringed-slice-derived-comparisons: the existing statement assumes a continuous site functor and normalized site-object data, not arbitrary sheaf slices of an arbitrary geometric morphism.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-weil-pbc-ringed-slice-derived-mate-isIso: the existing statement assumes the site functor and a supplied normalized beta; it does not construct the arbitrary sheaf-slice comparisons.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-weil-pbc-ringed-slice-pullback-mate-normalization: the existing normalization only treats a continuous functor between the original sites and localization at its object V.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-weil-pbc-ringed-projection-restriction: the existing result is for scheme pro-étale sites and invertible coefficient pullback; the new result imposes neither and does not assert a projection-formula theorem or local detection clause.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-weil-pbc-ringed-slice-comparisons-shift: that result is shift normalization for a site-induced morphism with invertible coefficients; this one constructs arbitrary sheaf-slice derived comparisons and their mate.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-weil-pbc-ringed-sheaf-slice-adjunction: the latter provides element-site presentations and an exact underived restriction/extension adjunction, with no second geometric morphism or derived direct-image comparison.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-weil-pbc-ringed-slice-normalized-comparisons: the existing statement concerns tensor and internal-Hom restriction on one ringed site, not the derived adjunction of an arbitrary geometric morphism.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-coef-signed-single-dual-restriction: the existing statement concerns single-dual signs and tensor/internal-Hom comparisons, not direct image of a geometric morphism.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-coef-slice-hom-source-shift: the existing statement concerns the shift in derived internal-Hom's source, not slice base change for direct image.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-sfb-base-change-identity-open-restriction: the existing statement concerns a scheme morphism which is the identity on an open, with condensed coefficient objects; this one is for arbitrary ringed topoi and all sheaf slices.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-weil-pbc-element-restriction-hom: that statement concerns derived internal Hom and presentation equivalences of element restrictions; it has no second geometric morphism or derived direct-image slice comparison.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-weil-pbc-etale-localization-exchange: that statement concerns bounded-below abelian étale complexes on schemes, not unbounded modules with arbitrary structural ring maps.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-weil-pbc-etale-underived-exchange-restriction: that statement concerns underived abelian étale sheaves on schemes and their section formulas, not arbitrary ringed-topos derived comparisons.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-pur-kinjective-restrict-localized: that statement gives K-injective restriction alone, not the second geometric morphism, comparison and mate normalization.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-pur-kinjective-restrict-localized-universes: that statement generalizes the universe of K-injective restriction alone; it does not state the geometric derived-adjunction comparison.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-pur-kinjective-restrict-localized-adjunction: that statement gives an exact underived left adjoint to module restriction, not the geometric derived-adjunction comparison.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-pur-kinjective-restrict-localized-adjunction-universes: that statement generalizes the universe of the exact underived restriction adjunction, not the geometric derived-adjunction comparison.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs new-localized-restriction-extension-exists: that statement is existence of an exact underived extension left adjoint, not derived direct-image slice base change.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs new-localized-restriction-extension-exists-universes: that statement generalizes the universe of an exact extension left adjoint, not the new comparison or its canonical mate.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-exc-finite-coefficient-open-kinjective: that statement is K-injective preservation for a scheme open immersion and finite continuous-function coefficients, not arbitrary geometric morphisms and structural ring maps.

lem-sbc-ringed-topos-sheaf-slice-derived-comparison vs lem-dg-etale-injective-finite-cech-rows: that statement concerns split finite Čech rows for injective étale module sheaves, not geometric slice derived adjunctions.

## Review by NU

I read the item against 0944 and its canonical map 0B56, not merely against the blueprint. I read the chapter and unit records: sk-rem-rest has no proof steps to replace; the nearest blueprint ancestor's main-20261015 proof uses the integral lattice theorem followed by central localization. This item provides the already-seeded ordinary projection maps inside that integral construction. I searched the entire DAG and blueprint by projection formula, slice, 04IF and 08FI, and read the potential generic slice and projection-locality nodes. No blueprint node gives the general sheaf-slice helper. The chapter, unit route and ancestor are preserved.

Step 1 uses exactly the statement of ringed-projection-mate-exact: its exact additive F,G, shift compatibility, triangle-morphism clause and alpha_R=identity. Thus the formula being proved is the specified adjunct, with the correct unit value, and the unit/shift case is valid for any unbounded E and any structural map.

Step 2 uses naturality and additivity from that same statement. I checked the inverse F(p) alpha_H^{-1} G(i): both composites simplify using naturality and pi=identity, with the domains in the right order. It is a written elementary calculation, not a new lemma node. Finite biproducts are enough; nothing requires Rf_* to preserve infinite sums or global free sheaves to be projective.

Step 3 uses only degreewise splitting from strict-perfect-coefficient-package, the distinguished-triangle conclusion of degreewise-split-derived-triangle, the triangle-morphism clause of ringed-projection-mate-exact, and two-out-of-three from triangle-morphism-iso. I checked that Mod(R) is abelian in the chosen universe, the tail short exact sequences split in each degree, the base tail is zero, and the induction really descends through the finite interval. For a term supported in degree c, the convention is T^c[-c], as the shift definition requires. There is no need to split the complex as a complex. Natural isomorphisms from chosen strict models to P are sufficient, so a proof does not depend on a chosen representative.

Step 4 uses the **statements** of the package definition, element-restriction-hom, the new comparison, derived-tensor-pullback and exchange-tensor-coherence. I corrected an initial draft which attributed the equivalence between the element site of a sheafified representable and the ordinary localized module category to the sheaf-slice-adjunction statement: that statement alone did not say this. The delivered step cites element-restriction-hom, whose statement explicitly supplies this equivalence and identifies actual restriction. I checked the four edge labels in exchange-tensor-coherence: g and g' are the two slice morphisms, whose coefficient maps are identities, f=u and f'=u_A. The new lemma fixes theta as the comparison from the actual ringed square, not an arbitrary isomorphism, and beta as its exchange mate. Thus the coherence equation identifies the actual restriction of the actual projection arrow. It never asserts general base change for unrelated squares.

Step 5 uses exact-functor-complex-cohomology (natural in complexes), sheaf-cover-local-isomorphism and unbounded-derived-iso-cohomology. I wrote the roof argument to pass the natural cohomology comparison to derived arrows, rather than assuming a complex-only statement already quantified over derived arrows. The family of all chosen covering domains is small because the original site is small; its sieve covers each object. Applying the local-isomorphism criterion to underlying abelian sheaves is legitimate, and the inverse to an invertible linear map is linear. Cohomology detection is for the ordinary unbounded derived category, not a bounded-below surrogate.

For the new node I checked 04IF's arbitrary-sheaf and arbitrary-ring-map hypotheses and the representative argument written above; the canonical counit equation is typed explicitly. Its statement has no proof sketch, its proof and proof_deps are empty, and all its notions are defined inline or named. It is not a clause of the projection-formula item. Source tags and labels were checked in tags/tags. The off-unit statements are generic tools and are declared in split_report.tool_uses, with their actual uses; no top-level tool_uses was set by this delivery.

Small cases checked: P=0, P=R[n] for either sign of n, a split finite-projective term (without projectivity in the global sheaf category), a two-term complex with nonzero differential, identity u, zero coefficient ring, and a nonflat ring map of point topoi (Z to Z/2). The slice helper also works for A=terminal, A=initial, and for A not representable on the chosen site. These tests expose precisely why underived pullback exactness and representability must not be smuggled in. Bounds may differ between covering objects throughout. Every proof step is shorter than 2000 characters, and I checked that none hides a new sublemma beyond its named citations and written elementary calculations.

No mathematical statement dispute, source error, unfinished clause, or missing source remains. The new helper is intentionally unsplit for the next stage-1 item; the requested item itself has a complete one-level split.
