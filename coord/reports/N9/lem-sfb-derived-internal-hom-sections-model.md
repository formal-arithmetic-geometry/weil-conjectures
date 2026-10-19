# Worker report — lem-sfb-derived-internal-hom-sections-model

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-derived-internal-hom-sections-model.json`: existing statement, now split into six steps; no Mathlib match for the whole statement. Statement, statement dependencies, chapter, unit, source and existing blueprint provenance are unchanged. Added current, actually executed Mathlib searches and explicit off-unit tool declarations.
- `citations.json`: one literal quotation for every node used by every proof step (17 entries).
- `report.md`: this report. `prepare_split.py` is sandbox-only preparation scratch and is not a delivered project file.

New nodes: **0**. New Mathlib leaves: **0**. No unit file changed: this item is a child of the unit's detail lemma, not its statement node.

## Attachments

None. Searched the item id, the exact blueprint docstring tag, and the concepts `internal hom`, `RHom`, `Hom complex`, and K-injectivity in the named source checkouts. The slopmaster2 `CategoryTheory/DerivedCategory/Monoidal/Closed.lean` explains at lines 75–78 that comparison with the concrete Hom-complex model is further work. Its abstract derived-adjunction API and the master finite-/module-coefficient `Derived/Hom.lean` define right adjoints, but do not give the arbitrary-ringed-site Hom-complex model and its full derived-global-sections complex. No project declaration states all clauses of this item without sorry. Master is reference material only and has not been treated as a finished proof.

## WANTED

None. All mathematical sources used are present in the shared literature checkout.

## Findings and corrections

There is no statement dispute and no statement correction. The imported statement is true even with an arbitrary nonflat source, but one must not infer that its sheaf Hom complex is K-injective. Tag 0A96 only gives that conclusion for a K-flat source. The proof handles this by comparing with a K-flat resolution twice: both sheaf Hom and ordinary global Hom are quasi-isomorphic to the K-flat-source model. A natural comparison square with derived sections then proves the full complex statement, not just the H⁰ version of Tag 08JA.

The parent blueprint proof's notation `cHom` is underived-looking, whereas its current corrected DAG statement uses derived internal Hom. This child explicitly proves the comparison with the abstract right adjoint; it does not assume ordinary underived Hom computes derived Hom for a nonprojective coefficient module. No parent file was changed.

## Not duplicates

No new node is proposed, so there are no new/existing pairs to distinguish. Before drafting I searched all DAG node statements and sources for 08J7, 08JA, 08J9, 0A95, 0A96, K-flat resolutions, global Hom complexes, total tensor/Hom, and representative independence. I also ran `tools/blueprint_refs.py ancestor` for the item and whole-blueprint searches for `internal hom sections`, `08J7 08JA 08J9 0A96`, `K-injective`, `Hom complex`, and `internal hom`. The nearest ancestor is `det-lem-int-ext-formula`. None of the other blueprint statements supplies this entire item. The generic existing nodes used below supply the smaller ingredients; in particular the existing `lem-sc-derived-internal-hom-adjunction` only concerns a scheme, so it cannot be applied to this arbitrary site. Its generic helper `lem-sc-derived-hom-tensor-total` does have a ringed-site statement and can be reused.

## Mathlib search assessment

Ran the required msearch wrapper with N9 and this item's id, using LeanFinder twice with distinct phrasings, LeanSearch, two Loogle patterns, and grep in Algebra/Homology and CategoryTheory/Sites. Every new entry in the node records the executed tool and exact query text. All services returned successfully; no unavailable service was converted into a negative result. Existing search records are retained.

Read the returned types and Mathlib source `CategoryTheory/Sites/SheafHom.lean:226–263` and `Algebra/Homology/DerivedCategory/KInjective.lean:41–85`. The former supplies an underived sheaf of types and its sections; the latter supplies the generic K-injective localization bijection, already an existing Mathlib leaf `lem-weil-pbc-kinjective-hom-derived`. Neither supplies the internal sheaf-Hom/tensor comparison on the unbounded derived category or the full complex of derived sections. The light condensed closed-structure hits concern underived constant-ring sheaves on a special site. The ordinary sheaf pullback adjunctions and bounded-below injective resolution Ext hits also do not state this item. No new node or duplicate Mathlib leaf was created.

## Review by N9

I read the current chapter record and `sk-lem-int-ext` unit, then the statement and proof of `det-lem-int-ext-formula` in the current main-20261015 blueprint. This item serves proof (2), the identification of global derived Hom with derived sections used to lift the support/open adjunctions. Its general ringed-site statement is a tool below that route and does not replace any unit step. All off-unit generic tools are declared in `split_report.tool_uses` for maintainer review.

For the item's mathematics I read `sites-cohomology.tex` Section 08J7 (`section-internal-hom`), Lemmas 08J9 (`lemma-internal-hom`), 08JA (`lemma-section-RHom-over-U`), 0A95 (`lemma-RHom-well-defined`), 0A96 (`lemma-RHom-from-K-flat-into-K-injective`), 06YS (`lemma-K-flat-resolution`), 0A90 (`lemma-compose`), and Equation 0A8Z (`equation-global-cohomology-hom-complex`). I checked the tag/label mapping in `stacks-project/tags/tags`. I also read `derived.tex` Definition 070H and Lemma 070I, and `injectives.tex` Theorem 079P, whose functoriality is needed for the natural comparison to derived sections. There are no new-node sources to review and no forbidden SGA reference.

Step 1 uses exactly the existing statements `lem-pc-kflat-resolution` (any sheaf complex has a K-flat resolution), `lem-pur-rhom-well-defined` (quasi-isomorphism in the source and between K-injective targets induces a sheaf Hom quasi-isomorphism), `lem-pur-hom-kflat-into-kinjective` (the K-flat/K-injective Hom complex is K-injective), and `def-pur-derived-internal-hom` (the descended bifunctor with independence of representatives). I opened all four nodes and checked their hypotheses. The source resolution is P→A, so the contravariant arrow is Hom(A,J)→Hom(P,J). No K-flatness is imposed on A. This also checks the direction of the comparison, often easy to reverse.

Step 2 uses `lem-weil-pbc-kinjective-hom-derived` twice, with K-injective targets C and J, and `lem-pur-hom-complex-global-homotopy` twice, which gives ordinary H⁰ of global Hom for any two complexes. It uses `lem-sc-derived-hom-tensor-total` for its full generic ringed-site tensor/Hom formula, not the scheme-only adjunction node. I read the statement of each of these nodes. The remaining tensor-order issue is written out using the differential of `def-pc-tensor-complex-sheaves`; the Koszul swap has inverse itself and commutes with both differential summands by the displayed parity identities. Thus it represents the exact K⊗ᴸN convention in the item. Arbitrary unbounded test complexes B are permitted in every cited statement. Naturality in B and J is part of the cited global-Hom and total-Hom statements, and passes through localization.

Step 3 cites no node: it writes the uniqueness-of-representing-object argument as explicit inverse maps f and g obtained from the two natural bijections. The equations θ(a)=f∘a and θ⁻¹(b)=g∘b immediately give fg=1 and gf=1. Thus it is elementary rather than an uncited appeal to a general Yoneda theorem or to the mere full faithfulness of Yoneda. The same equations imply naturality in M; the precomposition bifunctor from step 1 supplies the contravariant first-variable maps when K changes. This handles the word “any” in “any right adjoint”.

Step 4 reuses `def-pur-hom-complex`, `lem-pur-hom-complex-global-homotopy`, `def-pur-kinjective-complex`, and `lem-weil-pbc-kinjective-hom-derived`. Their statements provide the differential, the H⁰/homotopy identification, the null-homotopy definition, and the localization bijection respectively. I checked the Hom/shift formula: after shifting by n both differentials in degree a are (-1)^n d_J f − (-1)^a f d_T. The argument that J[n] is K-injective is written out by shifting an acyclic source, so a shifted-target K-injective theorem is not being smuggled in. The resulting Hⁿ comparison is natural, and on the map induced by r it is precomposition with the invertible Qr. This proves global Hom(r,J) is a quasi-isomorphism even though Γ need not preserve arbitrary quasi-isomorphisms. In particular this step avoids assuming exact products or exact global sections.

Step 5 uses the unbounded derived-global-sections definition in `def-pur-ringed-site-zeroth-hypercohomology`, the functorial resolution transformation actually stated in `prop-pur-kinjective-resolutions-exist`, and the homotopy-equivalence conclusion actually stated in `lem-weil-pbc-kinjective-hom-derived`. I opened those statements, including the functoriality clause of the resolutions node. For a K-injective E, E→I(E) is between K-injectives, so applying Γ preserves its homotopy inverse. The comparison δ_C is therefore invertible. Both horizontal arrows of the displayed naturality square are invertible for different, explicitly supplied reasons: ordinary sections by step 4, derived sections by the sheaf quasi-isomorphism in step 1. This proves δ_B is invertible and, since δ itself is natural before choosing P, gives full-complex naturality for arbitrary source chain maps without demanding a functorial K-flat resolution.

Step 6 uses `def-pur-hom-complex` for its product terms, signed differential and pre/postcomposition maps, and `def-pur-sheaf-hom` for its explicit global-sections-equals-module-morphisms clause. I read that latter clause rather than deriving a global formula merely from a sheafification definition. Γ=Hom(O,−) commutes with products by the elementary product universal property. The resulting term identification respects the displayed differential, so this identifies complexes rather than only graded objects. The final all-degree cohomology assertion follows from the already proved comparison and step 4.

I checked the small cases K=0, M=0, and the trivial ringed topos: all complexes and groups vanish and the representing-object calculation forces the arbitrary right adjoint's value at zero to be zero. For a point site and an arbitrary commutative ring, the argument becomes the usual unbounded module-Hom computation into a K-injective. A torsion module such as Z/2 in degree zero confirms that source flatness must not be assumed and underived degree-zero Hom into M is insufficient; the resolution target remains essential. An unbounded acyclic source gives an acyclic global Hom complex by the all-degree localization calculation, which checks the delicate nonbounded case. Negative n is covered by the same shift and parity identities. No small-site object U or terminal object is assumed: all global sections are Hom(O,−), so the proof also applies to sites without a terminal object.

Against B–E of delivery-errors: the only delivered node is the existing item; there are no new elementary, duplicate, clause-restatement, hollow-definition or unsearched nodes. Every non-elementary ingredient above is a cited existing statement. The six steps contain the actual adjunction and derived-sections argument rather than relocating either clause to a child. There is no extra finiteness, boundedness, flatness, scheme, constant-coefficient or exact-product hypothesis. I corrected the initial quotation choices in `citations.json` to include the localization bijection where used, rather than quoting only its homotopy-equivalence corollary. All 17 quotations were then checked as literal substrings of the cited statements. No known mathematical gap remains.

## What could not be finished

Nothing mathematical remains in this one-level split. The independent second reader must perform their own review and delivery; this worker runs only the required no-push dry run.

## Second reading by N9

- Item statement: checked every hypothesis and clause against Stacks `sites-cohomology.tex`, Section `section-internal-hom` (08J7), Lemmas `lemma-internal-hom` (08J9), `lemma-section-RHom-over-U` (08JA), `lemma-RHom-well-defined` (0A95), `lemma-RHom-from-K-flat-into-K-injective` (0A96), and the existing definition nodes; verdict: faithful for arbitrary small ringed sites, unbounded complexes, arbitrary source representatives, and all integer shifts.
- Step 1: checked K-flat resolution, quasi-isomorphism invariance, K-injective Hom, and representative independence against the four cited node statements; verdict: the precomposition direction and hypotheses are correct and no flatness of the original source is smuggled in.
- Step 2: checked each displayed adjunction bijection against the K-injective localization, global Hom/homotopy, total tensor/Hom, and tensor differential statements; verdict: all cited statements supply the claimed maps, the Koszul swap supplies the stated tensor order, and naturality covers arbitrary test complexes.
- Step 3: checked the explicit two-sided inverse construction against the Yoneda uniqueness sentence in 08J7; verdict: the inverse equations prove the isomorphism and its naturality without citing an unstated theorem.
- Step 4: checked the Hom-complex differential, shift signs, shifted K-injectivity, and all-degree localization comparison against the cited Hom, K-injective, and localization statements; verdict: the parity calculation covers positive and negative integers and does not assume exact global sections.
- Step 5: checked the natural K-injective resolution comparison and its square against `def-pur-ringed-site-zeroth-hypercohomology`, `prop-pur-kinjective-resolutions-exist`, and the localization statement; verdict: the comparison is invertible first for the K-injective model and then for the arbitrary source by two-out-of-three, with naturality retained.
- Step 6: checked products, global sections of sheaf Hom, the signed differential, and the final cohomology identification against `def-pur-hom-complex` and `def-pur-sheaf-hom`; verdict: the result identifies complexes in every degree, including the zero and negative-degree cases.
- New nodes: none; there are no new-node statements or searches to review, and all dependencies are existing DAG nodes.
- Edge cases: checked zero source/target, the point site over an arbitrary ring, a nonflat torsion source such as `\\mathbf Z/2`, an unbounded acyclic source, and negative shifts; verdict: the statement remains meaningful and the proof uses the K-flat resolution where required.
- Searches and citations: checked the recorded Mathlib searches and every citation quote as a literal substring of its cited node; verdict: searches are recorded with successful tool results and no Mathlib declaration supplies the full ringed-site statement.

Changes made in this second reading:

1. Added `[def-weil-abstract-derived-category]` after “derived category of abelian groups” so that this notion is explicitly tied to its existing definition node.
2. Left the six proof steps and all existing citations unchanged after checking their hypotheses and directions.
3. Added this second-reading audit; no new node was created, no source dispute was found, and no Lean or build tool was run.
