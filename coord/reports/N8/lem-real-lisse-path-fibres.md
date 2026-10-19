# Stage-1 delivery: lem-real-lisse-path-fibres

1. Files written

- `dag/nodes/sec-purity-real-sheaves/lem-real-lisse-path-fibres.json`: item, statement unchanged, split into ten proof steps; inherited searches retained and the actual new searches appended.
- No new nodes or Mathlib leaves. The proposed abstract existence node was removed after the dry run identified a newly synced existing basepoint-transport node.
- `citations.json`: 21 verbatim statement witnesses, one for every node in every proof step's `uses`. For readability and to retain all clauses used, the witnesses reproduce the complete cited statements.
- `searches.jsonl`: actual msearch log. Reading extracts and the construction script are under `source-notes/`; these are scratch material, not library changes.

2. Attachments

No full attachments. I read `CategoryTheory.PreGaloisCategory.nonempty_iso_of_fiberFunctor` in `WeilConjectures/Mathlib/CategoryTheory/Galois/Prorepresentability.lean:138-146`. Its sorry-map record has `s=false`, `ts=false`, and its body has no sorry. It proves only abstract path existence, so it does not attach this item or the entire existing basepoint-transport node. The latter also asserts adic and coefficient compatibility. No declaration is claimed to prove that complete package.

3. Literature wanted

None. All sources used are available locally. No literature was downloaded and no SGA route was used.

4. Problems found and repaired

The item was an unsplit, proof-empty compatibility package, not an attachment. Search by its exact blueprint tag in the project found no declaration. Searches for paths and transport located finite-cover infrastructure and special paths, but nothing proving all of the module, adic, scalar, arbitrary-automorphism and framework clauses. In particular the finite-cover paths in `BoundaryInertia.lean` do not constitute the full item.

Two possible citation errors were avoided. `thm-galois-fundamental` does not state existence of an isomorphism between different fibre functors, although its Stacks source does. The proof now cites the existence clause actually stated in `lem-wf-fibre-functor-basepoint-transport`, rather than taking it from `thm-galois-fundamental`. Also `lem-per-lisse-completed-system-comparison` concerns finite-free integral local systems, whereas the classical definition allows torsion in an integral model. Step 8 replaces the rational object by a free stable lattice before using that comparison; it does not assume that every initial integral model is free.

A general pro-etale lisse E-module need not come from a global integral lattice on a singular scheme. The item is smooth: step 9 invokes the existing smooth global-lattice theorem with the identity field extension. That theorem carries the normal/geometrically-unibranch route through Bhatt-Scholze 7.4.7 and 7.4.10. No normality or lattice claim was added to the item's hypotheses.

5. Work remaining

The cited dependency nodes retain their own independent stage status. No part of this item's natural-language argument is intentionally left unfinished; no Lean file or build was produced.

## Not duplicates

No new node remains. The first dry run found `lem-wf-fibre-functor-basepoint-transport`, which had become available in the shared DAG after the initial searches. I opened its full statement: it gives path existence, natural linear finite and adic transport, coefficient extension, identity/composition and loop conjugation. Step 1 now cites it, and the proposed abstract node was removed from the sandbox delivery. The item still needs its arbitrary scheme-automorphism equation and ordinary pro-etale/framework comparison, so it is not a duplicate or one-line application of that existing node.

Whole-DAG searches used `0BN5`, `0BND`, `fibre functors`, `fiber functors`, `nonempty_iso_of_fiberFunctor`, and the proposed id, with statement inspection of the hits. Blueprint searches used `fibre functor`, `two fibre`, `two fiber`, `fibre functors isomorphic` and `lisse transport`, across all chapters. The ancestor tool gives `p-real-operations`; the item's existing ancestry is retained and `same_as: []`. The unit key node is `p-real-operations`, so no unit record was edited. The search log and the useful explicit compatibility arguments were retained after removing the redundant dependency.

## Review by N8

I read the whole B-E delivery-error checklist against the node files and sources. The literature basis is Stacks `pione.tex`, Theorem 0BND (`theorem-fundamental-group`), particularly its separate second clause, and the abstract functoriality Lemma 0BN5 (`lemma-functoriality-galois`). For the finite-local-system bridge I read Stacks 03RV (`etale-cohomology.tex`, `lemma-characterize-finite-locally-constant`). For the finite tensor/stalk normalization I read Stacks 03EL (`sites-modules.tex`, `lemma-tensor-product-pullback`), including its functorial statement. I read Weil II (1.1.1) b)-d), pp. 146-147, and its fibre/representation convention (1.1.6), and Bhatt-Scholze Proposition 6.8.4(1),(4) and Lemmas 7.4.7, 7.4.10, including the nonnormal counterexample between those lemmas. The abstract path-existence proof and its precise hypotheses were also read in the project source and the Mathlib class declarations, as detailed above. The item's proof is honestly marked `by: agent`: the compatibility package is assembled explicitly from these constructions rather than quoted as a theorem of one document.

Step 1 uses the existence sentence actually stated in `lem-wf-fibre-functor-basepoint-transport` and the fibre-compatible equivalence in `thm-galois-lc-etale`. Only connectedness and geometric endpoints are needed for existence, so no Noetherian assumption is imported at this point. The node's functors are on finite locally constant sets; the equivalence transfers to finite etale covers, which is the item's convention. Independence from representing covers is written as the naturality square for the comparison isomorphism. This is not an appeal to the proof of the equivalence. The existing node states more of the classical package, but the following steps retain the explicit formulas needed to verify compatibility with the specified pro-etale realization.

Step 2 uses the finite-limit compatibility actually stated by `thm-galois-fundamental`, which includes the finite-locally-constant identification. Addition, zero and multiplication by a ring element are morphisms of underlying finite locally constant set sheaves. Both projection equations determine transport on a product, and every element of a constant finite set is given by a map from the terminal object. Thus the linearity and constant-coefficient assertions follow by the written equations, and the step is elementary. No tensor/adic theorem is hidden there.

Step 3 uses clause (3) of `lem-pod-lisse-tensor-and-scalar-extension`, which explicitly gives the scalar/stalk isomorphism on pure tensors, local constancy, and composite-extension compatibility. Its hypotheses hold for the finite quotient rings. The formula for a pure tensor follows from the set-sheaf map for each coefficient, and additivity extends it to the module. This is a two-line application, not a new node.

Step 4 uses the actual inverse-system, fibre and localized-Hom definitions of `def-pod-lisse-l-adic-sheaves`, and the finite complete module reconstruction of `lem-pod-adic-limit-finite-modules`. Transitions are sheaf maps, so every coordinate commutes with transport. I checked maps in the rational category as finite sums of integral maps tensored with scalars. That proves independence under rational isomorphisms and includes torsion integral models. Identity/composition and inverses are checked coordinatewise, not asserted without a formula.

Step 5 uses those same precise scalar-extension and common-stage definitions, the scalar-compatible fibre equivalence actually stated in `cor-galois-lisse-representations`, and completeness in `lem-pod-adic-limit-finite-modules`. The ramified extension uses level `ceil(m/e)`, rather than confusing powers of the two uniformizers. Equality is checked in each of these finite quotients. The algebraically closed coefficient assertion is at a common finite stage; it does not assert an inverse limit over coefficient fields.

Step 6 uses the natural fibre bijection `tau_P` actually given in `lem-galois-pi1-functoriality` and base-change compatibility in `thm-galois-lc-etale`. I checked the orientation: `h(p)=tau_b p_(h*P) tau_a^{-1}`, so its conjugated equation is precisely `tau_b p_(h*M)=h(p)_M tau_a`. These results apply to arbitrary scheme morphisms, including non-k-linear automorphisms. Iterates use actual composed projections, and the inverse automorphism supplies negative iterates.

Step 7 uses the normalization of actions explicitly in both clauses of `cor-galois-lisse-representations`. Evaluating the composite natural automorphism gives the displayed conjugation formula, and the earlier limit/localization construction respects that composition. This is elementary given the cited normalization and does not need a new conjugation lemma.

Step 8 uses the continuous-representation equivalence of the corollary and the finite-free stable lattice promised by `lem-pod-profinite-stable-lattice`. The group is profinite as stated in the corollary, the representation is finite-dimensional and jointly continuous, and the stable lattice has the required adic continuity. Those hypotheses are what permit using the finite-free integral comparison later; I did not use a mere definition as evidence for lattice existence.

Step 9 uses exactly the global lattice conclusion of `lem-a1-smooth-lisse-integral-lattice`, not only the etale-local lattice theorem. Its hypotheses hold with `K_0=K=k` and the given smooth separated finite-type X. `lem-weil-pbc-finite-type-over-noetherian` establishes the Noetherian hypothesis, since a field has only the ideals 0 and 1. `lem-per-lisse-completed-system-comparison` then supplies the finite-free etale tower equivalence, fully faithful rational realization, and specified pullback/scalar compatibilities. Full faithfulness supplies rationalized integral comparison maps, and step 4 proves their naturality. This establishes lattice independence without inventing an identification from a definition node.

Step 10 uses the actual pullback compatibility of that comparison at `Spec Omega`, which is also Noetherian and separated; the finite-cover splitting in `lem-galois-geometric-fibre` and the base-change/fibre equivalence in `thm-galois-lc-etale` identify each finite sheaf over the algebraically closed point with its constant fibre. Taking sections of a sheaf limit is componentwise by the limit's definition. The finite-free lattice gives the rational point fibre on localization. The final framework assertion uses exactly the ordinary module-pullback, point-fibre, naturality and coefficient-extension assertions of `lem-tw-lisse-rational-realization`. The named framework functor is applied only at `s=Spec k`; other geometric points use the explicitly stated analogous finite-tower interpretation. I did not apply the finite-type-k framework comparison to a geometric field not finite type over k, nor commute arbitrary pro-etale stalks with limits.

I checked zero sheaves and rank-zero lattices, X a geometric point, equal endpoints, identity paths, a path followed by its inverse, identity coefficient extension, ramified coefficient extension, torsion integral models with zero rational fibre, and inverse automorphisms. All formulas specialize correctly. The forbidden empty X is not needed for existence because geometric endpoints are assumed; the nonempty hypothesis is retained. There are no new definitions with data holes, no weakened statements, and no unreported statement disputes. Every non-elementary input is a cited node; no new unsplit node is delivered. Every step is under 2,000 characters, and I checked that the longer realization steps use existing statements rather than hiding a separate comparison lemma.

Generic off-unit uses are declared individually in `split_report.tool_uses`. They build the fibre-transport tool used by this unit's local Frobenius comparison and do not replace the unit's route. This report is my author review, not an independent review.
