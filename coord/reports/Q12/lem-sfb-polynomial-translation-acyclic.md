# Stage-1 delivery: lem-sfb-polynomial-translation-acyclic

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-translation-acyclic.json`: item, statement unchanged, five-step split, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-ind-unipotent-procyclic-difference.json`: one new statement-only analytic obligation, status unsplit, no Mathlib match.
- `citations.json`: one verbatim statement quotation for each node cited in each proof step.

One new node; zero Mathlib leaves. Auxiliary `write_split.py` and the unmodified search log are sandbox research material, not DAG deliveries.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item's blueprint tag, polynomial translation/invariant terminology, and nilpotent/procyclic comparisons found no project declaration giving this item. The actual procyclic declarations in `RepresentationTheory/DiscreteModule/Procyclic.lean`, lines 617–669, concern discrete continuous ell-primary modules, rather than the present norm-coefficient internal modules, and therefore do not attach.

## WANTED

WANTED: a precise reference for the ordinary internal condensed derived two-term difference model for countable increasing unions of finite-dimensional unipotent norm representations of Z_ell, with a commuting profinite action, for ALL continuous E- or noncomplete Omega-valued coefficients; for `lem-sfb-ind-unipotent-procyclic-difference`.

The local main-20261015 direct-images proof paragraph (3) delegates the open-immersion coefficient theorem; it does not prove the analytic comparison needed here. The new node is explicitly an agent-formulated obligation, and the item has proof_origin.by = agent. Neither the blueprint nor a Stacks tag is claimed to prove this missing analytic result. No SGA source is used. The direct delivery brief permits recording the missing reference here rather than modifying literature/LIST.md.

## Audit findings and corrections

The imported item had no proof. Its statement is retained verbatim, including both fields, all profinite parameters, the ordinary internal action category, the unbounded polynomial direct sum, and rank-zero/spectator cases. No STATEMENT-DISPUTED was found.

The apparent shortcut through `lem-sfb-dense-lattice-derived-invariants-comparison` is circular: that node uses `lem-sfb-trivial-ladic-derived-exterior`, which uses `lem-sfb-polynomial-derived-bar-comparison`, which uses this item. We do not cite any of them. Nor do we infer acyclicity of a filtered colimit from finite-stage acyclicity. Finite-degree translation modules are generally NOT acyclic: even constants with trivial rank-one action can have degree-one classes. The new comparison is for the actual sheaf colimit; its analytic content remains visible as an unsplit obligation.

The new node differs substantially from polynomial acyclicity: it treats a single procyclic factor on arbitrary compatible nilpotent finite-dimensional systems, and identifies its entire derived object with a generally nonacyclic two-term complex. It does not assume a surjective difference operator. The item's finite-difference contraction and induction establish the additional polynomial-specific content. For D=0 it predicts the two nonzero terms [M ->0 M], not vanishing. This prevents turning the item into “apply a renamed acyclicity lemma.”

The existing blueprint ancestor command returns None for this imported descendant chain. The item's existing null from.node and via chain are retained, and the new node has the same ancestor with the item prepended to via; its from.place is precise. Searches of the entire blueprint for polynomial translation, nilpotent, procyclic, unipotent, ind-unipotent and difference found no statement of the new node.

## Unfinished work

The new analytic obligation is intentionally not split in this delivery. In particular this delivery does not claim to have supplied a proof of the noncomplete-coefficient ind-unipotent comparison. This is one-level stage-1 decomposition, not a finished Lean theorem. No Lean was written or compiled.

## Not duplicates

lem-sfb-ind-unipotent-procyclic-difference vs lem-exc-procyclic-two-term: the latter assumes a finite ell-primary coefficient ring and a discrete continuous module; the new node uses ordinary internal norm-coefficient modules and a sheaf colimit of nilpotent norm representations, retaining an arbitrary commuting profinite action.

lem-sfb-ind-unipotent-procyclic-difference vs lem-sfb-dense-lattice-derived-invariants-comparison: the latter compares finite-dimensional lattice representations with a dense discrete lattice and is an ancestor depending on this item; the new node treats a rank-one sheaf colimit directly and does not use that comparison.

lem-sfb-ind-unipotent-procyclic-difference vs lem-sfb-polynomial-translation-acyclic: the item is polynomial positive-degree vanishing for any lattice rank; the new node is a rank-one derived difference model on arbitrary finite-stage nilpotent systems and generally has nonzero degree one.

lem-sfb-ind-unipotent-procyclic-difference vs lem-per-normal-subgroup-ind-unipotence: the latter is closure and augmentation-ideal structure in the discrete continuous category, not a norm-coefficient derived computation.

lem-sfb-ind-unipotent-procyclic-difference vs lem-sfb-normed-scalar-profinite-hom-acyclic: the latter concerns derived internal Hom into the scalar ring, not invariants on sheaf colimits of representations.

No new Stacks tag is attached, so there are no same-tag pairs. The generic exact-inflation composition theorem and product-action inflation theorem already exist and are reused; no duplicate homological node is created.

## Review by Q12

I read the current main-20261015 chapter description, the sk-thm-sf-ctf-stability unit, and paragraph (3) of sk-thm-sf-ctf-stability-direct-images.proof.md, along with the item and the polynomial-bar parent. This delivery serves the delegated analytic step underneath the existing open direct-image argument; it does not replace the unit route. For the new rank-one node I read those same local sources and the existing procyclic statement and upstream declarations. None supplies its full noncomplete, all-continuous internal assertion: that is exactly the WANTED obligation, not an invented attribution. I read the full statements of both existing lemmas used in step 5 and of the new node, and checked that each quoted assertion is actually in its statement.

Step 1 needs no non-elementary node: invariants for the trivial group are literally the identity, so no resolution changes a degree-zero module. This covers every spectator count and r=m=0.

Step 2 checks the hypotheses of the new node, not its proof. The total-degree stage is finite-dimensional; its inclusions are injective, all translations preserve degree, differentiation lowers degree, and the other coordinate translations commute with it. The identity exp(-t partial_y1)f=f(y1-t) is finite Taylor expansion on the monomial basis. Its matrices have polynomial coordinate entries and hence are continuous even for Omega, because each stage is finite-dimensional and the formulas are finite. The nilpotence order n+1 may grow; the new statement explicitly allows that.

Step 3 uses precisely the new node's derived-object comparison for a sheaf colimit and its retained G-action. I checked the colimit is the direct sum on all monomials using its universal property and finite-dimensional coordinate maps, rather than claiming it is a norm completion or an unrestricted polynomial-valued function space. Compatible actions agree on each generator. The conclusion is an isomorphism in D(A_G(A)), which is the equivariant category required for the subsequent invariants, not merely a collection of abstract cohomology groups.

Step 4 is an explicit algebraic contraction, not an analytic input hidden as elementary. I checked the signs in b_n=(-1)^n y(y+1)...(y+n-1)/n!: b_0=1, b_1=-y, b_2=y(y+1)/2, and Delta b_n=b_(n-1). Factoring the common product proves the identity for every n. The leading coefficient is an invertible rational, so triangular elimination gives a basis over arbitrary remaining polynomial coefficients B, including the section rings A(S). J shifts that basis, p is evaluation at zero, and Delta J=1, J Delta=1-ip, pi=1 give a G-equivariant homotopy equivalence. These are finite polynomials on each input, so no convergent series, topology completion, or bounded global degree is required. For the smallest nontrivial case r=1,m=0 the result is the exact sequence with kernel A and a surjective difference map.

Step 5 cites `lem-sfb-condensed-product-action-inflation` for the existence, exactness, Grothendieck property and normalized adjunctions, as well as the literal equality M^(GxH)=(M^H)^G. These are all in its statement; I did not use a mere action definition for an existence theorem. It cites `lem-sfb-derived-composition-adjunction-normalization` for the isomorphism R R_c = R R_a R R_b, with exact left adjoints supplied by the first node. Its statement specifically allows these Grothendieck action categories and K-injective ordinary derived functors. Its coefficient universe conventions match the item's. The induction hypothesis is stated simultaneously for all m in step 1, and the step reduces (r,m) to (r-1,m), so the induction is well founded and does not invoke a lemma depending on the item.

For the new statement I tested G=1, zero stages, constant systems, D=0, and unbounded dimensions/nilpotence. D=0 gives a zero differential, compatible with nontrivial degree-one continuous characters; the theorem has not erroneously asserted acyclicity for every unipotent module. Arbitrary transition maps would need more care, so the statement explicitly requires injective transitions and commuting nilpotent operators. Omega remains noncomplete throughout. Exponentials are finite at each stage. The stronger requirement that this computes the derived functor in the full action category is stated explicitly; it cannot be discharged by taking resolutions only in the ind-unipotent subcategory.

I checked B–E: self-contained statement-only new node; every used notion has a defining dependency or explicit meaning; single TeX escaping; honest recorded searches; exact verbatim citations; no off-route source or SGA; no strengthened hypotheses on the item; no duplicate or circular dense-lattice citation. The Mathlib searches were made with msearch.py and their actual logged output is copied into the nodes. Results concern finite/discrete cohomology, ordinary topological continuous complexes, solidification definitions, and complete-space Mahler series. I also read the pinned source `RepresentationTheory/Homological/ContCohomology/Basic.lean` and `Condensed/Solid.lean`: neither supplies a comparison with ordinary internal norm-coefficient derived invariants. No step exceeds 2000 characters, and the polynomial calculation is written out rather than hiding an auxiliary lemma.

## Delivery-check repair

The first dry run rejected the short displayed invariants equality in citations.json (under 40 characters). I replaced that quotation with the full product-action-inflation statement, so exactness, Grothendieckness, adjunctions and the equality used in step 5 are all visible verbatim. I also declared `lem-sfb-derived-composition-adjunction-normalization` in split_report.tool_uses: it is generic exact-inflation derived composition, not a replacement of the geometric unit route. I read its referenced Stacks Tag 09T5, derived.tex lemma-derived-adjoint-functors, and Tag 0D6E, sites-cohomology.tex lemma-derived-pushforward-composition; the former derives adjunctions and the latter illustrates composition via uniqueness of adjoints. The actual general normalized comparison used is the existing node statement.
