# Stage-1 repair: lem-sfb-polynomial-translation-acyclic

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-translation-acyclic.json`: unchanged statement; 2,356-character four-step assembly, status split.
- `dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-rank-one-difference-model.json`: statement, status unsplit, no Mathlib match; finite-degree stages, their continuous equivariant colimit presentation, and relative derived difference comparison.
- `dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-difference-deformation-retract.json`: statement, status unsplit, no Mathlib match; internal binomial-basis difference contraction, equivariance and derived isomorphism.
- `citations.json`: full verbatim statement for each cited node in each parent proof step.

Two new nodes, zero Mathlib leaves. The two new statements have 2,617 and 2,252 characters, respectively. Their proof/proof_deps are empty and proof_origin is null. Auxiliary research files and the search log remain in the sandbox only. No Lean was changed or compiled.

## Attachments

None. I searched `lean/WeilConjectures/` for polynomial translation, PolynomialTranslation, the exact blueprint tag, and finite-stage/difference-contraction concepts. No project declaration states the item. The existing `Sheaf.CategoryTheory.PolynomialTranslationAcyclic` theorem `Profinite.CondensedAction.PolynomialTranslation.polynomial_translation_acyclic`, lines 125-130, still has sorry, so it is not an attachment. Its docstring has exactly the five arguments being redistributed. The new algebraic and finite-stage assertions are not separately supplied by an existing project theorem.

## WANTED

WANTED: a precise reference for the ordinary internal condensed derived difference model for countable finite-dimensional unipotent norm representations of Z_ell with a commuting profinite action, retaining ALL continuous functions and the noncomplete norm on Omega; for existing `lem-sfb-ind-unipotent-procyclic-difference` and the application in `lem-sfb-polynomial-rank-one-difference-model`.

The main-20261015 blueprint direct-images proof paragraph (3) delegates the open-immersion coefficient result. It does not contain this analytic theorem or the explicit polynomial contraction. These remain honestly agent-formulated arguments. No SGA source is used and no analytic reference is invented. The prior delivery report, including its citations, mathematical cautions, searches and review, is retained below.

## Audit findings and corrections

The returned issue was excessive work in the parent proof, not a false statement. I preserve the parent's entire statement, all inherited metadata and search records, and its existing source and proof_origin. At session start the sandbox held only dispatcher brief marker files: there were no retained node files, report, citations or searches.jsonl to reuse. I copied the current shared node (which contains the returned five-step proof) and read the existing Q12 report and landed Lean docstring. The unchanged original node is retained as sandbox research material. Delivery overlays the current server head, preserving maintainer-owned fields.

The requested repair adds TWO comparable independent arguments. The first is a relative one-coordinate derived model; it does not prove positive vanishing for the whole lattice. The second is an algebraic homotopy equivalence, with no p-adic analytic input or derived group invariants. Neither restates the parent or moves the whole theorem into one node. The parent keeps the induction and exact-inflation composition. No statement dispute was found, and no hypothesis was added to the parent.

## Coverage of every retained argument

Old step 1 (rank-zero base) is retained verbatim as new parent step 1. For r=0 invariants are identity, so their derived functor on a degree-zero object has zero positive cohomology. This works simultaneously for all m, including m=0.

Old step 2 is carried by the finite-stage clauses of `lem-sfb-polynomial-rank-one-difference-model`. The future proof takes the span V_n of total-degree-at-most-n monomials over E. It is finite-dimensional; its inclusions are injective and commute with differentiation. Every translation preserves total degree. D_n=-partial/partial y_1 lowers degree and hence D_n^(n+1)=0. Translation in the other y variables commutes with D_n. In the finite monomial basis each action matrix entry is a polynomial in the lattice coordinates, proving continuity for the finite product norm. On y_1^a, the finite sum of t^j D_n^j/j! is the binomial expansion of (y_1-t)^a, giving the Taylor identity, and multiplication by the other variables gives it on every monomial. Thus all the hypotheses of the existing `lem-sfb-ind-unipotent-procyclic-difference` hold, with no uniform nilpotence bound.

Old step 3 is carried by that same new node's realization, colimit and derived-comparison clauses. Coefficient projections and assembly identify C(S,F tensor_E V_n) with the finite sum of copies of A, continuously and naturally in S. A compatible family of maps from these finite monomial sums is exactly a map from each monomial copy of A, so their sheaf colimit is the internal monomial coproduct. The actions agree on every coprojection for every varying profinite group parameter. Apply the existing ind-unipotent comparison with these stages and its retained G-action: exp(D)-1 is precisely Delta f=f(y_1-1)-f(y_1). Its conclusion is the derived isomorphism in D(A_G(A)), with degree-zero invariant inclusion normalization. No commutation of a derived functor with a filtered colimit is asserted, and no finite-degree stage is claimed acyclic.

Old step 4 is carried by `lem-sfb-polynomial-difference-deformation-retract`. Here is the entire algebraic argument retained for its future worker. Over B, b_0=1 and b_n=(-1)^n y(y+1)...(y+n-1)/n! have invertible rational leading coefficients. Eliminate the highest degree successively to expand every monomial uniquely in finitely many b_n. For n>0, subtracting the two products at y-1 and y factors out y(y+1)...(y+n-2); the remaining factor is (y-1)-(y+n-1)=-n. Including (-1)^n/n! gives Delta b_n=b_(n-1), including n=1 by the empty-product convention. Also Delta b_0=0 and b_n(0)=0 for n>0. Therefore J(b_n)=b_(n+1), p(f)=f(0), and constant inclusion i satisfy Delta J=1, J Delta=1-ip, pi=1 and Delta i=0 on every basis vector. The basis change and these operators send each monomial to a finite combination, so their coproduct maps are internal and natural in test sets. G acts only on B and all coefficients in these formulas are rational constants, so the maps are G-equivariant. In degrees 0 and 1 these identities are exactly the homotopy between identity and ip, with J from degree 1 to degree 0. They give inverse derived isomorphisms Q[T->T] and B[0]. The statement gives the derived isomorphism itself, not merely per-degree groups.

Old step 5 stays in parent step 4: `lem-sfb-condensed-product-action-inflation` supplies the Grothendieck action categories, exact additive left adjoints, their specified invariants right adjoints, and the conjugate equality Gamma_(GxH)=Gamma_G Gamma_H^G. These hypotheses allow the existing normalized derived-composition theorem. After the first new node and second new node give RGamma_H^G(T)=B[0], total invariants are RGamma_G(B[0]). Relabel the remaining y variables to identify B with T_(r-1,m). The simultaneous induction hypothesis therefore kills positive cohomology. This reduces r by exactly one and never cites the polynomial-bar/dense-lattice ancestors.

## Mathlib and duplicate searches

Every new-node search was run through the mandated msearch.py command and recorded exactly from searches.jsonl. Each node has LeanFinder, Loogle, grep and LeanSearch records, including a second semantic phrasing. The first node's hits concern Taylor linear equivalences on degree-bounded polynomials, nilpotent polynomial elements and cotangent constructions: none states the equivariant condensed colimit presentation or ordinary relative derived isomorphism. The second node's hits include Polynomial.fwdDiff_iter_eq_zero_of_degree_lt, Polynomial.fwdDiff_iter_degree_add_one_eq_zero, Polynomial.fwdDiff_iter_degree_eq_factorial, Pochhammer polynomials, interpolation and general homotopy equivalences. These state useful ingredients, not the internal equivariant contraction, and it is not a one-line specialization. I read the local Pochhammer definitions and recurrences and ForwardDiff degree formulas; no leaf claim is made.

Before creating either node I searched the whole DAG for polynomial/difference, finite-stage, nilpotent-translation and binomial-basis concepts and checked the prospective ids were unused. I ran blueprint_refs ancestor on the item (it returns None), and whole-blueprint searches for polynomial translation, difference contraction, polynomial finite stages, Pochhammer and polynomial. The 74 broad polynomial hits concern unrelated geometry, polynomial ring definitions, or cohomological characteristic polynomials; the precise searches give no match. The parent's null ancestor and via chain are retained, with the parent prepended for each new node. I also read the existing ind-unipotent-system definition, ind-unipotent comparison, polynomial-bar comparison, rational polynomial bar contraction, relative cyclic model, filtered-continuity and norm-algebraic-closure augmentation statements before deciding these were distinct.

## Unfinished work

The two new statements are intentionally unsplit and ready for separate workers. The existing analytic ind-unipotent lemma remains an obligation; I do not claim to have proved it, its finite-stage application or the parent in Lean. This delivery repairs the requested one-level decomposition only. There is no additional unresolved return point.

## Not duplicates

lem-sfb-polynomial-rank-one-difference-model vs def-sfb-ind-unipotent-system: the existing node defines a general representation system and its presentation; the new node asserts that a specific polynomial filtration gives that type of system, presents the monomial coproduct, and has the relative derived model.

lem-sfb-polynomial-rank-one-difference-model vs lem-sfb-ind-unipotent-procyclic-difference: the existing generic comparison assumes the compatible nilpotent finite-dimensional system and its sheaf colimit; the new argument constructs/verifies those polynomial stages and identifies their colimit with the specified polynomial action module. Its additional assertions are not a one-line specialization, and are exactly old steps 2-3 of the returned proof.

lem-sfb-polynomial-rank-one-difference-model vs lem-sfb-polynomial-derived-bar-comparison: the existing node is a comparison of the trivial-coefficient polynomial bar complex for the whole lattice; the new node treats relative invariants of a translating polynomial module for one factor and retains a residual action. The existing node is also an ancestor, so it cannot be used circularly.

lem-sfb-polynomial-rank-one-difference-model vs lem-sfb-relative-cyclic-restriction-model: the existing node constructs a comparison map and its discrete-cyclic two-term target but explicitly does not say the map is an isomorphism. The new node asserts an isomorphism for this polynomial translation module and verifies its finite unipotent presentation.

lem-sfb-polynomial-difference-deformation-retract vs lem-sfb-rational-polynomial-bar-contraction: the existing node contracts the many-degree additive-bar complex onto an exterior complex; the new node contracts a two-term backward-difference complex onto constants, internally with an arbitrary commuting coefficient action.

lem-sfb-polynomial-difference-deformation-retract vs lem-sfb-polynomial-translation-acyclic: the parent is positive vanishing of all lattice-derived invariants for specific norm coefficients; the new node is a rational algebraic equivariant chain contraction with no analytic or invariants comparison.

No new source has a Stacks tag, so there are no same-tag duplicate pairs. The generic composition theorem is reused, with its inherited tool-use declaration, instead of duplicating it.

## Review by Q96

I read the main-20261015 chapter, current sk-thm-sf-ctf-stability section and direct-images proof paragraph (3), the DAG unit record, the returned parent with its five-step proof and Q12 review, and the landed PolynomialTranslationAcyclic module. Paragraph (3) supplies the route (open-coefficient direct image), but delegates the analytic calculation: neither new statement is falsely attributed to a proved theorem there. For the finite-stage node I read the full generic ind-unipotent comparison and its system definition; its hypotheses match the concrete polynomial stages described above, including injectivity, finite-dimensional norm topology, G commutation, finite exponential, all continuous F-valued sections and sheaf colimit. For the contraction node I recomputed the binomial formulas in the retained argument above. It is an agent algebraic lemma over rational condensed coefficients, not a cited analytic result.

Parent step 1 is the unchanged elementary identity-functor base. Parent step 2 uses precisely the first new node's final isomorphism, with r>=1 and both allowed fields; the finite-stage construction is now the new node's explicit task. Parent step 3 uses precisely the second new node's internal equivariant derived isomorphism, with d=r-1+m, the rational constant inclusion into A, and the remaining-variable polynomial algebra B; the G-translation preserves its algebra structure. Regrouping monomials is the coproduct universal property. Parent step 4 uses the full statements of product-action-inflation and derived-composition-adjunction-normalization, which I opened and read. The former explicitly supplies Grothendieckness, exact additive inflations, normalized right adjoints and their conjugate comparison. The latter explicitly gives the natural derived composite isomorphism for such specified exact adjunctions. I also read its Stacks sources Tag 09T5, derived.tex lemma-derived-adjoint-functors, and Tag 0D6E, sites-cohomology.tex lemma-derived-pushforward-composition. The actual general normalized assertion used is the existing DAG theorem; I did not misattribute it directly to the narrower ringed-topos theorem. This existing off-unit theorem is a generic tool, as the inherited split_report.tool_uses explains. citations.json contains the actual full statements for all four uses, so the quotes can be checked literally without borrowing a fact from a proof or a definition.

I tested the new finite-stage statement at r=1,m=0,n=0: V_0=E, D_0=0 and the action is trivial, consistent with the finite Taylor sum. At n=1, D(y_1)=-1 and exp(tD)y_1=y_1-t, so the sign is right. With no spectator or remaining y variables the colimit still has all y_1 monomials and the relative comparison remains a two-term complex. I did not replace this with false finite-stage acyclicity. For the contraction, b_0=1,b_1=-y,b_2=y(y+1)/2 give Delta b_1=1 and Delta b_2=-y; p(b_n)=0 for n>0 and the identities on constants agree. The same computation includes arbitrary B coefficients, d=0, G=1 and B=0. The rational-algebra hypothesis is essential for factorial inverses and holds for both E and Omega. Every formula is finite and natural, so no completeness of Omega or global degree bound was slipped in. The induction base covers r=m=0 and the step preserves m.

I checked B1-B10: both nodes are self-contained statement-only obligations with real sources/places, definition citations, singly escaped TeX, honest logged searches, no unsupported leaf/attachment, and filled blueprint provenance. C1-C8: every non-elementary parent input is a cited statement, quotations are verbatim, there is no circular ancestor citation or newly asserted off-route tool. D1-D5: the decomposition separates two independent arguments, preserves their formulas and all original work, and retains the actual rank induction rather than renaming a clause. E1-E7: the field, topology, universes, group actions, rational inverses, degree-zero normalizations and derived categories match throughout; no statement error was found. No parent step is over 2000 characters and the whole parent proof is below 3000. The mathematical analytic risk is still explicitly assigned to the existing ind-unipotent comparison, as in the accepted prior delivery.

## Validation

Server check_dag and the required final deliver.py --no-push preflight are run from the delivery tools; their results are recorded in the final delivery output. No forbidden local preflight or compiler is invoked.

## Return d8c3a2a3306: current-DAG repair (2026-10-22)

The specific return was the landing refusal “completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it)”. I retained the delivered sandbox, original-item.json, the prior reports, citations and searches rather than restarting the split. The initial interrupted dry-run receipt named c4c529b8e7e; no delivery command was still running when this resumed session checked the process list. The first resumed dry run exited successfully at 06d498349c0. These are dry-run commits, not claims that a push or landing happened.

I compared the retained original-item.json with the current shared DAG parent: all fields agree. Compared with that current parent, the delivered parent differs only in proof, proof_deps and split_report; its statement and statement dependencies remain identical. Both proposed new ids remain absent from the current shared DAG. I re-read every parent proof citation, all statement dependencies of the parent and new nodes, and the existing ind-unipotent comparison and system definition. Each of the four citations.json quotations is still exactly the entire statement it cites. In particular the current product-action inflation statement still supplies Grothendieckness, exact additive inflations, their invariant-inclusion adjunctions and the conjugate product equality; the current normalized composition statement still gives the derived isomorphism for precisely those specified adjunctions. No cited mathematical assertion needed replacement. I checked the live Sheaf theorem again: its proof is still sorry; no WeilConjectures declaration supplies an attachment.

The concrete adjustment is parent step 4: it now specifies the three categories and each of L_a, L_b and L_c, their three right adjoints, and why the composite identification has the required conjugate. This checks the normalized-composition hypothesis directly against the current citations instead of leaving it under “these are the hypotheses”. All former proof arguments remain represented; neither new node's statement or search question changed, so the logged searches were read and reused without repetition. The final assembly has 2,356 characters and no step exceeds 2000 characters. citations.json needs no changed quote or step number.

The required deliver.py constructs the delivery on the latest fetched origin/sheaf-dag and overlays only split-owned fields, preserving current maintainer metadata. Its successful server preflight is the worker's verification of this rebased overlay. Promotion of side completion to the queue's live DAG remains the maintainer's operation named by the return; I have not changed live state or worked around that gate. The final dry run and push below use the prescribed tool after this concrete proof/report repair. This section supplements my Review by Q96 above with the return-specific rereading and correction.

## Retained prior delivery report (Q12)

The following is the historical report read and preserved from the shared repository; its references to one new node and five steps describe that earlier delivery, before this repair.

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


## Current-head revalidation by Q96 (2026-10-22)

I continued the retained repair rather than rebuilding it. The first required dry run in this session completed successfully at c6eb49d6202. The shared original parent still agrees field-for-field with original-item.json; the sandbox differs only in proof, proof_deps and split_report. Neither proposed new id exists in the current shared DAG. The released stage-1 repair note still requires two statement-only nodes and a parent assembly of at most 3000 characters.

I reopened all four parent-citation statements and every statement dependency of the parent and the two new nodes. The current product-action theorem still states exact inflation, the full profinite-base-change fixed-section condition and the inclusion-normalized adjunction. The current composition theorem explicitly requires its derived adjunctions to be those induced by these underived adjunctions. Accordingly I expanded step 4 to check the product-fixed condition using (g,h)=(g,1)(1,h), to check that both transpose maps restrict along the same invariant inclusion, and to specify the induced derived adjunctions. This is a concrete hypothesis check against the current DAG, additional to the retained repair. The mathematical statements and search questions of the two new nodes have not changed; I read and reused all eleven logged search results. All four citation quotations remain verbatim.

I reread blueprint direct-images paragraph (3), which still delegates the coefficient calculation, and the current ind-unipotent comparison: its full ordinary action category, all-continuous functions, finite-stage exponential and noncomplete Omega assumptions still match the first new node. For the second node I checked the signs at b_1=-y and b_2=y(y+1)/2 and the contraction on constants; no change is necessary. I repeated the source attachment search: the WeilConjectures hits concern unrelated finite-stage descent, while the Sheaf polynomial-translation theorem still ends in sorry. The earlier report's theorem line 125-130 is historical; the current theorem starts at line 126.

The updated assembly has 2584 characters; its longest step has 1166 characters. No statement, definition dependency, new-node scope or citation number changed. The final dry run and delivery are performed with the prescribed tool, which constructs the overlay on the fetched current server head and preserves maintainer metadata.
