# Worker report: lem-trf-bar-scalar-restriction-coherence

## Files written

- dag/nodes/sec-trace-formula/lem-trf-bar-scalar-restriction-coherence.json: statement, split into seven steps; Mathlib has scalar infrastructure, but no declaration found stating the whole normalized bar comparison. Statement and stmt_deps are unchanged. All inherited metadata and searches are retained; six searches actually run for NJ on this item are appended.
- citations.json: verbatim statement excerpts for every node cited by every proof step.
- report.md: this report. searches.jsonl is the search command's own log; write_split.py is an item-local generation script, not a delivered node.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the live project under lean/WeilConjectures/ for the exact blueprint id, barComplex, barResolution, bar/scalar combinations and restriction-of-scalars terminology. Ordinary scalar restriction, tensor and coefficient lemmas do not give all the present clauses. The item has no finished project declaration identified by these searches.

## WANTED

None. The proof is an agent coefficientwise refinement of the available Stacks material, not a claim that Stacks states this normalized scalar theorem verbatim.

## What changed and what was wrong

The imported item had an empty proof. Its assertion is valid with its stated hypothesis that the canonical acyclic bar comparisons m are isomorphisms. No statement correction was needed. In particular, the scalar comparison here is the one determined by those specified comparisons: alpha=(Dr(m_S))^(-1) Q(kappa) m_R. Establishing total derived colimit existence or the acyclicity giving m is not an extra assertion of this item. The proof never assumes restriction along an arbitrary ring homomorphism preserves projectives.

I read the chapter sec-trace-formula, unit sk-i-curve-zero, and the current main-20261015 locality node and proof. The item's long inherited blueprint.from place explains its intermediate cotangent-transitivity/bar-computation branch; I retained that precise provenance. Whole-blueprint searches for scalar restriction, restriction of scalars, and bar terminology found no blueprint node stating this assertion. There are no new duplicate candidates. I also read the existing derived-colimit-bar, same-ring bar-resolution-derived-reindexing, bar-scalar-unit-transpose, exact-bar-cone-boundaries and several general exact-derived-comparison statements. The parent derived-colimit-bar uses this item and cannot be cited without a cycle. The same-ring reindexing theorem has additional normalized-adjunction and u_!-acyclicity assumptions; none are needed for the coefficientwise chain identities asserted here, which are proved directly.

## Review by NJ

For the item I read literature/stacks-project/sites-cohomology.tex, Tag 08PG, label example-left-derived-colimits, and Tag 08PH, label example-morphism-categories, including their signed degree-two differential and reindexing formula. I checked the corresponding tag mappings in tags/tags. These are the source of the formulas; the scalar coherence refinement is explicitly marked agent-written. For the exact-derived input I read derived.tex, Tag 015F, label lemma-right-derived-exact-functor. I also read the local Mathlib implementations in Algebra/Category/ModuleCat/ChangeOfRings.lean (restriction, identity and composition maps at lines 65--89 and 197--299) and ChangeOfRingsExact.lean (exactness and finite-limit/colimit preservation, lines 36--49). No new nodes require further sources.

Step 1 uses only the displayed definition of scalar restriction and finite-support sums: kernels, images and quotients are literally unchanged abelian groups. This establishes exactness and quasi-isomorphism preservation, including objectwise presheaf exactness. It does not cite the existing lem-weil-restriction-of-scalars-exact, whose statement is about a particular completed integral coefficient map rather than arbitrary R to S.

Step 2 cites lem-trf-augmented-presheaf-bar-resolution. I opened its whole statement: it states that these precise B and K formulas are complexes, gives the face identities and augmentation, and gives the coefficientwise colimit identification b. Its hypotheses are exactly the small category, arbitrary commutative ring, and identity-cover presheaf category here. The extra scalar identification is proved in this step on finite-support coefficients, with both ordinary and last faces checked separately. Augmentation compatibility is the equation r(a_H) beta=a_(rH), and naturality is the same coefficient calculation. Thus no new lemma repeats a clause of the item.

Step 3 cites lem-sf-exact-functor-derived-triangulated. Its statement takes any additive exact functor between abelian categories and gives its termwise triangulated functor on unbounded derived categories, so it applies to restriction after Step 1, with no flatness, boundedness or preservation-of-projectives hypothesis. The rest is the written three-factor definition of alpha and cancellation with the assumed invertible m. Its naturality uses naturality of kappa from Step 2 and of the specified canonical comparisons m: the latter also follows directly from their displayed formula using the natural augmentation a, b, and epsilon. No right-derived injective-resolution theorem is substituted for a left-derived bar comparison.

Step 4 has no external theorem: for each finite-support generator, the faces before the last commute because u respects identities/composition, and the last commutes by the explicitly written equation G(uf)t(x)=t(F(f)x). This also verifies the same-ring factorization, including when different source chains acquire the same image.

Step 5 has no external theorem: it writes the two successive images of a generator, verifies sigma-rho semilinearity and writes both iterated R-actions. The identity and scalar-compositor maps are literally the identity on coefficients. Since maps of direct sums are determined by their summands, this proves the equalities rather than merely asserting compatibility.

Step 6 cites def-weil-abstract-derived-category only for its actual definition of Q as localization. I read the statement: it supplies the functor Q and complexes/morphisms, not a hidden scalar comparison. The derived identities are proved by applying functoriality and explicitly cancelling the intervening m and inverse. The same calculation gives scalar-comparison composition with the iterated restriction identification on complexes.

Step 7 cites def-weil-abstract-derived-category for the stated cone differential, shift and minus-projection convention. I checked that these are explicitly in its statement. We take a cone roof for a connecting morphism as given; exact restriction preserves its quasi-isomorphic left arrow by Step 1. Both components of the roof, its sign and the map (b,a) to (f_B b,f_A a) remain the same. This establishes preservation of connecting roofs without claiming, from a definition alone, a new theorem about acyclic resolutions or their derived connecting maps.

I checked the small cases: for the empty indexing category both complexes and both derived bar representatives are zero; in degree zero the augmentation is unchanged; in degrees minus one and minus two the formulas agree respectively with d_0-d_1 and the three-term differential in 08PG. For identity categories they reduce to identity-on-coefficient maps. Nonfaithful u can merge chains but images are finite sums, so the formulas remain linear. A nonflat map Z to Z/2 and also a zero coefficient module cause no change in these checks: tensor products, inverse scalar extension, and restricted projective resolutions are never used. Each proof step is under 2000 characters. I checked delivery-errors B--E: no new standalone proof sketch, no duplicate or restatement node, no uncited non-elementary fact, no use of a cited node's proof in place of its statement, no hidden stronger hypotheses, and no cyclic citation of the parent.

## Not duplicates

No new nodes.

## What could not be finished

Nothing outstanding in the mathematical split. Delivery verification is recorded below when it completes.

## Delivery checks

The first dry run rejected one citation excerpt as shorter than 40 characters. I expanded Step 7's excerpt to include the entire verbatim cone differential and projection clause; the mathematical proof was unchanged.


## Repair of returned delivery ce80bbc6920

The return of 2026-10-23 04:21 UTC was an integration refusal: the approved side completion had not been promoted into the DAG read by the live queue. I continued the retained sandbox rather than treating the earlier reader's approval as a live completion. Compared with the current read clone, the item is still unsplit, with empty proof and proof dependencies; its statement, statement dependencies, source, creation metadata, chapter, unit and blueprint provenance agree with the retained item. The retained seven-step proof and all searches remain in this delivery. The first required repair dry run built a fresh commit d6a1cfc29d4 against current origin/sheaf-dag and passed server preflight; the final dry run below checks the revised proof, rather than an unchanged re-push.

I re-read all three proof-cited nodes in the current DAG, including the augmented-bar node which is now itself split, and all six statement dependencies. Their current statements support the same uses. In Step 2, the bar node explicitly gives the face identities, functorial augmented complex and the coefficientwise isomorphism b: CB(F) -> K(F); I expanded the verbatim excerpt to cover these clauses instead of quoting only its first sentence. Step 3's Mathlib leaf explicitly treats any exact additive functor of abelian categories and unbounded derived categories, so the exactness proved directly in Step 1 supplies all its hypotheses. Its local Mathlib source ExactFunctor.lean defines mapDerivedCategory, mapDerivedCategoryFactors and the triangulated instance. I corrected the proof's notation Dr(QX)=Q(rX) to the canonical localization identification and wrote out naturality of m from a, b and epsilon. Step 6 now displays the full normalized composite and its intermediate inverse cancellation, including the scalar-only specialization. Step 7's current definition explicitly specifies the cone differential, shift, and negative projection; its expanded excerpt now includes all three, not just the differential and unsigned projection.

For the current parent and route I re-read the trace-formula chapter, sk-i-curve-zero, and the main-20261015 locality statement and proof. This remains a supporting bar-comparison argument under the inherited cotangent-transitivity provenance; the parent derived-colimit-bar still cites this item, and I did not introduce a reverse edge. I re-read Stacks 08PG/08PH and 015F and the local scalar-restriction definitions and exactness instances. The explicit coefficient, finite-support, last-face and signed-cone arguments remain valid. The current item assumes the m-comparisons rather than asserting their existence from restriction preserving projectives. Empty categories, zero modules, identity and nonfaithful functors, and nonflat coefficient maps give the same edge checks as the retained review. Every proof step is below 2000 characters. No new statement, node, Mathlib claim or search query was needed; the recorded searches and their results were retained and read. Delivery-errors B--E were checked again against these current statements. No repository, launcher, Lean source, or compiler was changed or invoked.
