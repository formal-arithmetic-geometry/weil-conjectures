# Stage-1 delivery: lem-sfb-reductive-framed-noetherian-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-reductive-framed-noetherian-descent.json: statement, split into twelve proof steps; no Mathlib match for the complete framed descent assertion.
- citations.json: forty step/node entries, using verbatim statements of the cited live nodes.
- report.md: this report.

No new DAG nodes; zero Mathlib leaves. The statement and statement dependencies are unchanged. No unit realization is changed: this supporting lemma is not the unit's key statement. write_split.py is sandbox-only working material, not part of the delivery.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint id, reductive group descent, framed Lie weights and Noetherian descent. The existing smooth-algebra descent modules do not state this group-scheme assertion. Abstract reductive Lie algebra declarations do not concern reductive group schemes. No sorry declaration is treated as a completed proof.

## Literature wanted

WANTED: Brian Conrad, Reductive group schemes, local copy literature/conrad-reductive-group-schemes.pdf, Corollary 3.1.11 and proof, pp.88-89; introduction to Section 4, p.107; Corollary 3.3.6, p.101; Section 1.3, pp.25-29. I read the Stanford PDF online at the source URL already in the item. Since it is absent from literature/, proof_origin remains agent. I did not download into or edit literature/.

## What was wrong and what changed

The seed had a complete statement but no proof. Nothing in the statement required correction. The framing is additional finite data, and it would not suffice to descend only the smooth coordinate algebra. The proof now descends the Hopf maps, group diagrams and specified inclusion; closedness, smoothness and reductivity; geometric maximality; and the particular tangent isomorphism with its inverse. Each weight error is then expanded in a finite Laurent support and its coefficients are killed at a common stage. This avoids inferring an equality or isomorphism from tensoring along a nonfaithful or nonflat inclusion.

I checked the inherited source/blueprint chain against the latest chapter and unit, and read the latest direct-image proof (3). The inherited blueprint ancestor is null, which blueprint_refs.py ancestor confirms; the existing from.place and via chain are preserved. Searches of the whole DAG and blueprint for reductive, torus, framed, Noetherian approximation and the source's places found no blueprint node equivalent to the item. The related split-reductive-finite-type-spreading node concerns an extension of fields and a full based root datum; it does not imply descent over arbitrary rings or with all prescribed root vectors. The arbitrary-base-root-lines-coroots node is downstream of this item through its rank-one Gauss-chart route and is deliberately not cited. I checked that none of the actual dependencies reaches this item.

## Mathlib searches

The seed's existing searches and results are retained. Additional actual searches, recorded by msearch.py in searches.jsonl and copied exactly into mathlib_searches, were:

- leanfinder: A reductive group scheme with a specified split maximal torus and finitely many framed Lie algebra weight vectors descends to a finitely generated integer subring
- loogle: "Scheme", "reductive"
- grep: reductive|torus.*descen|framed.*Lie (AlgebraicGeometry)
- leansearch: Noetherian approximation of a reductive group scheme with split maximal torus and specified tangent weight basis
- leanfinder (second phrasing): A smooth affine finite presentation algebraic group and chosen torus representation basis spread out over a Noetherian subring

All services answered. Loogle and grep returned no hits. The semantic hits concern abstract Lie weights, root pairings, Noetherian scheme recursors, and smooth algebra models. I read Mathlib/RingTheory/Smooth/NoetherianDescent.lean:255-279: Algebra.Smooth.exists_finiteType at line 268 gives a smooth algebra over an injective finite-type subring, but none of the Hopf maps, specified torus, reductive fibres or framing. This is not a one-line specialization proving our item.

## Not duplicates

No new nodes are proposed. Existing model, openness, module-descent, tangent-base-change, centre and rank nodes are reused. In particular, no new lemma merely restates a clause of this item.

## Review by NO

I read delivery-errors.md B through E in both copies, the worker brief, stage-1 document, GOAL.md, and SETUP's three-level and tool-use rules. I checked the item against Conrad Corollary 3.1.11 (including the distinction between reductivity of identity components and connected reductive fibres), and the Section 4 full-character grading discussion. For the algebraic descent I read Stacks algebra.tex lemma-colimit-category-fp-algebras (05N9) and lemma-colimit-category-fp-modules (05N7), the Noetherian permanence statement (00FN), limits.tex lemma-descend-smooth (0C0C), and lemma-limit-contained-in-constructible (05F4). The closed-immersion descent input is precisely the existing 01ZP node, with its locally finite type and qcqs hypotheses checked. For the final field calculation I used the existing Milne radical, maximal-torus quotient and tangent-dimension statements, and Conrad's scheme-theoretic centre/weight kernel statement. There are no new node sources to audit.

Here is my check of what each step actually takes from its cited statements:

1. The finite-type-subalgebra node gives the directed ring colimit and containment of finite coefficient sets. The Noetherian permanence node applies over Z (every ideal is principal). The affine qcqs node and affine-limit node give exactly the scheme limit and hypotheses later used. Every subring is unital inside the nonzero A, so it is nonzero.
2. The smooth-affine equivalence really supplies a finite presentation of C. The finite-presentation definition gives the explicit quotient. The diagonalizable-group definition gives the fixed Laurent Hopf algebra, not a theorem about root spaces. The affine fibre-product node and tensor finite-presentation node justify precisely the tensor-power algebras used for diagrams. The torus and its monomial lattice are not allowed to drift under descent.
3. The algebra-colimit node has separate map and eventual-equality clauses, both read. It is not being used for object existence (its statement omits that clause); the object was constructed by coefficients in step 2. I listed all group diagrams and homomorphism diagrams. All domains and codomains are finitely presented by step 2, including triple products. One finite upper bound enforces every diagram.
4. The closed-immersion node assumes locally finite type, not an unproved flatness assumption. Laurent generators of the target coordinate algebra give that finite type directly. Smooth descent has locally finite presentation and qcqs models available, and supplies persistence on the tail. The reductivity-eventual-ring-colimit statement concerns the entire connected reductive fibre group, with no injectivity/flatness/Noetherian condition missing. All its hypotheses are satisfied after smooth descent.
5. The torus-fibre-openness node explicitly states the maximality openness used. Field-extension invariance is its own cited node, in both directions, and compares residue fields via a common algebraically closed extension; I did not assume that every point of Spec A_i is hit by Spec A. The Noetherian ring makes the open a finite union of principal opens; their retrocompactness and the definition of constructible establish the exact input to 05F4. The affine-limit node from step 1 supplies the actual limit. Thus eventually every stage point, including new points outside the original image, has a maximal torus.
6. The relative-tangent-weight-base-change node is only used after the base has become nonzero Noetherian. It applies without reductivity or maximality, so it cannot be circular here. Smoothness of the split Laurent torus is proved from the formal-smoothness definition by lifting a unit and correcting its inverse modulo a square-zero ideal. The cited node gives finite projectivity and the full coaction comparison for arbitrary extension A_i to A, not merely flat extension. Naturality of the inclusion differential is postcomposition of dual-number points, written out in the step.
7. The affine module-colimit node supplies descent of both specified maps and equality of their two composites. It also supplies equality with the actual torus differential. Finite presentation of V_i follows explicitly from a finite idempotent splitting, V_i = coker(1-e), while F_i is finite free. I replaced an earlier appeal to finite relations over a Noetherian ring by this finite matrix presentation, so no module-Noetherian lemma is hidden here.
8. The same module-equality node is applied only with finitely presented source A_j and target V_j. It is not applied to the infinite-rank Laurent module. Instead the explicit tensor/direct-sum coefficient isomorphism leaves a finite list of coefficients in V_j; each defines a map from A_j. Full coaction base change in the tangent node says exactly why each coefficient vanishes at the limit. Finite Psi gives a common later stage.
9. The inverse maps already ensure linear independence and generation, and remain inverse after every scalar extension. The definition of the diagonalizable group supplies commutativity; commutativity directly fixes the torus tangent summand on all algebra points. This is an elementary assembly step with the explicit coaction formula, not a fresh structural lemma.
10. The tangent comparison really permits extension to any algebraically closed residue field of A_0. The displayed basis stays a basis. Laurent monomials, unlike differentials of characters, remain distinct in characteristic p. Coefficient comparison proves exact support and permits empty Psi; it does not rely on a generic fibre calculation.
11. The relative centre/weight-kernel node is applied over F, a nonzero Noetherian field, to the already proved full weight support. It states the scheme-theoretic centre, including non-smooth centres such as mu_p. The torsionfree-free node applies to the explicitly finitely generated torsionfree quotient N=M/L. The diagonalizable duality node supplies the contravariant closed-inclusion/surjection dictionary; every subtorus over algebraically closed F has a free character group, and therefore kills the torsion L/ZPsi. This proves K is the largest central torus. The radical-quotient node then identifies that largest central torus with the radical and supplies the semisimple quotient. I use its statement, not a step hidden in its proof.
12. Rationalization of M/L gives rank r-d by the ordinary vector-space quotient formula. The multiplicative-type-largest-subtorus node explicitly says every torus is smooth. The Lie/tangent equivalence and group-tangent-dimension criterion identify Krull dimension with the number of Laurent tangent coordinates. The reductive-semisimple-rank-formula node states precisely that quotient by the given central radical has maximal torus T/K and rank dim T - dim K. The radical hypothesis is proved in step 11. This proves the definition of semisimple rank written in the item, without substituting a different notion of rank.

Small cases: A may be disconnected or nonreduced, and no tensor equality is reflected without eventual-equality descent. The zero ring is excluded exactly as in the item, and every model subring is nonzero. Positive-characteristic examples SL2 in characteristic 2 have weights +2 and -2 as distinct torus characters, even though their differentials can coincide; the proof never compares character differentials. A central mu_p contributes no spurious central torus: the saturation in step 11 removes only torsion in the character quotient. For Psi empty, the computed centre equals T, the radical is all of T and the rank formula is zero. Rank-zero M and the trivial group are covered by empty presentations, sums and zero-dimensional tori. For {a,-a}, a is nonzero in a free lattice so its rational span has dimension one in every residue characteristic. Nonprincipal root lines cause no issue because the item's own hypothesis explicitly gives free lines and specified generators; these are descended with the inverse map.

No proof step is longer than 2000 characters. I reviewed the lattice calculation as the routine argument from the quoted duality and radical statements, not an unquoted theorem equating rank with root-span dimension. There is no new unsplit-node proof, no relabelling of the item, no route replacement, and no SGA source is cited. Generic dependencies from other units are declared in split_report.tool_uses, not in the maintainer-owned tool_uses field.

## Unfinished work and validation

No mathematical clause is left unfinished. This is a stage-1 split, not a claim of a Lean proof. Server review_split passed before this report was written. Required full dry-run and push results are recorded below after they finish.

First full dry-run preflight rejected only the phrase “the item's definition” in proof step 11 under its standalone-wording check (B2). I replaced it with the explicit maximal-torus definition of semisimple rank. No mathematical statement or dependency changed.
