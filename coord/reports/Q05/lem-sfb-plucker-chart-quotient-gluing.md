# Q05: lem-sfb-plucker-chart-quotient-gluing

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-plucker-chart-quotient-gluing.json`: statement, split; no exact Mathlib match. Eight proof steps, no new nodes, and no new Mathlib leaves. The statement is unchanged.
- `citations.json`: one verbatim cited statement for every step/node pair.
- `report.md`: this report. `searches.jsonl` records five fresh searches, whose actual records were appended to the item's existing search history. The sandbox's `write_split.py` is a local preparation script only.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, Plucker/Grassmann/pivot and module gluing found no declaration stating this item. The module-gluing declaration proves a supporting tool only. The item has no recorded Lean declaration to attach.

## WANTED

None. The needed source material is present in the read-only repository.

## Corrections and scope

The statement is unchanged and no statement dispute was found. The previously empty proof is replaced by an argument. The determinant-locus chart theorem is a proof dependency, not a statement dependency: the item independently introduces B, H, A, X and every chart matrix, and its statement does not invoke that theorem. All other statement dependencies and inherited provenance fields are retained. The chapter/unit records were read; this item is a lower prerequisite and does not realize the unit's key statement, so neither record is edited.

The explicit transition argument and the local-ring maximal-minor proof are agent completions of Stacks 089T. They are marked as such rather than attributed verbatim to the source. The source uses quotient rank n-k; here n=N and n-k=r. Its route is the same: normalize on pivot loci, glue sheaves and maps, show the pivot loci are open, stable under arbitrary pullback, and covering. We use the existing generic Cauchy--Binet node instead of creating a separate spanning-basis node for its final vector-space paragraph.

## Not duplicates

No new nodes. The search of the whole DAG by pivot, minors, Cramer, adjugate, gluing and determinants found the existing tools used in this split. Full-blueprint searches `pivot` and `Grassmann` found no equivalent blueprint node; `blueprint_refs.py ancestor` returns None. The item's already specific inherited `blueprint.from.place`, `via`, and empty `same_as` are retained. No claim is extracted into a new copy of one of the item's clauses.

## Mathlib search assessment

All five commands were run with Q05 and this item's id: LeanFinder's normalized chart/glued quotient query, Loogle's `"Grassmannian", "chart"`, grep `Grassmann|Plucker|plucker|pivot` in AlgebraicGeometry, LeanSearch's tautological quotient query, and a second LeanFinder phrasing asking for a free-sheaf surjection covered by invertible minors. All services answered successfully. The results were read: Module.Grassmannian and its quotient properties concern individual modules; SheafOfModules generating sections describe presentations/generators, not the displayed Proj or transition matrices; the ideal-sheaf gluing hit glues a subscheme, not a quotient module. Loogle and grep returned no hits. The pinned Mathlib RingTheory/Grassmannian.lean lines 46--53 explicitly list affine charts, scheme Grassmannians, and representability as TODO. The old search records remain intact, and the fresh records are copied exactly from the search log, with separate verdicts.

## Review by Q05

I read the complete proof of Stacks Tag 089T (`constructions.tex`, label lemma-gkn-representable), including its omitted-detail gluing paragraph, normalized quotient subfunctors, open pivot argument, pullback argument and coverage paragraph. I also read the chart theorem's complete DAG statement, Stacks 07DQ (`algebra.tex`, lemma-matrix-left-inverse), Stacks 01HZ (`schemes.tex`, lemma-f-open), Stacks 01AG and its preceding cokernel/stalk construction in `modules.tex`, and Stacks 04TN/00AL/00AM in `sheaves.tex`. The matrix adjugate, determinant multiplicativity and Cramer DAG statements were checked against the pinned Matrix/Adjugate.lean and Matrix/Determinant/Basic.lean. There are no new nodes requiring additional sources.

Step 1 uses the existing chart theorem exactly for the cover and the formula det(M_J)=p_J/p_I, and the adjugate node exactly for a two-sided inverse after multiplying by the inverse determinant. Reciprocal homogeneous fractions are used only on the overlap where they are defined.

Step 2 uses the same chart minor formula and the determinant multiplicativity clause of the Cramer identities node. It writes the equality for each ordered replacement tuple, including repeated indices, and expands a determinant of an identity matrix with one column replaced. Thus it proves the actual entries of the claimed transition, rather than assuming that matching Plucker coordinates reconstructs a matrix. Both determinant inverses exist by step 1; there is no cancellation of a zero divisor.

Step 3 is elementary: take the I-columns of two products that already equal M^(L). This verifies precisely g_IL=g_KL g_IK, rather than its reverse, including repeated-chart cases.

Step 4 applies the two separate clauses in the module-gluing node's statement, not something hidden in its proof: first objects with transitions F_I to F_K, then the compatible arrows phi_I^{-1} M^(I). The frame equation is phi_K=g_IK phi_I, so these arrows agree. The finite locally free definition says exactly that the displayed frames certify constant rank r. Local right inverses prove sheaf surjectivity. No surjectivity on sections over arbitrary global opens is inferred.

Step 5 uses the basic-open node for openness and an inverse determinant on D(a_I), the adjugate node for the inverse matrix, and determinant multiplicativity for the converse and independence of trivialization. It works on any trivializing open; neither affineness nor reducedness is assumed. This is a local characterization of the frame locus, not a representability assertion borrowed from the item itself.

Step 6 uses the finite-free stalk node to write q_t as an R-linear map, and the exact-stalk node (its clause (5), or its cokernel clause (3)) for surjectivity. The right inverse is constructed by lifting the finitely many standard basis vectors. The explicit formula in clause (2) of the maximal-minor node applies with A=S, B=E_t and f=1, and has exactly the required column minors of E_t and row minors of S. Thus no unquoted transpose-determinant theorem or field-basis extraction is hidden. If all column minors were in the maximal ideal, their displayed finite sum would put 1 in it. The basic-open node then places t in a pivot open. The ring R is a commutative local ring because T is a scheme, and N>=r is already a hypothesis.

Step 7 is elementary: b_I is the basis map q s_I; b_I^{-1}q is forced by normalization and b_I^{-1}b_K is its K-column matrix. The inverse K-column formula follows by composing these very maps. This step is a calculation, not a newly named lemma.

Step 8 reads the tensor definition of module pullback and the definition of a locally ringed-space morphism. On free bases tensor pullback sends coefficients through f-sharp, so the finite determinant formula sends a_I to its pulled-back determinant. The local-ring unit node states that the nonunits are exactly the maximal ideal; the local homomorphism sends that ideal into the target maximal ideal, and any ring homomorphism sends units to units. This proves both directions of equality of the pivot loci. I checked the formula for normalized entries by pulling back the two inverse identities of b_I, and used the pulled-back local right inverses to justify surjectivity of f^*q. No flatness, faithful flatness, or abstract exactness of tensor pullback is invoked.

I checked B1--B10: no new unsplit nodes, no missing-object statements, no fabricated Mathlib leaves or searches, correct source labels, and no project attachment. C1--C8 were checked by opening every cited statement; each non-elementary input has a node and `citations.json` quotes the actual statement, with generic tools declared in `split_report.tool_uses` only. I rejected the small-etale abelian-sheaf epimorphism lemma for this Zariski module argument, and instead used the existing ringed-space module stalk-exactness statement. D1--D5: the proof carries the argument itself, creates no restated clauses, and fills the source's omitted gluing details. E1--E7: all local-ring, rank, invertibility, and arbitrary-base hypotheses were checked as above; no source error was found. Every non-elementary step is below 2000 characters.

Edge cases checked: for r=1 the replacement determinant is just the entry, so the signs and inverse transition reduce to ordinary projective coordinates. For r=N-1 the same formulas use no extra complementary-rank hypothesis. Characteristic 2 changes the sorting signs consistently on both sides. Repeated indices give zero on both sides, not an invalid minor. Nonreduced local rings are allowed because all inverses are taken only for units. Empty test schemes and the zero-ring affine scheme give empty covers with vacuous pointwise coverage, and gluing the empty family gives the unique module. On a nonaffine T the argument is local and never claims q is surjective on global sections. Arbitrary f is allowed because its stalk maps are local and the pulled-back pivot splittings exist without a flatness assumption.

## Unfinished work

None in this one-level split. Existing supporting nodes retain their own current states and are cited without being changed. No Lean was written and no compiler, Lake or build tool was run. The required server dry run and direct delivery are performed after this report is written.
