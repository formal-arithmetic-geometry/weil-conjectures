# Worker report

Item: lem-pod-finite-sheaf-h0-augmentation. Group: Q95. Stage 1 only.

## Files written

- dag/nodes/sec-poincare-duality/lem-pod-finite-sheaf-h0-augmentation.json: statement, split using existing nodes; not a Mathlib leaf. Preserved the statement and blueprint metadata, replaced the proof by six explicit steps and recorded the source route and split report. Retained the inherited searches and added the searches actually logged by Q95 in searches.jsonl.
- citations.json: one verbatim statement quote for every step/node citation.
- report.md: this report.

No new nodes; no new Mathlib leaves. No Lean files or repository files were written, and no compiler was run.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag and by finite-sheaf H0/augmentation terminology found no declaration stating all clauses of this item. WeilSheaf/CohomologyDegreeZero.lean concerns compact support with rational Weil coefficients, and AlgebraicGeometry/ProEtale/FiniteCoefficientCohomology.lean concerns constant abelian-sheaf comparison and high-degree vanishing; neither is this arbitrary-module-sheaf augmentation theorem.

## WANTED

None. All sources used are available in literature/.

## Corrections and scope

No statement dispute or statement change. The item is the finite-level section augmentation used by lem-pod-connected-constant-h0, under prop-cohomological-finiteness, current main-20261015 proof Step 7 final paragraph. Its conclusion does not assert that every section of a constant sheaf is constant. In particular, no connectedness or nonemptiness hypothesis was introduced. The proof identifies the specified unbounded derived direct image through a K-injective computation, rather than silently substituting a classical right-derived functor indexed by natural numbers.

The inherited search results were retained. Q95's saved log was read and its general augmentation candidates checked against Mathlib/CategoryTheory/Abelian/RightDerived.lean, especially toRightDerivedZero', its naturality, toRightDerivedZero_eq and the left-exact isomorphism instances (lines 260-370). Those generic facts are already represented by existing DAG leaves; they do not by themselves supply the specified pro-etale total-derived and point-evaluation comparisons. The other Q95 semantic hits concern underived pushforward sections or unrelated augmentation complexes. No search was invented or rerun merely because of the interrupted turn.

## Not duplicates

No new nodes. The existing generic ringed-site, injective-resolution and K-injective computation nodes are reused. Whole-blueprint searches for augmentation, degree zero, and degree-zero cohomology found no imported blueprint node stating this item in another form, so blueprint.same_as remains empty. Its ancestor remains prop-cohomological-finiteness, via lem-pod-connected-constant-h0.

## Review by Q95

I read the node, its parent lem-pod-connected-constant-h0, the chapter and sk-lem-finite unit records, SETUP's three-level rules, and main-20261015 prop-cohomological-finiteness.proof.md, especially Step 7. For the mathematical proof I read Stacks derived.tex Tags 013K (lemma-injective-resolutions-exist), 05TD (lemma-left-exact-higher-derived), 070J (lemma-bounded-below-injectives-K-injective), 013P (lemma-morphisms-lift), and 070Y (lemma-K-injective-defined). I also read injectives.tex Tag 079H (theorem-injective-embedding-grothendieck), its K-injective embedding theorem, and sites-cohomology.tex Tag 07A5 (section-unbounded). These apply to module sheaves on the small ringed site, with arbitrary finite-level module sheaves, not just constructible ones. No SGA route is used.

Step 1 uses the size convention in def-weil-pbc-proetale-site and the exact statement of lem-pur-ringed-site-grothendieck-abelian to obtain a Grothendieck abelian category. lem-sp-grothendieck-enough-injectives supplies enough injectives; clause (1) of lem-weil-pbc-left-exact-injective-resolution-degree-zero supplies the nonnegative augmented resolution; lem-weil-pbc-bounded-below-injectives-kinjective supplies K-injectivity. Each hypothesis is met: the site is small in the selected universe, A_Y is a commutative ring sheaf, and the chosen resolution is zero below zero.

Step 2 uses lem-sfb-grothendieck-k-injective for the all-complex resolution hypothesis required by lem-sf-kinjective-derived-map-computation. I opened the latter's statement: it supplies the normalized comparison c_a, the actual derived-map formula, and transitions for changes of resolution, not just the existence of an abstract isomorphism. def-weil-derived-direct-image selects this K-injective total right derived functor. def-weil-proetale-module-direct-image states both additivity and the sectionwise formula. lem-weil-point-proetale-sections-exact explicitly states that exact sections preserve quasi-isomorphisms and induce the derived functor. Its algebraically closed field hypothesis holds for k. Thus the comparison with the complex I_F(Y) is justified.

Step 3 applies clause (2) of lem-weil-pbc-left-exact-injective-resolution-degree-zero to T=Gamma(s,-) composed with f_*. lem-weil-proetale-module-direct-image-left-exact and lem-weil-point-proetale-sections-exact provide left exactness; additivity and the formula T(F)=F(Y) are in def-weil-proetale-module-direct-image. The cited degree-zero node states the augmentation-induced isomorphism to the kernel, not merely an unspecified isomorphism. The displayed cycle-class formula therefore specifies epsilon. A-linearity follows because all maps are module morphisms and their inverses and kernel factorizations remain module morphisms.

Step 4 is elementary: all negative terms of I_F, hence of J_F by the direct-image formula, vanish. Cycles and boundaries in a zero module are zero. This proves negative vanishing without any assertion about positive degrees or finiteness.

Step 5 uses exactly the strict augmentation equation in lem-weil-pbc-injective-resolution-lift-exists. The nonnegative injective resolutions from Step 1 meet its hypotheses. lem-sf-kinjective-derived-map-computation identifies the induced derived map with the lifted chain map, including changes of resolution; exact point sections then evaluate it. The equation v^0 u_F^0=u_G^0 h gives the written equality of classes. Using h=id with two resolutions proves independence; the comparison statement's cocycle and map compatibility ensure that these are comparisons into the same specified C_F. No uncited homotopy uniqueness assertion is needed.

Step 6 uses only the definitions def-weil-pbc-constant-sheaf, def-weil-finite-coefficient-point and def-weil-ordinary-compact-cohomology: finite point evaluation is Gamma(s,-), ordinary cohomology is H^0 of the evaluated direct image, and A_Y is the constant sheaf of rings. Substitution in the explicit augmentation formula sends a_Y to its augmentation class, including a=1. This is elementary after Steps 2-3. I did not use the false assertion that constant-sheaf sections always equal A.

For C4, I opened every cited node and checked the statement, then checked every citations.json quote is literally a substring of that statement, and checked that every (step,node) pair is present exactly as required. For C1, the genuinely non-elementary inputs are all existing statement nodes: Grothendieckness, enough injectives, nonnegative resolutions, K-injectivity, all-complex resolution existence, normalized derived-map computation, left exactness and lift existence. Definitions are used only for the objects and formulas they actually specify. No new clause-restating node or hidden identification was introduced. All six proof steps are under 2000 characters; no long step hides a lemma. proof_deps is the union of the uses lists.

Small cases: F=0 gives the unique zero-module isomorphism. Empty Y gives F(Y)=0 and the zero unit class, as required; no nonzero unit or injection of A into sections is asserted. A disjoint union of two points allows A_Y(Y)=A times A, with epsilon defined on all pairs and the scalar section a mapped diagonally. For Y=s, the construction reduces to the ordinary augmentation isomorphism of an exact sections functor. Negative j=-1 is covered even though J^0 can be nonzero, since J^{-1}=0. No finite-cohomology, constructibility, properness, smoothness, or connectedness hypothesis was used without being present.

The remote review_split check passed with zero new nodes. This continuation preserved the saved proof and citation work; its changes complete the report and retain Q95's logged searches. The required delivery dry run and push follow this review.

## Unfinished work

None within this stage-1 split. The existing dependency nodes retain their own statuses and are not claimed proved by this delivery.
