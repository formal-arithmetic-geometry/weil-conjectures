# Stage-1 delivery: lem-zl-condensed-global-frobenius-comparison

## Files written

- dag/nodes/sec-zeta-weil/lem-zl-condensed-global-frobenius-comparison.json: existing statement split into eight steps; statement, statement dependencies, original searches, source, ancestry and imported metadata retained.
- dag/nodes/sec-zeta-weil/lem-zl-model-compact-comparison-unit.json: statement-only implementation-normalization lemma, unsplit, no Mathlib match.
- dag/nodes/sec-zeta-weil/lem-zl-proper-unit-condensed-realization.json: statement-only proper-unit comparison through whole coefficient towers and condensed realization, unsplit, no Mathlib match.
- citations.json: a verbatim statement excerpt for every citation in every proof step.
- searches.jsonl: actual msearch records; the two new nodes use their own relevant queries, each with LeanFinder, Loogle, LeanSearch, grep, and a second semantic phrasing. All services answered. The later declaration-name grep was also read; it is not represented as a separate theorem match.

## Attachments

None. I searched WeilConjectures in the read-only slopmaster2 source for the exact blueprint tag, global Frobenius comparisons, and compactCohomologyFrobeniusComparison/weilCompactCohomology. I also checked the named upstream master reference. No declaration there states the specified conjugacy. The abstract finite-coefficient lowerShriekExchange in SixFunctors/ProEtale/TraceFormula/Frobenius.lean:620–689 supplies useful construction evidence, but it is neither the actual PR1473 module-object implementation nor an exact attachment for this statement.

## Wanted sources

WANTED: literature/upstream-pr1473-495bc3883/, especially the declaration compactCohomologyFrobeniusComparison and the definition of weilCompactCohomology used by TraceFormula/Statement.lean in PR1473, for lem-zl-model-compact-comparison-unit. The existing nt-assume-trace-formula node cites this archive, but it is absent from this read-only literature snapshot, and neither supplied source checkout contains those named declarations. I did not download or invent its text. The normalization is isolated as a new unsplit obligation rather than treated as an already proved unfolding. Its source record explicitly distinguishes the finite blueprint recipe from the concrete module-object assertion.

## What was wrong or missing

The item was a newly created, unsplit comparison obligation, not a verbatim theorem of the rationality blueprint. The object comparison in lem-zl-assumed-trace-determinant-bridge expressly excludes global Frobenius equality. Equivariance cannot be inferred from its object isomorphism. Similarly, the compact-support realization theorem preserves morphisms and refinements but does not state preservation of the specified proper-unit map through the finite coefficient tower. Those are the two new obligations. They are infrastructure comparisons without a geometric Frobenius conclusion, not copies of the requested conjugacy.

The geometric convention is retained. The model map fixes k; the Galois map g_Y need not be k-linear. They are compared through the canonical finite-level kappa, never identified as scheme maps. The q^m convention in the item is not changed. No statement dispute was found.

The item is not its unit's key statement, so no unit realization record was changed. The proof stays within the first sentence of the rationality route, identifying the Frobenius in the trace-to-determinant input; cross-unit coefficient and graph results are explicitly declared as tool uses.

## Not duplicates

lem-zl-model-compact-comparison-unit vs prop-trf-graph-operator: the existing node computes a finite-A graph correspondence operator; the new node compares the named concrete condensed module-object compactCohomologyFrobeniusComparison with its proper-unit composite, before a Weil coefficient map is supplied.

lem-zl-model-compact-comparison-unit vs def-trf-weil-shriek-pushforward: the definition gives a finite-A exchange recipe for relative Frobenius; it says nothing about equality with the named concrete condensed implementation.

lem-zl-model-compact-comparison-unit vs nt-assume-trace-formula: the latter names the concrete comparison and operator but does not identify that comparison with the proper-unit formula. The new node asserts no trace formula.

lem-zl-proper-unit-condensed-realization vs lem-pur-compact-support-condensed-realization: the existing theorem supplies natural compact-support coefficient isomorphisms; the new node asserts the equality for the specified adjunction unit and its coherent finite-output tower. Naturality in an input morphism alone does not give this square involving h-pullback and direct-image composition.

lem-zl-proper-unit-condensed-realization vs lem-weil-pbc-condensed-e-realization: the existing theorem transports individual pullback/direct-image adjunctions and a proper cartesian exchange at the E-stage; it does not compare compact-support proper-unit maps from whole finite towers through Omega and point realization.

lem-zl-proper-unit-condensed-realization vs lem-trf-compact-support-system-realization-normalization: that theorem compares geometric-Galois automorphism exchanges and their integral system normalizations, without an adic-to-condensed comparison or the proper k-endomorphism unit considered here.

lem-zl-proper-unit-condensed-realization vs lem-trf-frobenius-transports-scalar-extension: that theorem concerns finite E-to-M adic coefficient changes and geometric Frobenius, not realization into the actual condensed Omega module-object category.

lem-zl-proper-unit-condensed-realization vs lem-weil-pbc-condensed-coefficient-point-unit-pasting: that statement concerns sections of an arbitrary condensed abelian sheaf along an algebraically closed field embedding, not the derived compact-support unit of a proper endomorphism or a coefficient tower.

lem-zl-proper-unit-condensed-realization vs lem-weil-pbc-qbar-condensed-push-counit: the latter is an abstract adjunction mate identity after restriction to predicates. It does not construct or normalize the strict finite-coefficient compact-support tower or identify its limit with the actual condensed unit.

I searched the whole DAG and blueprint by proper unit, compact support realization, compactCohomology, proper endomorphism, coefficient comparison, and the concrete declaration names. The source tags used to understand the standard adjunction calculus are Stacks 07A6 (sites-cohomology-lemma-adjoint), 0E46 and 0E47 (the two composition-of-base-change remarks), read in sites-cohomology.tex. Neither new statement is attributed to those generic Stacks facts: their source records identify the actual agent-formulated obligations.

## Review by NJ

I read the chapter and sk-thm-rationality unit, the current main-20261015 rationality proof's first sentence, the current sk-d-weil definition, prop-trf-graph-operator.proof.md and prop-trf-graph-frobenius-operator.proof.md, and the rational integral-model proof. For the second new node I read Bhatt–Scholze Definition 6.7.6, Lemma 6.7.7, Remark 6.7.8, Lemma 6.7.14, Proposition 6.8.14(2), and Remark 6.8.15. They give the separately derived proper/open construction and the field equivalence; they do not literally assert the new normalization equation. In particular I did not replace the separately derived proper/open composite by the derived functor of the underived composite, which Remark 6.7.8 explicitly rules out. The first new statement is grounded in the blueprint proper-unit recipe and the supplied slopmaster2 lowerShriekExchange construction; the missing exact PR1473 source is recorded above, and its concrete normalization is left as a real theorem obligation.

For Step 1 I opened the statements of the constant-datum theorem, the constant coefficient constructibility theorem, the canonical Weil-structure definition, finite Tor amplitude and the rational integral-model theorem. Together they provide the actual normalized integral lattice and reductions, and theta_E is the image of theta_R. The finite Tor condition is checked explicitly by the coefficient unit, uniformly in n, not inferred from bounded constructibility. The integral-model theorem is applied with the specific canonical u and N=0.

For Step 2 I read both the graph/geometric comparison and the rational-model theorem in full. The graph theorem states the canonical kappa normalization and the finite-A operator equality; the latter theorem states the whole-tower realization U_m, not only agreement of separate reductions. The integral recurrence theorem supplies the same V_m. Separated finite type and ctf are already available. For Step 3 I checked the domain of every factor in the recurrence: c_m maps P_1 P_m M to P_(m+1) M. Naturality moves H(P_1 u^[m]) across V_(1,P_m M). This gives U_(m+1)=U_1 U_m without presuming a faithful evaluation functor. The rational-model theorem explicitly identifies m=1 with the global-geometric definition, including its point transport. Thus the induction gives actual powers F_E^m.

For Step 4 the assumption node supplies the identity of G_m with the Weil compact-support coefficient map composed with its named comparison; the new implementation node supplies the additional proper-unit equality. It would be a C4 error to take that equality just from the assumption, so it is not done. Step 5 uses the second new statement for exactly its proper-unit square. I checked h is proper by finite model Frobenius, finite-implies-proper and composition. The pullback of the constant coefficient unit is the unit at each quotient and remains the unit after completion. The bridge gives bounded finite-dimensional rational cohomology and exactly the chosen sigma_Y; for M' the unit identification gives the same cohomology complex.

For Step 6 I checked that the bridge asserts realization of the normalized integral model Weil map, with pullback-composition iterates. The constant-datum node fixes the initial map and kappa; the E-realization theorem states preservation of pullback compositors. The induction therefore identifies the iterates without a new scaling. The new proper-unit theorem states naturality on whole systems, which is the premise for moving v_m past b, not an assumption that sigma is already Frobenius-equivariant. All displayed factors land in the b_(M') source before reaching rho(C_(M')).

For Step 7 the graph-operator node states the finite proper-unit formula, while the rational-model theorem gives its coherent integral realization. The new proper-unit node includes that same simultaneous unit/composition tower and its naturality on coefficient maps; this is why the integral composite is the one realized in Step 2. Step 8 uses the point-supertrace node only for its functor and natural cohomology comparison, not for any trace identity. Applying cohomology preserves the previously proved conjugacy and powers. Every cited node was opened and its actual statement, rather than its proof, checked. citations.json contains the verbatim statements or relevant clauses used.

Small cases: for the first new lemma, X empty and M=0 give the unique zero map; X_0=Spec k_0 gives h=id and the adjunction unit/compact-support comparison is the identity. On a nonreduced model the Frobenius is still finite; the statement did not assume a scheme isomorphism. For the second new lemma, h=id gives the identity on the whole tower, zero M gives the zero-object identity, and the constant unit specializes to the ordered unit formula with no arbitrary scalar. The lemma asks for no Weil structure or Frobenius. I also checked a nonidentity coefficient map on a constant rank-two object: the naturality square involves the same matrix on both sides, so it does not force an operator to be the identity. The geometric A^1 convention is carried by the existing finite graph theorem; I have not used a trace identity, a duality statement, or an unsupported separate computation of its top cohomology.

Against B–E: both new nodes are self-contained statement-only obligations, with their coefficient categories and hypotheses explicit, complete blueprint ancestry and actual logged searches. No new definition or Mathlib leaf is claimed. The generic adjunction search hits are insufficient for either concrete comparison. The existing finite graph, integral recurrence and coefficient equivalence nodes are reused. No new node is elementary, a duplicate, or the full conjugacy under another name. I corrected an initially inappropriate E-only adjunction-definition citation in the implementation node to the restricted-functor definition that explicitly covers Omega. I also corrected the proper-composition id before writing the parent. All eight steps have fewer than 2000 characters, so no long-step sublemma is hidden. There are no Lean edits, compiler runs, live-project writes, or SGA citations.

## What remains

The two new nodes intentionally remain unsplit for the next DAG level. There is no unfinished portion of this one-level split. The report does not claim that those obligations are already proved. Server check_dag passed; server review_split passed. The required delivery dry run and push follow this report and are the authoritative packaging checks.
