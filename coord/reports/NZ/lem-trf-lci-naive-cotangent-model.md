1. Files written

- `dag/nodes/sec-trace-formula/lem-trf-lci-naive-cotangent-model.json`: statement, split in ten steps; no exact Mathlib match; no new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for every node used by every proof step.

2. Attachments

None. Searches of the exact blueprint tag and the cotangent/conormal terminology in the read-only project source found no declaration stating every clause. Ordinary Kähler and conormal declarations do not give the standard derived cotangent comparison.

3. WANTED

None. All literature used is present locally.

4. Findings and repairs

The imported statement is retained verbatim. Its statement dependencies now also name the existing polynomial-ring definition used by its phrase “polynomial A-algebra”. I read Stacks cotangent.tex Tags 08RB (lemma-relation-with-naive-cotangent-complex) and 08UP (remark-explicit-comparison-map), algebra.tex Tag 00S1 (lemma-NL-homotopy), its preceding functoriality construction, and Tag 04EG (lemma-localization-formally-etale). The source leaves well-definedness and identification of the comparison unverified. The split supplies these calculations rather than quoting the source's omitted checks as lemmas. Its proof origin is agent-written for those supplied details.

The face-difference chain map initially applies to the canonical presentation R=A[B], not to an arbitrary polynomial presentation P. Steps 1–5 distinguish those objects explicitly and calculate the incoming-boundary cokernel. The arbitrary presentation is handled only afterwards. For P a localization W^{-1}F, the restriction F→B need not be surjective; accordingly the split does not assume that it is a polynomial presentation of B or that localization of such a presentation produces P→B. It instead uses the existing square-zero lifting leaf to compare P with R modulo squared kernels. This handles all multiplicative sets without a localization descent lemma or extra hypotheses.

The final split requires no new nodes. Two uncommitted auxiliary drafts were removed because the explicit calculation and the existing square-zero lifting theorem eliminate their need. Existing searches, citations and source records on the item were retained. An additional semantic search for the full standard-derived truncation statement returned only narrower localization-away conormal-module equivalences; it is recorded with no match after reading LocalizationAway.lean:200–219. The initial dry-run search-log issue was that searches invoked with a proposed child id were logged under that id; their actual records were copied into this item's log without changing the queries or results. No search was invented. The final delivery contains only the existing item, so it has no new-node search obligation.

5. Unfinished work

None in this one-level split. The existing standard-resolution coherence statement remains a cited dependency, as it already was in the imported item.

## Not duplicates

No new nodes. I searched the whole DAG and the blueprint for the naive comparison and the relevant Stacks tags. The existing polynomial-presentation homotopy-equivalence theorem is reused in Step 8, and the existing localization square-zero lifting theorem handles localized polynomial presentations.

## Review by NZ

I checked the final ten steps against the sources and opened every cited node's complete statement. Step 1 takes the actual standard-resolution terms and alternating-face convention from lem-trf-cotangent-resolution-coherence, and the free differential generators from the polynomial Kähler basis leaf. Its Q0, Q1, Q2 and faces are the ones in those definitions. Step 2 uses only the derivation universal property: the difference of the two evaluations is an A-derivation modulo I², and the displayed cancellation proves that rho kills the incoming boundary. This supplies the well-definedness omitted in 08UP.

Steps 3–5 are the explicit module calculation, not an invocation of an unrecorded comparison theorem. I checked each boundary relation separately: t_{X_b}=0 comes from Y_{X_b}; t_{2X_0}=-t_0 comes from 2Y_0; t_{X_0²}=t_0 comes from Y_0²; addition and product relations for h,k in I come from Y_h+Y_k and Y_hY_k. The two products Y_rY_h and Y_rY_0 give B-linearity of v. Both inverse identities are written, including the relation from Y_p-Y_{X_b}. This proves the precise incoming-boundary quotient is I/I² and leaves the lower degrees unconstrained.

Step 6 uses the polynomial universal property to lift R=A[B]→P, and the Kähler universal property to construct chain maps. Step 7 writes the derivation and both chain-homotopy equations for a difference of presentation maps. I checked that this still works for semilinear maps and for maps represented modulo the target's squared kernel: the derivative of that squared kernel vanishes after tensoring with the quotient. It is a direct few-line universal-property computation, not a separately invoked homotopy lemma.

In Step 8 the existing lem-weil-pbc-nl-presentations-homotopy-equivalent statement covers polynomial P and permits any lift a. For P=W^{-1}F I verified all hypotheses of lem-weil-pbc-localization-square-zero-lifting: D=R/I² has an F-algebra structure by lifting the variables, N=I/I² has N²=0, D/N is B by the original surjection, and P→B is an F-algebra map. Its statement explicitly gives the lift ell. The new differential map is obtained from the universal derivation, since d(I²) is zero after tensoring with B. Step 9 checks both compositions against the correct quotient maps, so it proves homotopy equivalence rather than merely an H0 comparison. The derived-category definition justifies passing those homotopies and quasi-isomorphisms to D(B). The polynomial-presentation theorem is declared as a generic tool in split_report.tool_uses; no unit-level trace-formula argument is replaced.

Step 10 checks the actual naturality square: the two maps from R to P' have equal reduction to B' and therefore the explicit homotopy from Step 7 applies. The standard comparison commutes strictly with the standard resolution maps, as the resolution-coherence statement provides. Thus the given semilinear map C(P)→C(P') intertwines the standard functoriality map on L; the target is regarded as a B-complex by restriction of scalars.

I checked the empty variable set P=A, the identity quotient J=0, infinite variable sets (all expressions involve finitely many variables), identity localization, a localization whose restriction F→B is not surjective (for example Z[1/2]→Z[1/2]), the zero ring, and the absence of finite generation or regularity assumptions. The formulas remain valid. The statements of the reused Mathlib leaves were read, including Smooth/Basic.lean's of_isLocalization and comp_surjective and Extension/Cotangent/Basic.lean's definition of the naive complex; none was mistaken for a theorem about the full derived complex. Every citation quote is copied verbatim from its node, proof_deps equals the union of step uses, and all proof steps are below 2000 characters. I reviewed the steps for C1/C4, circularity, unsupported hypotheses and moved clauses; no new node or hidden external result is needed.
