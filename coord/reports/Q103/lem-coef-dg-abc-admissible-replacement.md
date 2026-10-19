# Stage-1 worker report: lem-coef-dg-abc-admissible-replacement

## Files written

- `dag/nodes/sec-six-functors/lem-coef-dg-abc-admissible-replacement.json`: statement, not a Mathlib leaf; unchanged statement, now split into six explicit proof steps.
- `citations.json`: the single proof citation, to the definition of a dg category in `lem-coef-dgcat-model-structure`.
- `report.md`.

New nodes: 0. Mathlib leaves: 0. Removed the earlier attempt's uncommitted `lem-coef-dg-abc-cone-identity-contractible.json`: its conclusion is a two-equality calculation from the item's axioms, now written in Step 2. The earlier child also referred back to its parent for hypotheses and omitted the shift map in its contracting homotopy.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the full item id and blueprint tag, `09QN`, `09QM`, admissible monomorphisms/replacements, and dg-category terminology. No matching project declaration was found. Ordinary derived-category and t-structure declarations are not this abstract dg-category result. Upstream master was not treated as a finished proof.

## WANTED

None. All mathematical source used is in `literature/stacks-project/dga.tex`.

## What was checked and corrected

Read the item, `sec-six-functors` chapter, `sk-prop-sf-biduality-general` unit, and the current `main-20261015` statement and proof of `prop-coef-integral-exceptional-adjoint`. The latter's paragraph 2 supplies the inherited ancestry through enriched adjunctions, dg modules and their finite-cone triangulation. The local proof keeps that ancestry and the unit metadata. It changes no target, coefficient category, unit record, or chapter route.

Read Stacks `dga.tex` section `section-review`: Tags 09P6 (`lemma-get-triangle`), 09QJ (`situation-ABC`), 09QK (`lemma-id-cone-null`), 09QM (`lemma-factor`), and 09QN (`lemma-analogue-sequence-maps-split`). Verified the tags against `stacks-project/tags/tags`. The item is 09QN with its axioms spelled out and the initial identity choice supplied by the source induction. Its statement requires no correction.

The earlier sandbox's proposed quotient was the dg direct sum of y and x[1]. Its quotient map used the graded cone retraction pi, which is generally not closed. The earlier matrix checks consequently proved only a graded splitting and did not establish an admissible sequence of closed maps. Replaced this quotient with an actual cone C(alpha), supplied by the existing axiom (C), and checked closedness before the splitting equations. No existence of kernels, cokernels, abelian-category structure, functorial cones, or triangulated-category axiom is used.

## Source error

Tag 09QM displays the quotient x[1] for the injection x -> y direct-sum C(1_x). This fails already in the concrete dg category of complexes, with x=0, y=Z concentrated in degree zero, and the standard choice C(0)=0: the displayed sequence is 0 -> y -> 0, whose graded splitting identities would force 1_y=0. The quotient also cannot generally be replaced by the dg direct sum y direct-sum x[1] with the earlier sandbox's map: its first component has differential alpha eta_x bQ. For x=y=Z[0] and alpha=1, this is nonzero on the shifted cone summand. The correct quotient in Steps 4-5 is C(alpha), and its off-diagonal differential cancels that term.

The last paragraph of Tag 09QM also writes that 1_x is a boundary. It is the identity of C(1_x) that is a boundary by 09QK; 1_Z[0] is not null-homotopic. Step 2 explicitly contracts 1_C using t theta_x pi. These are repairs of the source's proof, not changes to the item's conclusion. The replacement proof is marked agent-written because it supplies the missing quotient construction.

## Not duplicates

No new nodes remain. Searched the whole DAG by Tags 09QK, 09QM, 09QN, labels and admissible-monomorphism terminology, and searched the imported blueprint using `tools/blueprint_refs.py search 'identity cone'` and `search 'admissible replacement'` (both returned zero blueprint matches). Checked the existing `lem-coef-dg-abc-cone-homotopy` statement: it compares an already admissible quotient with a cone and does not supply the closed quotient needed here. It is not used. The single-arrow factorization is the N=2 case of this very item, so it is proved here, not moved to a child. The contraction and matrix identities are elementary calculations, also kept here.

## Mathlib searches

Retained the item's existing search records and ran fresh searches through the mandated `msearch.py` wrapper: LeanFinder with two phrasings, Loogle for `CochainComplex.mappingCone, HomotopyEquiv`, LeanSearch for finite dg diagrams, and grep for dg/admissible terminology and the closest factorization API. Exact query strings and actual wrapper-log results are recorded in `mathlib_searches`; no unavailable service is called a negative match. Read all returned names and types. Read `Mathlib/Algebra/Homology/Factorizations/CM5b.lean`, especially its variables at 30-32 and `homotopyEquiv` at 110-121, and `HomotopyCofiber.lean` around its cylinder definition. These concern actual homological complexes; CM5b additionally assumes an abelian category with enough injectives. None supplies this construction for arbitrary small dg categories by one-line specialization. No new node needs a search or a Mathlib match.

## Review by Q103

I read the Stacks statements and proofs listed above against the unchanged item, including its closed-map conditions, boundary normalization, and the requirement that every square commute strictly. The six steps have the following precise inputs and checks.

Step 1 cites only the sentence of `lem-coef-dgcat-model-structure` defining a dg category to have associative unital chain-map compositions. That sentence is copied verbatim into `citations.json`. It gives the dg Leibniz rule by the tensor differential formula; none of that node's model-structure assertions is used. The rest of Step 1 differentiates the item's own five splitting identities and uses its boundary condition (C) to derive partial(s_f)=a_f f eta_x and partial(pi_f)=-f eta_x b_f. This is exactly the calculation in 09P6, with the shift isomorphisms made typed: theta_x has degree -1, eta_x degree +1, both closed and inverse by composition compatibility in (B). The derivative formulas are proved in the step, not borrowed without a node citation.

Step 2 has no external citation: for the identity cone it substitutes those formulas into the Leibniz rule to get partial(t theta_x pi)=a pi+tb=1. This is the full 09QK proof, a two-equality calculation, so making an unsplit child for it would violate the elementary-node rule. Checked all degrees and the negative Leibniz sign on the degree-minus-one composite t theta_x.

Step 3 uses only the already proved contraction and axiom (A). The inclusions and projections are closed, so j=I alpha+Ja and r=P are closed, rj=alpha and rI=1. The explicit degree-minus-one homotopy JhQ has differential JQ=1-IP. This proves the homotopy-equivalence clause, not just invertibility after localization.

Step 4 uses (C) again for the original alpha, producing the actual object D=C(alpha), with closed a',b' and graded pi',t'. The map q=a'(P-alpha pi Q)-t'bQ has degree zero. Its derivative is a' alpha eta_x bQ-a' alpha eta_x bQ=0 by Step 1, and qj=0 by pi a=1 and ba=0. This is where the earlier sandbox failed: a graded map cannot be called closed merely because it has a graded splitting. Both differential terms are now written explicitly.

Step 5 has no non-elementary input. Expanding products gives rho j=1, rho sigma=0, q sigma=1, j rho+sigma q=1, with rho=pi Q and sigma=I pi'-Jtb'; qj=0 was proved in Step 4. I checked each using pi t=0, b t=1, pi' t'=0, b' a'=0 and b' t'=1. All splitting maps have degree zero; they are not assumed closed. Together with the established closedness of j and q, these are precisely the item's admissibility definition. The quotient object is not silently identified with its graded decomposition.

Step 6 explicitly states the induction invariant, starts at N=1 with the identity, and applies the already proved construction to the closed composite f_(N-1) r_(N-1). The resulting equation is exactly r_N j_(N-1)=f_(N-1) r_(N-1), with no homotopy correction and no dependence on a future step. The previous initial equality and squares are retained. N=2 is obtained from this same induction; it is not assumed as an external lemma.

All six steps are elementary relative to the stated axioms and the preceding written calculations. No non-elementary fact is hidden behind a source citation, no newly created theorem restates a clause of the item, and there is no recursive dependency on the item. The only cited node is used for exactly the definition its statement gives; the proof dependency list is exactly the union of uses. In particular there is no unrecorded use of a proof of another node.

I tested N=1, N=2, zero source, zero target, the zero arrow and the identity arrow in ordinary complexes. For alpha=0 the quotient is a cone of zero, with the indicated negative sign on the x[1] quotient component. For alpha=1 on Z[0], the extra identity cone is contracted but x itself is not; the quotient is the cone of the identity, as required. The formulas also allow repeated objects, arbitrary finite lengths, and Hom torsion: no division, characteristic assumption, boundedness, cohomology, or finiteness of Hom groups is used. All sources are permitted Stacks sources; no SGA route is introduced.

Corrections to the earlier attempt: replaced its nonclosed quotient, inserted the missing shift map in the contraction, removed the elementary child and its back-reference, regenerated the exact citation quote, and expanded the induction and source-error record. The statement and its hypotheses remain unchanged.

## Unfinished work

No mathematical gap remains in this one-level split. Independent second reading and delivery belong to the next worker. This worker runs only the no-push dry run.

## Restart review by Q103

The restarted worker reread the actual Stacks source at Tags 09P6, 09QJ, 09QK, 09QM and 09QN, the current blueprint exceptional-adjoint proof, the chapter and unit records, and the sole cited node's statement. The recorded two errors in 09QM are present in this checkout. I independently expanded q sigma and sigma q: the mixed terms vanish by pi' t'=0 and b' a'=0, leaving a' pi'+t' b'=1_D and I(P-alpha pi Q)+JtbQ respectively. Differentiating q gives two opposite a' alpha eta_x bQ terms, so no closedness assumption on the graded splittings was used. This confirms the substantive repair in the earlier attempt; no new dependency is needed. The induction uses only the constructed single-arrow factorization and closedness of composition, including the one-object case.

I repeated both LeanFinder phrasings, the Loogle pattern, LeanSearch and the factorization-source grep through msearch.py. The actual latest log records replace the corresponding earlier results. I read the returned APIs and their hypotheses: CM5b.lean:30-32,110-123 assumes an abelian category with enough injectives; Pretriangulated.lean:208 and Triangulated.lean:139 concern ordinary cochain complexes; HomotopyCofiber.lean defines the cylinder of a HomologicalComplex. None is a direct Mathlib leaf for this arbitrary-dg-category statement. The DAG/tag and blueprint searches found no alternative node stating the item. The Lean source search by id, tags and dg/admissible-replacement notions yielded no attachment.

The restart corrected one escaped control character in Step 5's source place to the proper TeX alpha. A JSON comparison confirms the statement, metadata and ancestry are unchanged from the shared base; only the permitted split fields and search records differ. I checked the one citation quote verbatim against the cited statement. The earlier mathematical repair and all five admissibility identities remain intact. There are no new nodes, so statement-only children, new-node duplicate pairs, and new-node edge-case checks do not arise; the edge cases and source counterexamples above have been rechecked.

## Dry run

Final validation uses `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q103 lem-coef-dg-abc-admissible-replacement --no-push` against these files. READY is reported only after this command returns `OK (not pushed)`. The sandbox is then left unchanged for the independent second reader. No delivery is pushed.

## Earlier second reading (a previous round; superseded)

- Item statement: checked every hypothesis and clause against Stacks `dga.tex`, Tags 09QN/09QM and Situation `situation-ABC`; verdict: unchanged and faithful, including strict closed squares, shifts, boundary normalization, and the cases `N=1` and `N=2`.
- Step 1: checked the dg Leibniz rule against the cited `lem-coef-dgcat-model-structure` definition and equations (1)--(6) of Tag 09P6; verdict: the two differential identities for the cone splitting are explicitly derived and typed.
- Step 2: checked the degree signs, shift maps, and contraction against Tag 09QK; verdict: `h=t\theta_x\pi` has the stated degree and `\partial h=1_C` follows by the displayed calculation.
- Step 3: checked the direct-sum maps and homotopy inverse against axiom (A) and Tag 09QM; verdict: `j`, `r`, and `H` are correctly typed, closed where required, and `\partial H=1_M-IP` proves the homotopy equivalence.
- Step 4: checked the cone quotient `D=C(\alpha)`, the differential cancellation, and `qj=0` against axiom (C), Tag 09P6, and the source-error example; verdict: the quotient map is closed and uses the actual cone rather than a merely graded direct sum.
- Step 5: checked all five admissibility identities by expansion from the two cone splittings; verdict: `\rho`, `\sigma`, `q`, and `j` have the required types and every identity is written, with no hidden closedness assumption on graded splittings.
- Step 6: checked the induction invariant and composition `\alpha=f_{N-1}r_{N-1}` against Tag 09QN; verdict: the base, induction step, strict commutative square, and homotopy-equivalence data establish all clauses for every finite `N`.
- New nodes: none; there are no child statements to audit, and the cited existing node was searched and checked for the exact quoted definition.
- Edge cases and source repair: rechecked zero objects, zero and identity arrows, `N=1`, `N=2`, and the concrete-complex counterexample to the quotient in Tag 09QM; corrected that counterexample's wording to specify `C(0)=0`.
- Delivery audit: citations quote the dependency statement verbatim, all recorded searches are actual wrapper results, no SGA source is used, and the split has no extra files or nodes.

Changes made in the second reading:

- Specified the standard choice `C(0)=0` in the source-error counterexample, so the displayed middle object is exactly `y`.
- Added this independent statement, step, citation, and edge-case audit. The six proof steps and their single citation passed the reading without alteration.

## Second reading by Q103

- Item statement: checked against Stacks `dga.tex`, Situation ABC and Tags 09QN/09QM; verdict: hypotheses and conclusion match the finite composable closed-map replacement, with explicit strict squares and the valid `N=1` edge case.
- Step 1: checked against Tag 09P6 and axiom (C), using the cited dg-category composition statement; verdict: the Leibniz differentiations and the two identities for `∂s_f` and `∂π_f` are written and typed.
- Step 2: checked against Tag 09QK on the identity cone; verdict: the degree-minus-one contraction and its sign give `∂h=1_C` explicitly, so no child node is needed.
- Step 3: checked against Tag 09QM and the identity-cone contraction; verdict: the direct-sum factorization, closed homotopy equivalence, and `∂H=1-IP` are explicit.
- Step 4: checked against Tags 09P6, 09QJ and 09QM; verdict: the quotient is the actual cone `C(α)`, its differential cancellation is shown, and `qj=0` follows from the splitting identities.
- Step 5: checked each of the five admissibility identities against the two cone splittings; verdict: all products are expanded, with no unstated closedness of graded splittings.
- Step 6: checked against Tag 09QN; verdict: the base case, induction invariant, closed composite, strict square, and retention of earlier data prove every finite length.
- New nodes: none; DAG and blueprint searches found no duplicate or Mathlib leaf needed, and the sole cited node’s quoted definition is verbatim in `citations.json`.

Changes made: corrected the item node’s `created.item` from the unrelated homotopy-category target to this item so preflight recognizes it; added this independent second-reading record. No statement, proof step, citation, or search result required mathematical alteration.
