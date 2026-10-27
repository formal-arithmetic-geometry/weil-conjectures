## Worker report

This is a stage-1 re-split under coord/repair-notes/lem-trf-implicit-taylor-coordinate-calculus.json, released on 2026-10-22. Its explicit reopening is the exception now written in coord/brief-stage1.md §1 and the isolated-run rule. It supersedes the previous retries' interpretation that A7 made the assignment closed. The initial dry run in this retry exited 1 with unchanged-item, 3000-character assembly and four-new-node diagnostics. Those diagnostics are now addressed substantively.

### Files written

- dag/nodes/sec-trace-formula/lem-trf-implicit-taylor-coordinate-calculus.json: statement and stmt_deps unchanged; five assembly steps, 2758 characters; existing Q27 Lean record preserved in full.
- dag/nodes/sec-trace-formula/lem-trf-formal-transverse-shift-calculus.json: statement; unsplit, no exact Mathlib match; no proof or proof dependencies. Formal transverse shift, coefficient extraction and graph factorization.
- dag/nodes/sec-trace-formula/lem-trf-etale-graph-taylor-comparison.json: statement; unsplit, no exact Mathlib match; no proof or proof dependencies. Infinitesimal comparison with the graph of an etale closed subscheme.
- dag/nodes/sec-trace-formula/lem-trf-etale-coordinate-derivations-jacobian.json: statement; unsplit, no exact Mathlib match; no proof or proof dependencies. Coordinate differential basis, regular derivations and Taylor comparison.
- dag/nodes/sec-trace-formula/lem-trf-diagonal-taylor-faithful-flatness.json: statement; unsplit, no exact Mathlib match; no proof or proof dependencies. Faithfully flat Taylor realization at the residue-field diagonal point.
- citations.json: every assembly step/node pair, with a verbatim quotation of the cited statement.
- report.md: independent source review and the complete retained fifteen-step argument, partitioned by destination below. Research/search outputs and previous-stage1-node.json are sandbox material only.

### Attachments

None. The exact blueprint-tag and implicit-Taylor searches in lean/WeilConjectures found no attachment. AlgebraicGeometry.HilbertCoefficient.implicitTaylorCoordinateCalculus, lean/Sheaf/AlgebraicGeometry/ImplicitTaylorCoordinateCalculus.lean:400, ends with sorry at line 421. It is not a finished proof. No Lean was written, compiled or rebound.

### WANTED

WANTED: Bierstone--Milman, Invent. Math. 128 (1997), 207--302, Lemma 3.5 and Remarks 3.7, 9.9, 9.11, for contextual comparison with lem-trf-implicit-taylor-coordinate-calculus. This journal text is absent from the named repository literature. No download was made and no unavailable theorem from it is used as a black box. The proof remains agent-origin, with explicit Stacks inputs.

### What was wrong and what changed

The superseded packet improperly delivered a stage-2 existing:true rebind on the stage-1 lane. The current packet leaves Q27's full existing:false record, owning file, module and declarations intact (H2), contains no stage-2 edits or compiler activity (A3/H1), and supplies Review by Q62 (A2). A7 is resolved by the explicit released stage-1 human repair order, not by repushing the old mathematics. The new delivery contains four genuine subarguments and a new assembly proof. The parent statement, hypotheses, statement dependencies, route, maintainer fields and all blueprint/import metadata are preserved. There is no statement dispute or route replacement. The return's 2002-character step is now the 968-character first assembly step using the existing pointwise criterion, not an unexamined long step.

The old proof's non-elementary differential, completed-diagonal, lift-comparison and formal-coefficient arguments are now separate statement-only tasks. New nodes are not proved here. The finite-generator ideal contraction and neighbourhood argument stays elementary in the assembly. The full old text below is retained as proof material for future workers; no argument is deleted or blurred.

### Unfinished work

The four new nodes intentionally remain unsplit for independent workers, as the human order requires. Their proofs are supplied as retained research material in this report, not as proof fields or covert proof sketches in their statements. Stage 2 and Lean proving are outside this assignment.

## Review by Q62

I read SETUP.md's chapter/unit/node distinction, GOAL.md, roles/worker.md, stages/1-dag.md, delivery-errors.md B--E in full, and the chapter sec-trace-formula and unit sk-i-curve-zero. I also read the main-20261015 locality blueprint node. Its current contracting-correspondence route is unchanged: this item belongs to the historical resolution/coefficient-data branch recorded by its existing blueprint ancestry. No new chapter or unit edge replaces that route. I reread the actual released repair note; unlike the old report, I honor its explicit reopening even though both existing review records are present.

For the parent and each new node I read the source statements and relevant arguments in algebra.tex: 0H93 lemma-formally-etale-omega, 00RX lemma-differentials-polynomial-ring, 0H1D lemma-formally-etale-lift-infinitesimal, 00HT lemma-flat-localization, 00HR lemma-local-flat-ff and 00MC lemma-completion-faithfully-flat; morphisms.tex 02GU lemma-etale-at-point; and more-morphisms.tex 04FF lemma-unramified-flat-formally-etale. I read the ILO PDF at PDF pages 98--100, printed pages 92--94, including VIII 2.3.11 and 2.3.13: these are resolution context, not a source asserting this coefficient-calculus theorem. The four new sources identify the agent consequences separately from the supporting tags, without claiming a tag states the whole compound lemma.

For the coordinate-derivation node, 0H93 and 00RX give the coordinate differential basis, and the universal property gives derivations with arbitrary target module. The commutator is again a derivation and vanishes on that basis; the two derivations into the Taylor target agree on all coordinates. Restriction and localization preserve the universal property, so regularity and germ compatibility are not analytic differentiability claims. This node assumes an etale chart and finite type, with no characteristic restriction needed for this argument.

For the diagonal-Taylor node, 0H1D gives canonical quotients for P -> C, with C/J=L and I=(X). The localizations do not change these quotients because elements outside J have invertible residue and hence inverses modulo J^q. A compatible truncated polynomial family is a formal coefficient family. J contracts to the original prime, so 00HT and 00HR apply to A_p -> C_J. The rings are Noetherian since the chart algebras are finite type over fields; 00MC applies to C_J and proves faithful flatness of its completion. Successive preservation/reflection of exactness proves faithful flatness of the composite. No dimension equality or algebraicity of L/k is used. Naturality is the canonical quotient-map naturality of the existing augmented-etale node. The existing rational-point Taylor-isomorphism node gives the completion identification but does not give faithful flatness of the original local ring at a possibly nonclosed point; it is not a duplicate.

For the graph-comparison node, I checked its two etale hypotheses independently: A over k[w,y] and the quotient D over k[w]. The two maps to L[[W]]/(W)^q agree on the first coordinate algebra and modulo (W); 04FF gives unique lifts through each square-zero kernel. This yields the restriction identity. An arbitrary solution kills the defining ideal and therefore factors through D; the second etale hypothesis gives its equality with sigma. This proves uniqueness without assuming the point is closed. Denominators outside the evaluation prime have nonzero constant coefficient, which is precisely what permits the germ comparison. The statement takes no Jacobian conclusion for granted: it only assumes the two charts, and the parent supplies the second chart in assembly step 1.

For the formal-shift node, I checked the coefficient-family definition and read the actual MvPowerSeries substitution and pderiv declarations. Positive order of phi makes every bounded-degree coefficient finite. The inverse is the negative shift. A series vanishing on the graph can be divided monomial by monomial after shifting: allocate each monomial to the least transverse variable with positive exponent. The constant matrix is the given transverse Jacobian, and its formal geometric-series inverse exists. This is a separate ring calculation, with no scheme, regularity, local-ring flatness or implicit-existence assertion. The binomial coefficient equals the falling factorial divided by delta!, and only that division uses characteristic zero. The unrestricted T family is legal because T exponents are fixed by substitution. This node is much smaller than the parent and is not merely a renaming of its geometric coefficient clause.

Assembly step 1 uses the differential-basis statement of the new coordinate node. I opened def-sc-relative-differential-sheaf and lem-weil-pbc-spec-tilde-stalk-localization: they identify the affine differential module and its stalk with precisely the fibre required by lem-pur-etale-at-point-from-differentials. I opened that criterion: its smooth, finite-type, field and differential-basis hypotheses all hold here. The block triangular calculation is explicit. I opened lem-weil-pbc-etale-scheme-base-change: it gives etaleness of N -> A^m, not just smoothness. sbc-lem-affine-space-smooth, lem-weil-pbc-etale-smooth-zero-dimensional-fibres, lem-weil-pbc-smooth-ring-map-iff-smooth-affine and lem-weil-pbc-smooth-ring-map-base-change-composition give exactly the claimed smooth composite. Existing approved tool uses are retained; no new off-route tool approval is manufactured.

Assembly step 2 takes construction, arbitrary-point faithful flatness and coefficient-field naturality from the new diagonal node's statement. Its chart hypotheses hold for both B and N by step 1. Step 3 takes the graph and restriction identity from the new quotient comparison with D=A/(h). Step 4 takes the formal derivative/Taylor identity from the coordinate node and the shift, matrix factorization, factorial extraction and field naturality from the formal-shift node. Its constant Jacobian is D_yh(b) by the coordinate derivative identity, so invertibility is verified on exactly the open chosen in step 1. It applies to each f_gamma=tau(c_gamma), without a finite-support restriction.

Assembly step 5 uses lem-weil-pbc-faithfully-flat-ideal-contraction, whose statement explicitly contracts every extended ideal. I opened pqf-def-coherent and lem-weil-pbc-finite-type-module-support-closed: the former supplies finite type and the latter explicitly identifies affine finite-type sheaf stalks with module localizations. Clearing each generator's denominator and multiplying finitely many multipliers gives the displayed common principal neighbourhood. This remains an elementary step, and is not turned into an unnecessary fifth new node. Every node cited by every assembly step has a verbatim statement quote in citations.json; no step uses a cited proof in place of a statement.

Small cases: n=0 has zero differential module and empty derivation family. r=0 gives the whole chart, determinant 1, empty graph and identity shift. m=0 gives phi=0. t=0 and delta=0 give the constant family and factorial 1. Empty generators give multiplier product 1. At the origin with h=y-w^2 and c=y^2, phi=W^2 and the Z and Z^2 coefficients are 2W^2 and 1. At the generic point of A^1, t maps to t+W over k(t), not to a constant or a zero-variable completion: its source is a field and the resulting nonzero power-series algebra is faithfully flat. In characteristic p, the p-th derivative factorial formula cannot be used; the formal-shift node and parent retain characteristic zero. Zero h with a positive transverse rank does not satisfy the invertible Jacobian hypothesis. Nonreduced test rings are allowed in the square-zero lifting comparison, rather than silently replaced by pointwise equality.

I searched the entire DAG by titles, statement phrases, tags and candidate declarations, and used blueprint_refs.py for Taylor, implicit, derivations, faithfully flat, formal graph, coordinate differential and coefficient factorial. I read the nearest candidates: lem-trf-etale-chart-rational-point-taylor-iso, lem-trf-taylor-normal-cone-splitting, lem-trf-formal-jacobian-coordinate-chain-rule, lem-trf-formal-coefficient-transform-criterion, lem-wf-formal-substitution-hom and lem-wf-formal-substitution-chain-rule. None states one of the new lemmas: the last two are univariate and the normal-cone lemma compares initial ideals, not this graph calculus. All searches of Mathlib were run using msearch.py; the exact queries, actual service results and verdicts are in the node records and searches.jsonl. Second phrasings were run for every new node. No unavailable service is represented as a no-match result. I read the hits for KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale (Etale/Kaehler.lean:38), standard-smooth existence of some etale coordinates (RingHom/StandardSmooth.lean:200), Module.FaithfullyFlat.of_flat_of_isLocalHom (Flat/FaithfullyFlat/Algebra.lean:60), MvPowerSeries.substAlgHom (Substitution.lean:210), coeff_subst (310), substitution composition (477), and coeff_pderiv (Derivative.lean:133). These are useful inputs already represented in the DAG, not one-line proofs of the new statements.

The four new node files contain statements only, no proof fields with steps, no proof_deps and no embedded proof sketches. Their blueprint.from.node is the checked ancestor lem-trf-local-term-locality and their via starts with this item. Parent stmt_deps and full Q27 lean record were compared against live and preserved. No new proof step exceeds 2000 characters; some new statements exceed that threshold, but the long-step rule concerns proof steps. The old long steps are retained below rather than hidden or discarded. No SGA source was used and no launcher, repository, gate or compiler was edited or invoked outside the prescribed delivery/check scripts.

### Repair of the promotion return (2026-10-22)

I read the return for head `4ef86d1102b` in `coord/returns/Q62.md`: the independent reader approved the delivery, but landing refused the side-project completion because it had not been promoted into the live queue DAG. I retained the delivered sandbox's four statement-only nodes, complete arguments, search log, citations and report. The prescribed initial dry run rebuilt that packet on current `origin/sheaf-dag` and exited successfully at `24f63f02f51`; I did not run git in the read repository or attempt to promote the node myself. Promotion remains L's operation.

I compared the retained `previous-stage1-node.json` with the current read-clone parent: they are equal as complete JSON objects, including the fifteen-step predecessor, its statement and statement dependencies, source, ancestry, review and Q27 Lean record. The sandbox's parent differs from this current parent only in its proof, proof dependencies and split report. None of the four helper ids exists in the current read clone. Thus the retained re-split is still a substantive four-task replacement of the live long proof under the released stage-1 order, rather than an attempt to claim the side completion as a finished live proof.

I reopened every statement cited in the five assembly steps and checked every retained quote against those current statements. All 16 step/node pairs still have verbatim quotes; none of the parts cited has changed. I read the statements in full, including their hypotheses: step 1's differential criterion assumes a smooth finite-type scheme over a field and a basis of the fibre of the differential sheaf; the affine stalk node supplies the localization identification. The base-change node asserts etaleness, and the smooth affine equivalence and ring-map composition give the smooth composite. Steps 2--4 use the four retained helper statements for exactly their explicit conclusions: arbitrary-point Taylor maps, restriction by the formal graph, derivative comparison, and the formal matrix/shift/coefficient calculation. Step 5's contraction node contracts every ideal, and its support node requires quasi-coherence and finite type; our coherent ideals are on the smooth finite-type, hence locally Noetherian, scheme. The finite generator and common denominator argument is still written out. These statements still support the retained route, so no citation was replaced and no new search question arose.

There is one concrete repair to the assembly beyond the refreshed base. Step 3 previously wrote `phi_j = tau_b^N((y_j-y_j(b))|_N)`. At a nonclosed point, `y_j(b)` is an element of `L = kappa(b)`, not generally of the original local ring or its coefficient field `k`. I changed it to `phi_j = tau_b^N(y_j|_N) - y_j(b)`, subtracting the constant in `L[[W]]`. This is precisely the graph-comparison node's stated formula `phi_j = sigma(q(y_j)) - epsilon q(y_j)`. It changes no statement or hypothesis, and requires no new node or Mathlib search. The old fifteen-step proof remains verbatim below as retained research material; this correction governs the delivered assembly. For a direct nonclosed test, take `A=k[w,y]`, `h=y-w`, and the generic point of `N`: then `L=k(t)`, both coordinate values are `t`, `tau_b^N(y)=t+W`, and the corrected difference is `W`. The subtraction has a well-defined target without choosing a section of the residue field into the original local ring.

For the source recheck I read ILO VIII 2.3.11 and 2.3.13 on printed pages 93--94 (PDF pages 99--100): they provide the resolution context and cite the algorithm literature, not this Taylor calculus as a black box. I reread Algebra Tags 0H93, 00RX and 00RO for the coordinate-differential and derivation node, Tags 0H1D, 00HT, 00HR and 00MC for the diagonal completion node, and the graph node's explicit formally-etale lifting hypotheses. The formal shift node's conclusion is the coefficient-family argument retained in original steps 6 and 8--10, with characteristic zero exactly where factorials are inverted. I reread the saved `msearch.py` log and search outputs, including their second phrasings, and retained those actual searches unchanged. No helper statement changed, so repeating them would answer the same questions. The child statements remain self-contained, unsplit, and without proof steps or proof dependencies (B); every assembly use has its statement quote (C); the four different arguments and short assembly remain (D); arbitrary points, characteristic zero, empty variable sets and finite generator descent were checked (E). No non-elementary assembly step reaches 2000 characters.

The return's instructions are therefore addressed by a fresh tool-built base, a rereading of the current citations, a corrected graph formula, and this signed repair review. The final dry run and push below are required again after these edits. The earlier validation entries describe the historical attempt, not the final head of this repair.

### Current-DAG repair of returned head 86677e51646 (2026-10-23)

The present return names head 86677e51646, not the earlier 4ef86d1102b discussed in the historical review above. I continued the retained sandbox rather than reconstructing it. The first required dry run in this retry completed with exit 1, before pushing: it found three new same-tag pairs against the refreshed DAG. No delivery invocation remains active. I opened all three current node files in full. The adjacent-quotient differential interleaving and complete-derivation reconstruction nodes concern inverse limits of differential modules, not coordinate derivations on an etale chart. The formal-conormal quotient-data node concerns completeness and differential maps on a power-series quotient, not graph shifts or coefficient extraction. The new pair-specific comparisons below address those diagnostics without deleting necessary helpers or replacing them with insufficient statements.

I compared the current read-clone parent as a complete JSON object with previous-stage1-node.json: they still agree. The retained split initially differed only in proof, proof_deps and split_report, so the statement, statement dependencies, source, ancestry and full Q27 owning Lean record remain preserved. I reread all fifteen distinct statements used by the assembly and validated all sixteen step/node quotes against the current files. No cited statement required replacement: step 1 still has the smooth finite-type differential-fibre criterion and etale base change; step 2 constructs both Taylor maps at arbitrary residue-field diagonal points; step 3 still uses two etale charts and subtracts the residue value in the target; step 4 uses the coordinate-derivative identity and the formal-shift coefficient formula; step 5 uses contraction and finite generators/localized stalks. I adjusted assembly step 4 to make its Jacobian hypothesis explicit: by the preceding derivative identity and the constant-term evaluation of the Taylor map, the constant matrix is exactly D_y h(b), invertible on the open already chosen. All assembly steps remain below 2000 characters and their total remains below 3000.

I reread the saved searches.jsonl results, including both phrasings and the actual Mathlib candidates, and the supporting Stacks statements 0H93, 00RX, 00RO, 0H1D, 00HT, 00HR, 00MC and 04FF. The helper statements and their search questions are unchanged, so the logged searches are reused without inventing or repeating queries. I reread ILO VIII 2.3.11 and 2.3.13 on printed pages 93--94; they remain contextual sources, with the unavailable Bierstone--Milman input marked WANTED rather than silently invoked. The upstream project search still yields no exact attachment; the existing Sheaf theorem still ends with sorry.

The B--E check is unchanged in substance: four self-contained, statement-only independent arguments, each with recorded searches and blueprint ancestry; every assembly citation uses its statement with the verified hypotheses; no route replacement or new SGA source; and elementary finite-generator descent stays written out. I rechecked r=0, m=0, empty coefficient variables and the generic point example h=y-w over k(t), where the corrected graph is W. For h=y-w^2 and c=y^2 at the origin the shifted coefficients remain 2W^2 and 1. Thus the repaired packet preserves the full retained argument and adds a current-DAG duplicate audit and an explicit hypothesis verification. The prescribed delivery tool will rebuild its commit on the current server base; promotion of side completion into the live queue remains L's responsibility.

## Not duplicates

lem-trf-etale-coordinate-derivations-jacobian vs lem-trf-adic-differential-quotient-interleaving: the existing statement constructs adjacent-quotient comparison maps for completed differentials with a finite separable coefficient field and an already given derivation; it does not construct normalized commuting coordinate derivations on an etale chart or compare them with every coordinate-valued Taylor map. Shared tag 00RO is the universal property only.

lem-trf-etale-coordinate-derivations-jacobian vs lem-trf-complete-derivation-truncation-reconstruction: the existing statement reconstructs an isomorphism from a complete module to an inverse limit of differentials, assuming a generating derivation and compatible maps; it does not give an etale coordinate basis, regular commuting derivations or the formal partial-derivative identity. The common tag 00RO supplies their different universal-property inputs.

lem-trf-formal-transverse-shift-calculus vs lem-trf-formal-conormal-quotient-data: the existing statement constructs a complete quotient of continuous differentials by relation differentials and compatible maps into truncated Kahler modules; it does not give an invertible formal graph shift, the factorial coefficient formula or a graph-factorization matrix. Tag 0306 concerns the common power-series setting, not either combined conclusion.


lem-trf-formal-transverse-shift-calculus vs def-weil-pbc-multivariate-power-series: the shared tag concerns power-series notation or Noetherian/completion properties; the new statement is a formal transverse shift with a factorial coefficient formula and an invertible graph-factorization matrix, not a Noetherianity or completion assertion. Shared source tag(s): 0306.

lem-trf-formal-transverse-shift-calculus vs lem-weil-pbc-power-series-noetherian: the shared tag concerns power-series notation or Noetherian/completion properties; the new statement is a formal transverse shift with a factorial coefficient formula and an invertible graph-factorization matrix, not a Noetherianity or completion assertion. Shared source tag(s): 0306.

lem-trf-etale-graph-taylor-comparison vs lem-per-lfp-unique-infinitesimal-lifts-etale: the existing result is a general infinitesimal lifting statement or a definition; the new statement compares two given etale charts through a specified quotient and identifies their Taylor restriction with its unique formal graph. Shared source tag(s): 02HG.

lem-trf-etale-graph-taylor-comparison vs lem-sfb-lfp-unique-infinitesimal-lifts-etale: the existing result is a general infinitesimal lifting statement or a definition; the new statement compares two given etale charts through a specified quotient and identifies their Taylor restriction with its unique formal graph. Shared source tag(s): 02HG.

lem-trf-etale-graph-taylor-comparison vs lem-weil-pbc-flat-open-diagonal-conormal-zero: the existing result is a general infinitesimal lifting statement or a definition; the new statement compares two given etale charts through a specified quotient and identifies their Taylor restriction with its unique formal graph. Shared source tag(s): 04FF.

lem-trf-etale-graph-taylor-comparison vs lem-weil-pbc-flat-unramified-formally-etale: the existing result is a general infinitesimal lifting statement or a definition; the new statement compares two given etale charts through a specified quotient and identifies their Taylor restriction with its unique formal graph. Shared source tag(s): 04FF, 02HG.

lem-trf-etale-graph-taylor-comparison vs lem-weil-pbc-open-iso-conormal-zero: the existing result is a general infinitesimal lifting statement or a definition; the new statement compares two given etale charts through a specified quotient and identifies their Taylor restriction with its unique formal graph. Shared source tag(s): 04FF.

lem-trf-etale-coordinate-derivations-jacobian vs def-trf-completed-differential-extension: the existing result supplies a differential module, its universal property or a smooth presentation; the new statement adds the normalized regular commuting coordinate derivations and their comparison with every coordinate-valued Taylor homomorphism. Shared source tag(s): 00RO.

lem-trf-etale-coordinate-derivations-jacobian vs def-trf-continuous-kahler-differentials: the existing result supplies a differential module, its universal property or a smooth presentation; the new statement adds the normalized regular commuting coordinate derivations and their comparison with every coordinate-valued Taylor homomorphism. Shared source tag(s): 00RO.

lem-trf-etale-coordinate-derivations-jacobian vs def-weil-pbc-kahler-differentials: the existing result supplies a differential module, its universal property or a smooth presentation; the new statement adds the normalized regular commuting coordinate derivations and their comparison with every coordinate-valued Taylor homomorphism. Shared source tag(s): 00RO.

lem-trf-etale-coordinate-derivations-jacobian vs def-weil-pbc-polynomial-partial-derivative: the existing result supplies a differential module, its universal property or a smooth presentation; the new statement adds the normalized regular commuting coordinate derivations and their comparison with every coordinate-valued Taylor homomorphism. Shared source tag(s): 00RX.

lem-trf-etale-coordinate-derivations-jacobian vs lem-trf-completion-kahler-differential-comparison: the existing result supplies a differential module, its universal property or a smooth presentation; the new statement adds the normalized regular commuting coordinate derivations and their comparison with every coordinate-valued Taylor homomorphism. Shared source tag(s): 00RX.

lem-trf-etale-coordinate-derivations-jacobian vs lem-trf-formal-power-series-continuous-differentials: the existing result supplies a differential module, its universal property or a smooth presentation; the new statement adds the normalized regular commuting coordinate derivations and their comparison with every coordinate-valued Taylor homomorphism. Shared source tag(s): 00RX.

lem-trf-etale-coordinate-derivations-jacobian vs lem-trf-formal-power-series-continuous-free: the existing result supplies a differential module, its universal property or a smooth presentation; the new statement adds the normalized regular commuting coordinate derivations and their comparison with every coordinate-valued Taylor homomorphism. Shared source tag(s): 00RX.

lem-trf-etale-coordinate-derivations-jacobian vs lem-trf-formally-etale-differentials-base-change: the existing result supplies a differential module, its universal property or a smooth presentation; the new statement adds the normalized regular commuting coordinate derivations and their comparison with every coordinate-valued Taylor homomorphism. Shared source tag(s): 0H93.

lem-trf-etale-coordinate-derivations-jacobian vs lem-weil-pbc-kahler-differentials-polynomial-extension: the existing result supplies a differential module, its universal property or a smooth presentation; the new statement adds the normalized regular commuting coordinate derivations and their comparison with every coordinate-valued Taylor homomorphism. Shared source tag(s): 00RX.

lem-trf-etale-coordinate-derivations-jacobian vs lem-weil-pbc-naive-cotangent-complex-cokernel-kahler: the existing result supplies a differential module, its universal property or a smooth presentation; the new statement adds the normalized regular commuting coordinate derivations and their comparison with every coordinate-valued Taylor homomorphism. Shared source tag(s): 00RX.

lem-trf-etale-coordinate-derivations-jacobian vs lem-weil-pbc-polynomial-ring-kahler-basis: the existing result supplies a differential module, its universal property or a smooth presentation; the new statement adds the normalized regular commuting coordinate derivations and their comparison with every coordinate-valued Taylor homomorphism. Shared source tag(s): 00RX.

lem-trf-etale-coordinate-derivations-jacobian vs lem-weil-pbc-polynomial-ring-kahler-basis-any-variables: the existing result supplies a differential module, its universal property or a smooth presentation; the new statement adds the normalized regular commuting coordinate derivations and their comparison with every coordinate-valued Taylor homomorphism. Shared source tag(s): 00RX.

lem-trf-etale-coordinate-derivations-jacobian vs lem-weil-pbc-reduced-tensor-differentials: the existing result supplies a differential module, its universal property or a smooth presentation; the new statement adds the normalized regular commuting coordinate derivations and their comparison with every coordinate-valued Taylor homomorphism. Shared source tag(s): 00RO.

lem-trf-etale-coordinate-derivations-jacobian vs lem-weil-pbc-simple-transcendental-differential-decomposition: the existing result supplies a differential module, its universal property or a smooth presentation; the new statement adds the normalized regular commuting coordinate derivations and their comparison with every coordinate-valued Taylor homomorphism. Shared source tag(s): 00RX.

lem-trf-etale-coordinate-derivations-jacobian vs lem-weil-pbc-smooth-conormal-chart-differential-basis: the existing result supplies a differential module, its universal property or a smooth presentation; the new statement adds the normalized regular commuting coordinate derivations and their comparison with every coordinate-valued Taylor homomorphism. Shared source tag(s): 00RX.

lem-trf-etale-coordinate-derivations-jacobian vs lem-weil-pbc-symmetric-algebra-differentials: the existing result supplies a differential module, its universal property or a smooth presentation; the new statement adds the normalized regular commuting coordinate derivations and their comparison with every coordinate-valued Taylor homomorphism. Shared source tag(s): 00RO.

lem-trf-diagonal-taylor-faithful-flatness vs def-weil-pbc-finite-etale-category: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 02GO.

lem-trf-diagonal-taylor-faithful-flatness vs lem-pc-affine-associated-module-flat-over: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-pc-affine-chart-relative-flat-criterion: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-pc-affine-cover-module-tensor-flat-criterion: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-pc-affine-flat-module-local-criterion: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-pc-affine-flat-module-localization-preserves-flatness: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-pc-affine-flat-module-tensor-flat: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-pc-affine-projective-sections-sheafification: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-pc-affine-pullback-chart-tensor-flat-stalks: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-pc-affine-sections-flat-over-base: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-pc-flat-model-opcycles-flat-zero: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-pc-local-flat-faithful-flat-reflects-surjective: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HR.

lem-trf-diagonal-taylor-faithful-flatness vs lem-pc-pullback-stalk-tensor-flat: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-pc-relative-flat-module-stalk: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-pc-relative-flat-of-stalks: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-sbc-canonical-stalk-spectrum-flat: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-sbc-etale-regular-divisor-base-change: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 02GO.

lem-trf-diagonal-taylor-faithful-flatness vs lem-sc-affine-standard-cover-finite-free-local-fp-flat: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-sc-p1-localization-short-exact: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-sc-p1-polynomial-noetherian: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00FN.

lem-trf-diagonal-taylor-faithful-flatness vs lem-sc-principal-cokernel-projective-descent: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-sfb-augmented-etale-associated-graded: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 0H1D.

lem-trf-diagonal-taylor-faithful-flatness vs lem-sfb-formally-etale-power-step: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 0H1D.

lem-trf-diagonal-taylor-faithful-flatness vs lem-sfb-henselian-parameter-root-regularity: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00FN.

lem-trf-diagonal-taylor-faithful-flatness vs lem-sfb-nodal-graph-cone-chart: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 0H1D.

lem-trf-diagonal-taylor-faithful-flatness vs lem-sfb-power-quotient-graded-comparison: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 0H1D.

lem-trf-diagonal-taylor-faithful-flatness vs lem-trf-etale-regular-intersection-descent: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 02GO.

lem-trf-diagonal-taylor-faithful-flatness vs lem-trf-extended-hilbert-local-upper-bound: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00FN.

lem-trf-diagonal-taylor-faithful-flatness vs lem-trf-fg-commutative-monoid-finite-presentation: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00FN.

lem-trf-diagonal-taylor-faithful-flatness vs lem-trf-local-module-arrow-noetherian-descent: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00FN.

lem-trf-diagonal-taylor-faithful-flatness vs lem-trf-local-tower-collapse-noetherian: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00FN.

lem-trf-diagonal-taylor-faithful-flatness vs lem-trf-nodal-points-reduced-algebraically-closed: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00MC.

lem-trf-diagonal-taylor-faithful-flatness vs lem-trf-valuation-separable-closure-extension: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HR.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-annihilator-localization-finite: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-colimit-eventually-flat: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00FN.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-completion-dimension: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00MC.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-etale-affine-chart-descent: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 02GO.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-etale-base-change-finite-limits: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 02GO.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-etale-covering-base-change: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 02GO.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-etale-fibre-discrete-separable-points: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 02GO.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-etale-scheme-base-change: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 02GO.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-fibre-ring-noetherian: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00FN.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-finite-algebra-noetherian: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00FN.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-finite-projective-descends-flat-local: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HR.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-finite-type-algebra-noetherian: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00FN.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-flat-local-hom-faithfully-flat: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HR.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-flat-local-ring-maps: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT, 00FN.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-flat-localized-module-base-change: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-flat-map-local-criterion: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-flat-over-localization: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-geometrically-regular-smooth-ascent: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00FN.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-graded-finiteness-cohomology: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00FN.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-local-completion-faithfully-flat: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00MC.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-localization-flat: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-localization-noetherian: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00FN.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-localization-of-regular-ring: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00FN.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-localization-regular: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-rees-algebra-noetherian: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00FN.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-regular-local-maximal: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-regular-through-localization: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-surjective-image-noetherian: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00FN.

lem-trf-diagonal-taylor-faithful-flatness vs lem-weil-pbc-weakly-regular-sequence-localization-prime: the existing result supplies a completion, flatness, localization or infinitesimal quotient input; the new statement assembles the natural Taylor map from the original arbitrary-point local ring through its residue-field diagonal and proves its faithful flatness and field naturality. Shared source tag(s): 00HT.

lem-trf-diagonal-taylor-faithful-flatness vs lem-trf-etale-chart-rational-point-taylor-iso: the existing statement identifies a rational-point completion; the new statement gives the canonical truncated maps, naturality, and faithful flatness from the original local ring at an arbitrary point before the residue-field extension.

lem-trf-formal-transverse-shift-calculus vs lem-trf-formal-jacobian-coordinate-chain-rule: the existing statement differentiates an already specified invertible coordinate system; the new statement constructs a particular shift, computes all its transverse coefficients, and factors a vector of equations through its graph ideal.

lem-trf-formal-transverse-shift-calculus vs lem-wf-formal-substitution-hom: the existing statement is univariate algebra-homomorphism substitution only; the new multivariate statement also needs the coefficient family, factorial extraction, and invertible matrix factorization.

## Retained complete arguments and destinations

Every original proof step is reproduced verbatim below, including its source and cited nodes. This is proof material for the new statement-only tasks, not their delivered proofs. Assembly step 1 retains original step 2, and assembly step 5 retains original steps 14--15. Original step 11 is distributed among the three stated naturality assertions, with its complete text retained once here.

### Original step 1 → lem-trf-etale-coordinate-derivations-jacobian

Work on an affine open of the given chart. Put $x=(w,y)$ and $A=\mathcal O_B(B)$ there. The chart is smooth by [lem-weil-pbc-etale-smooth-zero-dimensional-fibres], hence its ring map is smooth by [lem-weil-pbc-smooth-ring-map-iff-smooth-affine]. Thus its naive cotangent H_1 is zero by [def-weil-pbc-smooth-ring-map]. It is unramified by the etale hypothesis, so its relative differential module is zero by [lem-weil-pbc-unramified-ring-map-iff-unramified-affine]. Apply [lem-trf-formally-etale-differentials-base-change] to $k\to k[x]\to A$ and [lem-weil-pbc-polynomial-ring-kahler-basis] to $k[x]$: the differentials $\mathrm dx_i$ form an $A$-basis of $\Omega_{A/k}$. The universal property [def-weil-pbc-kahler-differentials] therefore defines a unique regular $k$-derivation $D_i:A\to A$ with $D_i(x_j)=\delta_{ij}$. This also works on every smaller affine chart; the maps agree on overlaps by uniqueness. Their commutator $D_iD_j-D_jD_i$ is a derivation, by expanding both Leibniz rules, and vanishes on every $x_l$; the same basis shows it is zero. Thus iterated coordinate derivatives are well-defined regular functions.

Cited nodes: lem-trf-formally-etale-differentials-base-change, lem-weil-pbc-polynomial-ring-kahler-basis, def-weil-pbc-kahler-differentials, lem-weil-pbc-etale-smooth-zero-dimensional-fibres, lem-weil-pbc-smooth-ring-map-iff-smooth-affine, def-weil-pbc-smooth-ring-map, lem-weil-pbc-unramified-ring-map-iff-unramified-affine.

Source: literature/stacks-project/algebra.tex, Tags 0H93 (lemma-formally-etale-omega), 00RX (lemma-differentials-polynomial-ring); coordinate-dual derivations and their commutators are the written-out universal-property calculation.

### Original step 2 → parent assembly step 1

Work on an affine chart $U=\operatorname{Spec}A$ as in step 1, where $(\mathrm dw,\mathrm dy)$ is an $A$-basis of $\Omega_{A/k}$ and $\mathrm dh_i=\sum_l(D_{w_l}h_i)\mathrm dw_l+\sum_j(D_{y_j}h_i)\mathrm dy_j$ by the universal property used there. Let $u\in U$, with prime $\mathfrak q$, lie in the open set $U^\circ$ where $\det(D_{y_j}h_i)$ does not vanish. The change from $(\mathrm dw,\mathrm dy)$ to $(\mathrm dw,\mathrm dh)$ has a block triangular matrix with diagonal blocks $1_m$ and $D_yh$; its determinant is a unit of $A_{\mathfrak q}$, so $(\mathrm dw,\mathrm dh)$ is an $A_{\mathfrak q}$-basis of $(\Omega_{A/k})_{\mathfrak q}$ and its classes form a $\kappa(u)$-basis of $\Omega_{A/k}\otimes_A\kappa(u)$. The affine description in [def-sc-relative-differential-sheaf] and the germ identification [lem-weil-pbc-spec-tilde-stalk-localization] identify this fibre with $\Omega_{U/k,u}\otimes_{\mathcal O_{U,u}}\kappa(u)$, sending $\mathrm dh_i$ to the class of $\mathrm dh_i$. As $U$ is smooth of finite type over $k$, [lem-pur-etale-at-point-from-differentials], with $d=m+r$ and the functions $(w,h)$, gives an open neighbourhood of $u$ on which $(w,h):U\to\mathbf A_k^{m+r}$ is etale. Local finite presentation, flatness and unramifiedness in [def-weil-etale-morphism] are local on the source, so $(w,h)$ is etale on the union of these neighbourhoods and hence on its open subset $U^\circ$; the same holds after gluing the charts. Its inverse image of $\mathbf A_k^m\times\{0\}$ is scheme-theoretically $N=V(h)$, so [lem-weil-pbc-etale-scheme-base-change] makes $w:N\to\mathbf A_k^m$ etale. In particular $N$ is smooth: affine space is smooth by [sbc-lem-affine-space-smooth], etale morphisms are smooth by [lem-weil-pbc-etale-smooth-zero-dimensional-fibres], and smooth ring maps compose by [lem-weil-pbc-smooth-ring-map-base-change-composition], using the affine comparison [lem-weil-pbc-smooth-ring-map-iff-smooth-affine]. This open set contains $a$ by the assumed invertibility there.

Cited nodes: def-sc-relative-differential-sheaf, lem-weil-pbc-spec-tilde-stalk-localization, lem-pur-etale-at-point-from-differentials, def-weil-etale-morphism, lem-weil-pbc-etale-scheme-base-change, sbc-lem-affine-space-smooth, lem-weil-pbc-etale-smooth-zero-dimensional-fibres, lem-weil-pbc-smooth-ring-map-base-change-composition, lem-weil-pbc-smooth-ring-map-iff-smooth-affine.

Source: literature/stacks-project/morphisms.tex, Tag 02GU (lemma-etale-at-point), via lem-pur-etale-at-point-from-differentials; Tag 02GO (lemma-base-change-etale); Algebra Tag 00TD (lemma-compose-smooth).

### Original step 3 → lem-trf-diagonal-taylor-faithful-flatness

Fix any $b\in N$, closed or not, and put $L=\kappa(b)$. The original coordinate chart remains etale after base change to $L$ by [lem-weil-pbc-etale-scheme-base-change]. For an affine chart algebra $A$, put $C=A\otimes_kL$, let $\varepsilon:C\to L$ be $c\otimes\lambda\mapsto c(b)\lambda$, and put $J=\ker\varepsilon$. Let $P=L[X_1,\ldots,X_{m+r}]$ map to $C$ by $X_i\mapsto x_i-x_i(b)$. Its reduction modulo $J$ is the constant-term map with kernel $I=(X)$. The etale map is formally etale, so [lem-sfb-augmented-etale-associated-graded] gives canonical compatible isomorphisms $P/I^n\simeq C/J^n$ for all $n\geq1$. Taking their inverse limit identifies $\widehat C_J$ with $L[[X]]$: a compatible family of truncated polynomials is exactly the family of coefficients of a series [def-weil-pbc-multivariate-power-series]. Every element of $C\setminus J$ is invertible modulo $J^n$ (invert its nonzero residue and sum the finite geometric series). Thus the same quotients and completion are obtained from $C_J=\mathcal O_{B_L,b_L}$. Composing with $A\to C_J\to\widehat{C_J}$ gives $\tau_b$; a germ denominator outside $b$ has nonzero constant term and is invertible, so the map extends to $\mathcal O_{B,b}$. The identical construction for the etale chart $w:N\to\mathbf A_k^m$ gives $\tau_b^N$.

Cited nodes: lem-weil-pbc-etale-scheme-base-change, lem-sfb-augmented-etale-associated-graded, def-weil-pbc-multivariate-power-series.

Source: literature/stacks-project/algebra.tex, Tag 0H1D (lemma-formally-etale-lift-infinitesimal), inverse limit of its canonical quotients; Morphisms Tag 02GO. The completion is at b_L, not at b.

### Original step 4 → lem-trf-etale-graph-taylor-comparison

Define $\phi_j(W)=\tau_b^N((y_j-y_j(b))|_N)$. These series have zero constant term. The two maps from the original chart algebra to $L[[W]]/(W)^n$ obtained by (i) restricting to $N$ and taking $\tau_b^N$, and (ii) taking $\tau_b$ and substituting $Y=\phi(W)$, agree on $k[w,y]$ and modulo $(W)$. Unique lifting for the original etale chart [lem-weil-pbc-flat-unramified-formally-etale], applied successively to the square-zero kernels $(W)^l/(W)^{l+1}$, proves their equality for every $n$. Hence $\tau_b(c)(W,\phi(W))=\tau_b^N(c|_N)$ for every regular germ $c$. Apply this identity to $c=h_i$, whose restriction to $N$ is zero, to get $h_b(W,\phi(W))=0$.

Cited nodes: lem-weil-pbc-flat-unramified-formally-etale.

Source: literature/stacks-project/more-morphisms.tex, Tag 04FF (lemma-unramified-flat-formally-etale), repeated unique lifts into the explicitly specified finite quotients; formal-series comparison supplied here.

### Original step 5 → lem-trf-etale-graph-taylor-comparison

If $\psi\in(W)L[[W]]^r$ is any other solution, $c\mapsto\tau_b(c)(W,\psi(W))$ is a map from the chart algebra annihilating every $h_i$, so factors through the quotient defining $N$. Its residue map is evaluation at $b$, and its values on $w_i$ are $w_i(b)+W_i$. Unique square-zero lifting [lem-weil-pbc-flat-unramified-formally-etale] for the etale chart $w:N\to\mathbf A_k^m$, in each quotient $L[[W]]/(W)^n$, therefore identifies it with $\tau_b^N$. Evaluating on $y_j-y_j(b)$ gives $\psi_j=\phi_j$ modulo every $(W)^n$, hence as series. This proves uniqueness without assuming that $b$ is closed.

Cited nodes: lem-weil-pbc-flat-unramified-formally-etale.

Source: literature/stacks-project/more-morphisms.tex, Tag 04FF (lemma-unramified-flat-formally-etale), applied to the etale chart on N constructed in step 2.

### Original step 6 → lem-trf-formal-transverse-shift-calculus

The substitution $S:L[[W,Y]]\to L[[W,Z]]$, $Y_j\mapsto\phi_j(W)+Z_j$, is defined degree by degree since every substituted series has zero constant term. Its inverse sends $Z_j$ to $Y_j-\phi_j(W)$ and fixes $W$; composing on each finite-degree quotient is the identity, hence so is the composition on series. It is continuous because both substitutions take the variable ideal into the variable ideal. These assertions use exactly the coefficient-family definition [def-weil-pbc-multivariate-power-series], and cover $m=0$ or $r=0$.

Cited nodes: def-weil-pbc-multivariate-power-series.

Source: literature/stacks-project/algebra.tex, Agent coefficientwise substitution calculation; compare the power-series substitutions in the proof of Tag 05D5 (lemma-section-smooth).

### Original step 7 → lem-trf-etale-coordinate-derivations-jacobian

For any coordinate $x_i$, both maps $c\mapsto\partial_{X_i}\tau_b(c)$ and $c\mapsto\tau_b(D_i c)$ are $k$-derivations from $A$ to the $A$-module $L[[X]]$ with action through $\tau_b$; the Leibniz rule for the former follows from [def-trf-formal-power-series-partial-derivative]. They agree on each $x_j$. The differential basis and universal property used in step 1 show they agree on all of $A$ (and on germs by the Leibniz rule for inverses). Thus $\partial_{X_i}\tau_b(c)=\tau_b(D_i c)$. Iterating proves the corresponding identity for $D_y^\delta$, since these coordinate derivations commute by step 1. This proves compatibility with Taylor expansion while retaining regularity of all differentiated coefficients.

Cited nodes: def-trf-formal-power-series-partial-derivative, def-weil-pbc-kahler-differentials.

Source: literature/stacks-project/more-morphisms.tex, Tag 04BX (lemma-sheaf-differentials-etale-localization); written universal-property comparison of the two derivations, using the basis established in step 1.

### Original step 8 → lem-trf-formal-transverse-shift-calculus

Put $H_i(W,Z)=h_{b,i}(W,\phi(W)+Z)$. Step 4 says $H_i(W,0)=0$. Expand $H_i$ as monomials and assign each nonzero monomial to the least $j$ whose $Z_j$ exponent is positive, then divide that monomial by $Z_j$. This defines series $V_{ij}$ with $H_i=\sum_jV_{ij}Z_j$. Its constant matrix is $V(0,0)=(D_{y_j}h_i)(b)$, invertible over $L$. Write $V=A_0+R$ with $A_0=V(0,0)$ and all entries of $R$ of positive order. The convergent formal matrix series $\sum_{n\geq0}(-A_0^{-1}R)^nA_0^{-1}$ is an inverse to $V$, as multiplication telescopes on every truncation. Set $U(W,Y)=V(W,Y-\phi(W))$ using step 6. Then $h_b=U(Y-\phi)$ and $U$ is invertible. It follows in both directions, by multiplying by $U$ and $U^{-1}$, that the extended ideal $(h_b)$ equals $(Y-\phi)$; step 6 sends it to $(Z)$. No assertion about an ideal follows merely from equality of its zero set.

Cited nodes: def-weil-pbc-multivariate-power-series.

Source: literature/stacks-project/algebra.tex, Agent monomial division and geometric-matrix-series calculation from the power-series ring definition; no inverse-function theorem is invoked.

### Original step 9 → lem-trf-formal-transverse-shift-calculus

Write $\tau_b(c)=\sum_{\alpha,\beta}a_{\alpha\beta}W^\alpha Y^\beta$. Expanding each $(\phi+Z)^\beta$ gives the coefficient of $Z^\delta$ as $\sum_{\alpha,\beta\geq\delta}\binom{\beta}{\delta}a_{\alpha\beta}W^\alpha\phi^{\beta-\delta}$. This sum converges in $L[[W]]$: a summand has order at least $|\alpha|+|\beta|-|\delta|$, so only finitely many indices can contribute below any fixed degree. In characteristic zero, $\binom{\beta}{\delta}=\beta!/(\delta!(\beta-\delta)!)$, which, by the coefficient formula [def-trf-formal-power-series-partial-derivative], identifies the displayed sum with $(\partial_Y^\delta\tau_b(c))(W,\phi)/\delta!$. Steps 7 and 4 identify this with $\tau_b^N((D_y^\delta c)|_N)/\delta!$. The only division is by the nonzero scalar $\delta!$ in the characteristic-zero field $L$.

Cited nodes: def-trf-formal-power-series-partial-derivative, def-weil-pbc-multivariate-power-series.

Source: literature/stacks-project/algebra.tex, Agent multivariate binomial coefficient calculation in the coefficient-family definition. Bierstone--Milman Lemma 3.5 and Remark 3.7 are motivational sources, not used as unverified inputs.

### Original step 10 → lem-trf-formal-transverse-shift-calculus

For $F=\sum_\gamma c_\gamma T^\gamma$, apply step 9 to each $c_\gamma$. The substitution fixes every $T_i$, so it never mixes different $\gamma$. Consequently $[Z^\delta T^\gamma]F_b(W,\phi(W)+Z,T)=\tau_b^N((D_y^\delta c_\gamma)|_N)/\delta!$. Finite many variables ensure there are finitely many monomials of any bounded total degree in $(W,Y,T)$, so the coefficientwise substitution defines the full formal series even if the family of nonzero coefficients is infinite. No common bound on their degrees is assumed.

Cited nodes: def-weil-pbc-multivariate-power-series.

Source: literature/stacks-project/algebra.tex, Agent coefficientwise extension of step 9, using the formal power-series definition.

### Original step 11 → Taylor naturality in diagonal node; solution naturality in graph node; formal algebra naturality in shift node

Let $L\hookrightarrow K$ be a field extension, and take the induced $K$-rational point of $B_K$ and $N_K$. Etaleness survives this base change by [lem-weil-pbc-etale-scheme-base-change]. The quotient isomorphisms of step 3 commute with these maps by the naturality clause of [lem-sfb-augmented-etale-associated-graded]; equivalently, their inverse lifts into $K[[X]]/(X)^n$ are unique. Thus $\tau_b$ and $\tau_b^N$ become their $K$-valued Taylor maps by applying $L\hookrightarrow K$ coefficientwise. Step 5 identifies the image of $\phi$ with the unique solution over $K$. The monomial allocation in step 8, the matrix inverse geometric series, and the binomial sums in steps 9--10 all commute with a coefficient homomorphism, as each fixed truncation involves finitely many sums and products. The inverse of $\delta!$ is preserved as well. This is the asserted residue-field compatibility.

Cited nodes: lem-weil-pbc-etale-scheme-base-change, lem-sfb-augmented-etale-associated-graded.

Source: literature/stacks-project/algebra.tex, Tag 0H1D (lemma-formally-etale-lift-infinitesimal), canonical quotient maps and their naturality; Morphisms Tag 02GO.

### Original step 12 → lem-trf-diagonal-taylor-faithful-flatness

For faithful flatness keep the notation $C=A\otimes_kL$ and $J=\ker(C\to L)$ of step 3, and let $\mathfrak p\subset A$ be the prime of $b$. We have $J\cap A=\mathfrak p$ since evaluation factors through the embedding of $A/\mathfrak p$ in $L$. The ring map $A\to C$ is faithfully flat by [lem-weil-pbc-field-extension-base-change-faithfully-flat]. Both $A$ and $C$ are Noetherian, by [lem-weil-pbc-finite-type-algebra-noetherian] over $k$ and $L$ respectively; field coefficient rings are Noetherian since they have only the ideals $0$ and $1$. Hence [lem-weil-pbc-flat-local-ring-maps] gives a flat local homomorphism $A_{\mathfrak p}\to C_J$ of Noetherian local rings. It is faithfully flat by [lem-weil-pbc-flat-local-hom-faithfully-flat]. This proof uses no finiteness or algebraicity of $L/k$ and so includes nonclosed points.

Cited nodes: lem-weil-pbc-field-extension-base-change-faithfully-flat, lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-flat-local-ring-maps, lem-weil-pbc-flat-local-hom-faithfully-flat.

Source: literature/stacks-project/algebra.tex, Tags 00HI (lemma-flat-base-change), 00FN (lemma-Noetherian-permanence), 00HT (lemma-flat-localization), 00HR (lemma-local-flat-ff).

### Original step 13 → lem-trf-diagonal-taylor-faithful-flatness

The completion map $C_J\to\widehat{C_J}$ is faithfully flat by [lem-weil-pbc-local-completion-faithfully-flat]. Under the isomorphism $\widehat{C_J}\simeq L[[W,Y]]$ of step 3, the composite $A_{\mathfrak p}\to C_J\to\widehat{C_J}$ is precisely the Taylor map, because this was its construction on every truncated coordinate ring. Faithful flatness of the composite follows directly from [def-weil-pbc-faithfully-flat-ring-map]: tensoring a complex with the composite is tensoring successively with the two algebras, and each tensor operation preserves and reflects exactness. Hence the Taylor map is faithfully flat even when $\dim A_{\mathfrak p}<m+r$.

Cited nodes: lem-weil-pbc-local-completion-faithfully-flat, def-weil-pbc-faithfully-flat-ring-map.

Source: literature/stacks-project/algebra.tex, Tag 00MC (lemma-completion-faithfully-flat); composite exactness test is the definition of faithful flatness.

### Original step 14 → parent assembly step 5

If finitely generated ideals $I,J\subset\mathcal O_{B,b}$ have equal extensions to the Taylor ring, [lem-weil-pbc-faithfully-flat-ideal-contraction] contracts those extensions back to $I$ and $J$; they are therefore equal. This applies to every $b$ on the chart, not just closed points.

Cited nodes: lem-weil-pbc-faithfully-flat-ideal-contraction.

Source: literature/stacks-project/algebra.tex, Tag 05CK (lemma-faithfully-flat-universally-injective), ideal-contraction assertion.

### Original step 15 → parent assembly step 5

Finally let $\mathcal I,\mathcal J$ be coherent ideals with equal stalks at $b$. On an affine neighbourhood $\operatorname{Spec}A$ they correspond to finite ideals $I=(f_1,\ldots,f_s)$ and $J=(g_1,\ldots,g_t)$; [lem-weil-pbc-finite-type-module-support-closed] supplies the identifications of their stalks with $I_{\mathfrak p}$ and $J_{\mathfrak p}$. For each $i$, membership $f_i/1\in J_{\mathfrak p}$ means that some $u_i\notin\mathfrak p$ satisfies $u_if_i\in J$; similarly choose $v_j\notin\mathfrak p$ with $v_jg_j\in I$. Put $s_0=\prod_i u_i\prod_jv_j\notin\mathfrak p$ (an empty product is $1$). In $A_{s_0}$ each chosen multiplier is a unit, so each generator $f_i$ belongs to $J_{s_0}$ and each $g_j$ to $I_{s_0}$. Thus $I_{s_0}=J_{s_0}$ and $\mathcal I=\mathcal J$ on the neighbourhood $D(s_0)$ of $b$.

Cited nodes: lem-weil-pbc-finite-type-module-support-closed, pqf-def-coherent.

Source: literature/stacks-project/coherent.tex, Tag 01Y3 (lemma-local-isomorphism), local vanishing principle; here the ideal equality is proved explicitly with the finitely many localization multipliers, using Morphisms Tag 056J for the affine stalk identifications.

## Validation

The initial prescribed dry run failed on the unchanged stale attempt. The repaired delivery is subjected next to deliver.py --no-push and, only after its successful exit, deliver.py. Exact final results are appended below.

The repaired prescribed dry run exited 0: `OK (not pushed) deliver/Q62/lem-trf-implicit-taylor-coordinate-calculus at 06c4ff0eb69: preflight passed`. It added four statement-only nodes, zero Mathlib leaves, and validated the 2758-character assembly. The full live parent statement, stmt_deps and Q27 owning Lean record remain identical. The final push uses the same node files; this report records the dry-run outcome.

The first rebase diagnostic in this repair exited 0: `OK (not pushed) deliver/Q62/lem-trf-implicit-taylor-coordinate-calculus at 24f63f02f51: preflight passed`. The graph formula and repair review above were then updated, so a new final dry run is required.

Final repaired dry run exited 0: `OK (not pushed) deliver/Q62/lem-trf-implicit-taylor-coordinate-calculus at f4fd625a68c: preflight passed`. This validates the corrected nonclosed-point graph formula, the fresh repair review, all citations and logged searches, and the 2756-character assembly with four new unsplit nodes and zero Mathlib leaves. The subsequent push uses these same node files; this paragraph only records the successful check.
