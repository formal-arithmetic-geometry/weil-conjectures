# Stage-1 report: lem-trf-rational-node-quadratic-completion

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-rational-node-quadratic-completion.json`: statement node, now split into six proof steps; not a Mathlib leaf. Statement, statement dependencies, historical blueprint ancestry, creation record, and inherited searches retained. Added six searches actually run through msearch.py.
- `citations.json`: eighteen entries, one for each cited node in each proof step, copied verbatim from the cited statement.
- `report.md`: this report. `prepare_split.py` is a sandbox-only JSON preparation script; `searches.jsonl` is the search command's actual log.

New DAG nodes: **0**. New Mathlib leaves: **0**. No Lean files, compiler invocations, unit edits, repository writes, direct git commands, or subagents.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and `Comparator/` for the blueprint tag, rational-node and quadratic-completion language, nodal/ordinary-double-point language, and source tags 0C49/0C4D. No declaration states the item. Upstream master sorry declarations have not been treated as completed proofs.

## WANTED

None. The sources needed here are already in `literature/stacks-project/`.

## Findings and changes

The item was correctly stated and unsplit in the shared repository; the sandbox contained only dispatcher markers. I copied the current item, kept its entire statement unchanged, and supplied the proof. In particular I did not replace the assumption of a **ring** isomorphism by an algebra isomorphism, and did not add equidimensionality, global finite type, perfection, or a characteristic restriction.

The route is the rational-residue-field instance of Stacks curves.tex Tag 0C4D (lemma-nodal), from the geometric ordinary double point to the depth-one first-Fitting condition, followed by 0C4C (lemma-fitting-ideal) and 0C49 (lemma-nodal-algebraic). It uses only the existing DAG. The general nodal local criterion assumes equidimensionality and has a different conclusion, so I did not apply it to this merely dimension-one scheme. The global dimension hypothesis is retained but the proof is local and works without using it.

The blueprint ancestry explicitly identifies this as the retained historical nodal branch below lem-trf-local-term-locality. I read the current sk-i-curve-zero unit: its actual argument is contracting correspondences, not this nodal reduction. I preserve that existing historical annotation and the unit/chapter records. No new claim is made that this lemma realizes a step of the current contracting-correspondence proof. Blueprint searches for `rational node quadratic completion`, `nodal`, and `quadratic` found no blueprint node stating it in another form; `same_as` remains empty.

Mathlib searches used leanfinder twice with distinct formulations, loogle, leansearch, and grep twice (the second grep restricted to RingTheory). All six completed successfully and their recorded responses are in searches.jsonl and the item's mathlib_searches. I read the returned completion equivalence in Mathlib/RingTheory/MvPowerSeries/Equiv.lean:344: it completes the polynomial ring itself, with no singularity or descent hypothesis. I read Mathlib/LinearAlgebra/QuadraticForm/AlgClosed.lean:51 and :62: classification of quadratic forms requires invertible 2 and does not produce the local-ring equation here. The second grep's Morse hits concern Galois groups of polynomials, as its module introduction states. Weierstrass preparation results returned by the semantic searches concern one-variable division, and the displayed types contain no descent from a geometric node. These are not one-line specializations yielding this item.

## Not duplicates

No new node was created. The following existing results supply the argument rather than being restated as new dependencies:

- lem-trf-separable-closed-point-formal-presentation supplies Noetherian local completions, structural coefficient sections, faithful flatness of the local field-extension map with field closed fibre, and completed differential Jacobian presentations.
- lem-trf-formal-jacobian-quadratic-criterion supplies both directions between the depth/minor condition and the quadratic presentation, including its ring-isomorphism clause (c).
- lem-trf-nodal-point-local-criterion has an equidimensionality hypothesis and a separability/LCI/Fitting-stalk conclusion; it neither directly states this item's conclusion nor has the same hypotheses. Its split uses the same commutative-algebra inputs, all reused here.
- lem-trf-formal-binary-morse is already below the formal Jacobian criterion. No duplicate Morse or nodal-normal-form lemma was introduced.

## Tool uses

The sole non-Mathlib off-unit proof tool is `lem-weil-pbc-flat-local-depth-formula` from sk-thm-p1. Its statement is used exactly for three Noetherian flat local maps with field closed fibres. I declared this use in `split_report.tool_uses`; I did not write the maintainer-owned top-level field. This is a generic commutative-algebra tool and does not replace a geometric step of the unit. The other off-unit statements are existing Mathlib leaves (affine finite type, differential base change/localization, completion faithful flatness, and ideal contraction); definitions are notions.

## Review by Q82

I read the complete statement and proof of curves.tex 0C4D, including its algebraically closed Jacobian computation and arbitrary-field descent paragraphs. I also read 0C4C and the full 0C49 proof, including the polar-matrix definition of nondegeneracy immediately before 0C49. No SGA source was used. There are no new nodes needing separate source or edge-case reviews.

For step 1 I opened the statements of lem-weil-pbc-lft-affine-pairs and lem-trf-separable-closed-point-formal-presentation. The first explicitly applies to every affine open and yields finite generation of S. The latter explicitly says A and its completion are Noetherian local, supplies the coefficient section and presentation, and for the specified rational base-change point supplies B, faithful flatness, mB equal to the maximal ideal, and residue field K. I checked that the residue field here really is F with its structural identification, so its extension over the ground field is the identity, hence finite separable. The kernel of the augmented map S tensor K to K is maximal because that map is surjective. I read the presentation sources varieties.tex 0C52 and 0C54 and the rational/separable local comparison 0C4Y/0C50. The structure-preserving section is unique as an F-algebra map F to the completion, so the final algebra structure is the required one.

For step 2 I read the definition of Kähler differentials and both differential comparison statements. Finite generation is explicitly accounted for by writing differentials of polynomials in the finite algebra generators using Leibniz; over K the generators are the same s_i tensor 1. Localization gives finite differential modules at A and B. The base-change lemma is a module isomorphism over the full scalar-extended algebra, and the localization lemma applies to arbitrary multiplicative subsets, not just principal opens. Together they give Omega(B/K) equal to Omega(A/F) tensor B. I read algebra.tex 00RT(2) and 00RV and more-algebra.tex 07Z8/07ZA(3). The Fitting node's statement gives both independence of the chosen presentation and base change for arbitrary ring maps; it therefore really gives J_B=J_AB, not merely a definition of Fitting ideals.

For step 3 I checked the formal-presentation statement again at the finite-type K-algebra and rational closed point: it supplies a presentation with N at least 2 and ideal contained in the variables, together with the completed differential cokernel. I opened the complete formal-Jacobian criterion statement and specifically used **(c) to (a)**, since the input is a ring isomorphism only. The choice (a,b,c)=(0,1,0) has discriminant 1, including in characteristic 2. The criterion supplies both depth one and the maximal-ideal equality. The Fitting statement identifies this same minor ideal with extension of J_B. I wrote out why its kernel-row definition agrees with the displayed finite relation matrix: determinant multilinearity expands minors of combinations into combinations of the original minors. This avoids taking an uncited change-of-presentation theorem from a node's proof.

For step 4 I read both faithful-flat statements. Completion faithful flatness requires a Noetherian local source, which step 1 supplies. The ideal-contraction node states the contraction equality for **every** ideal; applying it to the two ideals in each pair proves equality downstairs. The second map A to B has the same property from step 1, and its maximal ideal extension equals n. I checked that I do not infer equality of ideals from their sets of vanishing points.

For step 5 I opened the flat local depth formula and the depth definition. Its hypotheses require both rings Noetherian and the map flat and local; these hold for all three maps by the presentation and completion statements. Their closed fibres are K, K, F because the extended maximal ideals equal the target maximal ideals, not just because the residue fields are named. Each field has depth zero directly from the definition: the only maximal-ideal element is zero, which annihilates its nonzero module. Thus the three applications give depth(B)=depth(A)=depth(Ahat)=1 without an uncited preservation-of-depth assertion. I checked algebra.tex 0337 and 00MC for these exact statements.

For step 6 I checked the presentation/Jacobian-cokernel clauses, the Fitting base-change statement, and the **(a) to (b)** clause of the formal quadratic criterion. The presentation has all required hypotheses: n at least 2, relation ideal in the variables, depth one, and its Jacobian-minor ideal equal to the maximal ideal. The conclusion of (b) is a complete local F-algebra isomorphism with nonzero discriminant, exactly what the item needs. This uses the statements of the three nodes, not an object hidden in their proofs. It is the final 0C4C/0C49 step of the source route.

I checked delivery-errors B--E against the actual files. There are no new statement-only nodes, new notions, unsearched leaves, duplicate clauses or inline claims promoted to nodes. Every substantive comparison or normal-form assertion is the statement of a cited existing node; the only inline calculations are polynomial differentiation generation, determinant multilinearity, field depth zero, and structural F-linearity. The eighteen citations are literal substrings (or complete relevant statements) of the current cited nodes. All six proof steps are below 2000 characters, and none conceals an independently stated comparison. The report and node preserve all pre-existing metadata.

Small cases checked by hand: the split node uv over any field, the nonsplit real node u^2+v^2 (discriminant -4), and the characteristic-two node u^2+uv+v^2 over F_2 (discriminant 1, split geometrically over F_4). In characteristic 2 the polar matrix [[0,1],[1,0]] is invertible, so no division by 2 occurs. The cusp v^2-u^3 and a double line fail the geometric nodal hypothesis and do not pass the minor/depth criterion. The proof does not require a perfect field: rationality alone gives the separable identity residue extension. Nonseparated or non-quasi-compact X causes no problem because one finite-type affine neighbourhood suffices.

I corrected no mathematical statement. I avoided the stronger equidimensional nodal criterion and the unjustified promotion of the given ring isomorphism to a coefficient-preserving one. No branch in this proof depends on the current item: the reused formal algebra criteria were independently created for the broader nodal local criterion.

## Unfinished work

None at stage 1 for this item; the proof is completely split into existing nodes. The unsplit dependencies remain their own stage-1 items. Server dry-run and final delivery results are recorded below once the commands finish.
