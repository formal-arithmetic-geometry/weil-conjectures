## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-fd-l2-middle-extension.json: statement, split; no Mathlib match. Seven proof steps, using existing nodes only.
- citations.json: one verbatim statement quotation for each of the thirteen step/node citations.
- searches.jsonl: actual msearch.py results, retained without alteration.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. In the read-only slopmaster2 source, WeilConjectures/DeligneLaumon/AffineLine/TraceEnergy.lean:688, AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.l2Weight_directImage has a proof body but uses traceEnergy_directImage_eq_add (643) and exists_boundaryEnergy_le (651), both proved with sorry. Its boundary-energy definition and the nonnegative boundary-energy lemma do not prove the whole item. The current blueprint's LAdicWeilSheaf declaration is absent from this source. These declarations cannot justify ATTACH. Their existing audit records are retained.

## WANTED

None. This is an agent expansion of the supplied blueprint argument; it claims no independent literature proof and cites no SGA source.

## Statement corrected

STATEMENT-DISPUTED: the imported October 8 statement omitted nonzero. Take the zero lisse sheaf, of rank zero, with any finite real w. Punctual purity of weight w is vacuous, both trace energies vanish for every m, and the positive-limsup parameter sets are empty. Their suprema are minus infinity, not w. The October 15 main blueprint and blueprint_update explicitly correct this by requiring a nonzero lisse sheaf. I adopted exactly that updated statement. This is not an added assumption against the current source.

The slopmaster2 l2Weight_directImage theorem also has the nonzero hypothesis. It confirms this correction but is not evidence of a completed proof. No target statement or definition is changed.

## What changed and why

The imported paragraph on the boundary omitted the dimension bound, the rational Frobenius-power comparison, and the trace estimate without semisimplicity. The split now cites the boundary-stalk invariant formula, the closed-point counting theorem, the rational local-power theorem, triangularization and the definition of trace. It writes the triangular-matrix multiplication calculation explicitly instead of asserting a spectral-power rule. The last step explains why a zero nonnegative limsup gives convergence to zero and why the boundary geometric sequence decays. The statement dependencies now include the definition of punctual purity, actually used in the statement.

The blueprint unit sk-p-dl-a1-correction uses the boundary semicontinuity route. Nothing in its two proof steps is replaced. This node supplies the auxiliary energy comparison, not the unit's proposition, so no unit realization fields are edited. The item is its own blueprint ancestor; blueprint.from remains null and same_as is empty. The whole-blueprint search for middle extension found the separate definition, boundary invariants, Euler product and Fourier/perverse comparison nodes, but no other statement of the same L2 comparison. Whole-DAG concept searches likewise found the existing tools used below. No new node was needed, and therefore no duplicate-tag pairs arise.

The item searches tried two semantic phrasings, Loogle, LeanSearch, and Mathlib source grep. LeanFinder returned Selberg sieve and Lie-weight or asymptotic-sum results, not sheaves. LeanSearch returned temperate growth, a modular-form trace and ExpGrowth.expGrowthSup_def, none a middle-extension comparison. Loogle reported unknown identifier WeilSheaf, so that query is not claimed as evidence beyond the absence of that name there; the two semantic searches and grep provide the other checks. The exact project names l2Weight, boundaryEnergy and LisseOnDenseOpen had no Mathlib grep hits. A further exploratory trace-eigenvalue grep found ordinary linear-algebra identities; the already existing triangularization and trace-definition nodes suffice, so no trace node was created.

## Unfinished work

None in the one-level split. The existing unsplit dependency nodes remain their own work items. No Lean was written or compiled.

## Not duplicates

No new nodes; no pairs to distinguish.

## Review by Q108

I read the October 15 main statement and its separate lem-fd-l2-middle-extension.proof.md, compared them to blueprint_update and the older October 8 combined file, and read the chapter and sk-p-dl-a1-correction unit records. The updated statement keeps the same dense open, finite complement, rank, punctual purity and two energy sums, with the necessary nonzero correction explained above. I also read the slopmaster2 theorem and its two sorry inputs; I did not mistake a sorry-free wrapper for an attachment.

For Step 1 I opened lem-wf-l2-purity-rigidity and its source. Its statement supplies exactly the L2 equality for a nonzero lisse punctually pure sheaf on a smooth geometrically connected affine curve. The dense open of the affine line is affine by the explicit principal-open description and remains irreducible after base change; smoothness restricts to an open. Nonzero is now a hypothesis, so r is positive. No reality assumption is introduced.

For Step 2 I opened def-wf-l2-norm and the current split statement of def-wf-middle-extension. The first gives the actual rational-point sum, and the second gives sections over the fiber product with U. Restriction to an etale V over U makes that fiber product V, including the Weil action. The partition of a finite sum and nonnegativity of squares are elementary; no localization or derived pushforward theorem is being smuggled into this step. Ordinary j_* is essential here.

For Step 3 I opened lem-wf-boundary-stalk-invariants and its blueprint source, def-weil-punctual-weights, and lem-wf-boundary-semicontinuity with its source. The invariant-stalk statement identifies V_s with a subspace of the rank-r generic fiber; it is not merely a definition of inertia. Its dimension bound is immediate. The purity definition gives equality of absolute values; squaring gives the inequality the semicontinuity statement assumes. The latter's actual hypotheses are checked on the affine line: smoothness, separatedness, geometric connectedness, finite complement, lissity and r at least one. It supplies exactly the boundary eigenvalue inequality. I use its explicit spectral inequality, not an unproved equivalence between spectral bounds and a mixed-sheaf filtration.

For Step 4 I opened prop-euler-product and its source. Its first displayed identity is enough: applied to the finite reduced boundary it gives the uniform bound by the sum of degrees. The residue-field embedding at a rational point and the degree-tower equation show divisibility. The Euler-series consequence is not used. This is an existing Lean-closed tool, not a new counting lemma.

For Step 5 I opened lem-trf-rational-local-frobenius-powers, whose statement explicitly gives conjugacy F_(y,er) = T_i inverse F_s^r T_i at rational E coefficients, and read its source's local-powers paragraph. I also read def-weil-pbc-qbar-category and the full current def-weil-local-frobenius-trace statement. I did not use the finite-ring frobenius-degree-formula as if it already stated the rational result. The integral representative required by the rational statement is checked on Spec kappa(s), not asserted for an arbitrary global sheaf: its geometric components are points, and arbitrary bases give finite free lattices. Its reductions are finite free, so bounded constructible of finite Tor dimension. The statement allows a rational Weil map without an invariant integral lattice. Restriction computes precisely the same point pullbacks and Weil iterates; scalar extension preserves the matrix conjugacy. This avoids an unsupported global integral-model assertion.

For Step 6 I opened p-linear-triangular, its current blueprint statement and its Lean audit, and def-weil-endomorphism-trace. Triangularization is used only over the algebraically closed coefficient field, where its invariant full flag gives an adapted basis. The multiplication computation in the step proves the diagonal-power assertion without a further spectral-mapping lemma. Trace is the sum of those diagonal entries by the cited definition. The triangle inequality, the n_s at most r bound, squaring and summing then prove E_m at most D r squared q^(mw). A Jordan block is allowed; the proof never assumes a diagonal basis. The argument is written in the step, rather than moved to a new node restating the boundary-energy clause.

For Step 7 I reopened the supremum definition. Inclusion of positive-limsup parameter sets gives the lower bound. For beta greater than w, positivity for the open sequence would contradict its already established supremum. Nonnegativity forces limsup zero and hence convergence to zero. The upper inequality and the explicitly identified ratio rho in (0,1) give convergence to zero for the extended sequence. This is elementary order and sequence calculus, not an application of the definition as an unexplained theorem. Taking the supremum of a set contained in (-infinity,w] proves the upper bound in extended reals.

The generic off-unit inputs are declared with reasons in split_report.tool_uses; no maintainer-owned tool_uses field was written. Existing closed counting/triangularization nodes and Mathlib trace definitions are used directly. I checked B1–B10: no unsplit nodes are created, the item is self-contained under its definition citations, TeX is singly encoded in strings, all inherited import and blueprint-update fields remain, and no unrun search is recorded. I checked C1–C8 by opening every cited statement; citations.json contains literal quotations. I checked D1–D5: all seven steps carry the proof rather than referring to new versions of its clauses, and there is no new-node cycle or unstated induction. The sole induction on matrix powers has its base and multiplication step implicit in A^1 and explicitly stated for the diagonal.

For E1–E7 I tested S empty (D=C=0 and the sums agree), a boundary point of degree two with odd m (no point above it), zero inertia-invariant stalks (empty trace sum), a nonsemisimple rank-two Frobenius matrix (the diagonal-power trace computation still applies), negative real w (all bases of real powers remain positive and the boundary ratio still decays), and the zero sheaf (the counterexample repaired in the statement). All non-elementary steps are below 2000 characters. No step hides a further comparison lemma behind a long paragraph. There was no earlier sandbox split or delivery result to preserve, and no dispatcher/second reader is claimed to have reviewed this work: this is the direct-delivery self-review authorized by the brief.
