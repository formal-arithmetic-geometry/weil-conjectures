# Worker report: lem-wf-l2-purity-rigidity (Q115)

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-wf-l2-purity-rigidity.json: seven-step split of the unchanged statement.
- dag/nodes/sec-deligne-laumon-a1/lem-wf-trace-energy-constant-twist.json: statement; unsplit, no Mathlib match. Exact constant-twist energy identity, for separated finite-type schemes and all positive levels.
- dag/nodes/sec-deligne-laumon-a1/lem-wf-trace-energy-real-envelope-bound.json: statement; unsplit, no Mathlib match. Comparison of envelope energy with normalized-sheaf energy, for separated finite-type schemes and all positive levels.
- citations.json: verbatim statement quotes for every node in every item's step uses list.
- searches.jsonl: actual search-command log; no inherited searches existed in the interrupted sandbox.

The sandbox initially contained only .brief2 through .brief5. There was no item, report, search log or active deliver.py process to resume. All writing was confined to this sandbox. No Lean or compiler was run, and no git command was run in the shared project.

## Attachments and Lean frontier

There is no closed attachment for the item. In /home/ubuntu/weil-src-slopmaster2/WeilConjectures/DeligneLaumon/AffineLine/TraceEnergy.lean:567-600, AlgebraicGeometry.WeilSheaf.l2Weight_eq_of_isPunctuallyPureOfWeight has a sorry-free proof body, but its four unfinished dependencies are explicitly listed in the item's existing lean_audit.slopmaster2.open. Reading their bodies confirms the sorries. In particular, the item is not established by inspecting its own body alone. No corresponding LAdicWeilSheaf theorem was found by the project-wide notion/name search.

Frontier correspondences, for maintainer metadata recording (not claims of completed proofs):

- AlgebraicGeometry.WeilSheaf.traceEnergy_constantTwist belongs to lem-wf-trace-energy-constant-twist, WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy:422-427; sorry at 427. The natural statement is its finite-type, positive-level specialization. The existing project's arbitrary-scheme finsum convention also treats infinite point sets, whereas this statement uses the genuine finite sums needed here.
- AlgebraicGeometry.WeilSheaf.traceEnergy_realEnvelope_le belongs to lem-wf-trace-energy-real-envelope-bound, same module:431-436; sorry at 436. Again the node restricts to separated finite-type schemes and positive levels, and needs no nonzero assumption.
- AlgebraicGeometry.WeilSheaf.exists_traceEnergy_le_of_hasWeightsAtMost belongs to existing lem-wf-l2-upper, same module:479-488; sorry at 488. Its derived l2Weight_le_of_hasWeightsAtMost is the precise clause used in step 6.
- AlgebraicGeometry.WeilSheaf.l2Weight_eq_of_isReal belongs to existing thm-wf-l2-dictionary, same module:540-557; sorry at 557.

The two new-node sandbox files retain the required sorry_here audit entries and also provide lean_candidates, so the maintainer can record the association if delivery's field ownership filter leaves audit installation to maintenance. Neither child claims a Lean-closed result.

## WANTED

None. The proof follows the available current blueprint and is marked agent-written, as that blueprint is agent-written. No SGA source is used.

## Corrections and source audit

No statement dispute or statement weakening was needed. The current main-20261015 statement agrees with the imported item. I read both current statement and separate proof at literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-l-dl-a1-energy/lem-wf-l2-purity-rigidity.{md,proof.md}, together with the chapter and energy-unit records and current chapter/unit source files. The item is not the key node sk-l-dl-a1-energy, so no unit realization fields were changed.

Two gaps in the imported proof were repaired. First, a calculation only for closed points of degree m does not immediately sum over X_0(F_{q^m}): points above closed points of degree d dividing m occur as well. At such a point the operator is a conjugate of F_x^(m/d), and twisting scales it by (b^d)^(m/d)=b^m. The two children expose the needed sheaf-level comparisons at every rational-point level rather than claim that a closed-point trace formula alone already proves an energy identity. Second, the imported proof took eigenvalue information from the proof of lem-wf-envelope-real, whose statement only supplies reality and lissity. Step 5 now takes exactly the stated energy inequality from its new child. Steps 2 and 5 write the parameter-set translation and inclusion arguments, including extended-real limsup/supremum conventions, rather than hide them behind the word comparison.

The normalized-envelope route is unchanged. The chapter's Fourier/energy organization and the energy unit's relation to the real-sheaf argument are retained. lem-tw-dual-negation is recorded in split_report.tool_uses as the generic weight-zero linear-dual tool; its proof route is not substituted for any energy-unit step.

## Not duplicates

Searches were made throughout dag/nodes, not just this unit, for traceEnergy_constantTwist, traceEnergy_realEnvelope_le, trace energy/energies, constant twist, and envelope/trace combinations. blueprint_refs.py searches for 'trace energy', 'trace energies', 'constant twist', 'envelope', 'purity rigidity', and 'L^2' were read, as was its ancestor result. The occurrences of the two project declarations in ancestor audit.open arrays are references to the same unassigned holes, not nodes stating their claims. No same-Stacks-tag pairs occur: these are blueprint trace-energy calculations, with no asserted Stacks tag.

- lem-wf-trace-energy-constant-twist vs lem-wf-constant-twist-weight: the existing lemma shifts punctual eigenvalue weights, while the child identifies finite sums of squared trace functions at every rational-point level. Knowing only magnitudes of individual eigenvalues does not determine a trace sum.
- lem-wf-trace-energy-constant-twist vs lem-wf-constant-twist-cohomology: the latter is a projection formula for pushforwards and cohomology, not an energy formula.
- lem-wf-trace-energy-real-envelope-bound vs lem-wf-envelope-real: reality and lissity of an envelope give neither a comparison with its summand's trace nor a bound on that trace energy.
- lem-wf-trace-energy-real-envelope-bound vs lem-wf-conjugate-tensor-traces: that existing statement treats a tensor product and its L-series, whereas this child treats a direct sum with a dual and a pointwise-to-global energy bound. No logarithmic derivative or L-series is used here.
- Both children vs lem-wf-l2-purity-rigidity and thm-wf-l2-dictionary: neither child asserts an equality of L2 growth weights or a rigidity theorem. They hold on arbitrary separated finite-type schemes and allow zero sheaves. The substantial real dictionary and upper bound remain independent citations in the item's proof.

The two children are the explicitly required missing Lean-frontier interfaces. They isolate the sheaf-operation/normalized rational-point Frobenius identifications needed before the elementary scalar and finite-sum calculations can be applied. The scalar identities themselves, the direct-sum purity calculation, positivity, finite translation of suprema and mixed filtration were kept as arguments in the item instead of additional nodes.

## Mathlib searches

Every recorded search was run through msearch.py and read. The two semantic phrasings per child were the LeanFinder and LeanSearch queries recorded verbatim in its JSON. Loogle and full-source grep returned no WeilSheaf, traceEnergy, constantTwist, realEnvelope or l2Weight statements. All services responded; no unavailable response was relabelled as absence.

For the twist child, LeanFinder found LinearMap.trace_tensorProduct' and FDRep.char_tensor. I read Mathlib/LinearAlgebra/Trace.lean:258-263 and Mathlib/RepresentationTheory/Character.lean:168-169: these give multiplicativity of linear traces/characters of supplied tensor operators, but do not identify stalk Frobenius of a Weil twist at all extension-field points or state the trace-energy identity. They therefore support the elementary linear algebra, not a one-line Mathlib specialization of the whole child. LeanSearch's L2/PiLp/Fourier lemmas concern analytic function spaces and do not supply the missing sheaf identification. For the envelope child, semantic hits were number-field bounds and direct-sum linear traces, none identifying the dual Weil stalk operator or the envelope's energy. The item searches likewise found unrelated algebraic/Lie weights, not punctual-weight rigidity for Weil sheaves.

## Review by Q115

I checked delivery-errors B through E against the actual JSON statements and the current source proof. Each new statement introduces its base field, coefficient field, embedding, scheme, sheaf, level, local operator and energy before using them. Its finite-type hypothesis ensures the rational-point sums are finite. Each child has only a statement: proof and proof_deps are empty. Its exact blueprint ancestor is the imported item, with the relevant source paragraph named, and same_as is empty after the searches described above. Neither child is a restated clause of the rigidity conclusion. Source provenance is the current blueprint proof, not a fabricated Stacks reference.

Step 1 uses the normalization construction, the weight-shift lemma and the rank-one Weil twist definition. I checked that the weight-shift hypothesis is 2 log_q |iota(b)| = c, so c=-w follows because q>1. The chosen scalar exists because the punctual-weight conventions specify a field isomorphism, rather than a merely nonsurjective embedding. Tensoring by the inverse rank-one character proves nonvanishing; local trivializations prove lissity. These arguments do not assume geometric semisimplicity.

Step 2 takes the energy identity, and only that identity, from the twist child. The def-wf-l2-norm statement explicitly supplies the positive-limsup parameter set and the empty-supremum convention. I checked the shift's sign by dividing q^(-mw) S_m(G) by q^(m(beta+1)), which yields the original ratio at beta+w. Translation of all upper bounds proves the supremum identity also at infinities; no subtraction of two infinite values occurs.

Step 3 uses the envelope's explicit direct-sum construction and lem-tw-dual-negation at weight zero. That lemma's conclusion is purity of the linear dual of a lisse sheaf, not a claim about a general complex. G^0 is lisse by step 1, so its hypotheses hold. The block-diagonal characteristic polynomial gives the direct-sum purity, and the punctual-weight definition makes that implication exact. Nonzero G^0 is a retract of the envelope; the envelope cannot be zero.

Step 4 takes reality AND lissity from the current statement of lem-wf-envelope-real, which explicitly includes both clauses. I checked thm-wf-l2-dictionary against the envelope: nonzero, lisse, real and punctually pure of weight 0, on the same smooth geometrically connected affine curve. Its conclusion is exactly ||E||=0. No assertion inside the reality lemma's proof is being used as a statement.

Step 5 takes S_m(E)<=4 S_m(G^0) from the envelope child. Both energies are nonnegative finite sums. The argument with epsilon/4 proves that zero limsup for the right-hand sequence forces zero limsup for the left-hand sequence, even though positive limsups may be infinite. This yields inclusion of the parameter sets in def-wf-l2-norm, hence the required lower bound on ||G^0||. I checked that the inequality direction is E <= G^0, so that it supplies a lower bound after ||E||=0.

Step 6 checks the only purity-to-mixed conversion needed: the length-one filtration 0 subset G^0 meets the definition exactly. lem-wf-l2-upper asserts the needed L2 upper bound, with G^0 lisse on the affine curve, so it applies at w=0. Step 7 is finite-translation cancellation in the extended reals and requires no new theorem node. These two bounds force a finite value before the final equality with w. All cited-node statements were opened and their actual used claims are copied verbatim in citations.json.

I tested the new statements at the zero sheaf (both sides zero), at empty point sets (zero sums), at b=1,w=0 (unchanged energy), and at a constant rank-one sheaf (scalar factor |iota(b)|^(2m)=q^(-mw)). For the envelope bound a unit-modulus eigenvalue exp(i theta) gives |2 Re exp(i m theta)|^2<=4, including theta=pi/2 where the envelope trace can vanish; the proof needs only an upper bound, never pointwise nonvanishing. Points over closed degree d|m give the same b^m factor, and powers of weight-zero eigenvalues still have modulus one. No semisimplicity or cancellation assumption is introduced. The original statement excludes the zero sheaf, as necessary: its L2 weight would be minus infinity. I also checked w<0 and the shift sign, as well as parameter sets that are empty or unbounded before the comparison.

All proof steps are below 2000 characters (the longest is under 800); no long step hides a separate subclaim. The new trace-energy interfaces are the only unsplit obligations introduced. There are no unfinished edits or wanted sources; required server dry run and delivery results are recorded below when available.
