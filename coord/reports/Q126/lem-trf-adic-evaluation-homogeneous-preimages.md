## Files written

- `dag/nodes/sec-trace-formula/lem-trf-adic-evaluation-homogeneous-preimages.json`: item, statement unchanged, six-step split; no Mathlib match for the full constructive assertion.
- `citations.json`: verbatim statement excerpts for every proof-step citation.
- No new nodes, no Mathlib leaves, no unit files or Lean files.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the blueprint tag and homogeneous-preimage/evaluation terminology. Read `RingTheory/PowerSeriesOntoCompletion.lean` and `RingTheory/PowerSeriesAdicEvaluation.lean`. The former's `MvPowerSeries.exists_surjective_toAdicCompletion` has a sorry-free proof but concerns coefficients in R and a map into its completion, and does not state the requested homogeneous witnesses under the present coefficient map. The latter constructs evaluation but does not give preimages. Neither is an attachment for this item.

## WANTED

None.

## Problems found and changes

The item is true as written. The source expressly says “some details omitted” for surjectivity; this delivery supplies those details, without silently identifying E with polynomial substitution. Step 1 proves that identification from the stated reductions and separatedness. No hypothesis, conclusion, or definition was changed. Completeness is used only through its included separatedness, since existence of E is already a hypothesis; neither Noetherianity nor completeness for J is assumed.

The nearest current blueprint ancestor is `lem-trf-local-term-locality`, whose latest proof concerns contracting correspondences. This item is an auxiliary complete-local algebra argument already introduced beneath that branch, not a replacement of the unit's geometric route. I read the chapter and unit records and the latest ancestor proof. The statement and existing provenance were retained. Searches `blueprint_refs.py search 'homogeneous'`, `'power series'`, `'adic evaluation'`, and `'homogeneous polynomial'` found no blueprint node stating this item. DAG keyword searches found `lem-trf-finite-support-monomial-ideal-power`, which already states the needed finite ideal-power expansion, so no duplicate lemma was created. The scheme-valued formal-polynomial lift/quotient-span nodes have extra objects and conclusions and are unnecessary here.

## Unfinished work

None at stage 1. This delivery writes no Lean and runs no compiler, Lake, or build command.

## Review by Q126

I read Stacks `dpa.tex`, Tag 09PZ, label `lemma-ci-well-defined`, particularly the third proof paragraph adjoining variables mapping to kernel generators. The tag-to-label mapping was checked in `tags/tags`. The source omits the approximation details, so the proof is explicitly agent-origin, with its motivating source recorded. I read the current blueprint ancestor under `literature/blueprint/latest/`; no SGA source is used. There are no new nodes requiring independent source checks or duplicate-tag comparisons.

For step 1 I opened `def-weil-pbc-adically-complete-ring`: its statement explicitly includes intersection of all powers equal to zero. Applying the given reduction formula to a finite polynomial at arbitrarily high order really gives its exact substitution, because the order can exceed both its degree and any fixed M. This avoids assuming the constant or variable values of E beyond the hypothesis.

For step 2 I opened the full statement of `lem-trf-finite-support-monomial-ideal-power`, not just its title or proof. Its first clause gives finite linear combinations of length-N generator products, including exponent zero and the empty family. Its unrelated auxiliary monoid data can be instantiated with the trivial monoid and identity map, so all hypotheses hold for the current commutative ring R and generators b_j. Grouping those finitely many products by exponent gives coefficients r_nu, and the given surjection C to R/J lifts each of them. Each coefficient error is in J and each length-N product is in J^N, proving the next-order error without any further approximation lemma. This is strictly smaller existing input, not a node restating the item. I checked its dependency closure does not contain the item.

Step 3 gives the induction base J^0=R and explicitly writes the residual after adding the correction. Its only mathematical input is step 2 and additivity of E. Step 4 cites the coefficient-family definition of multivariate power series, which I read: arbitrary families are elements of the ring. The construction selects exactly one homogeneous coefficient for each multi-index. Finiteness below degree N follows by bounding each coordinate, and the truncation identity is checked coefficientwise; no infinite summation or convergence theorem is being assumed.

Step 5 again uses exactly the separatedness clause of the complete-ring definition. The assumed E reduction formula and the already proved truncation and polynomial identities give the tail in I^N. The residual from the induction lies in J^N, hence I^N because every b_j lies in I. Their difference vanishes by the cited intersection statement. In particular no unsupported claim that J is I-adically closed or that E is J-adically complete enters the proof. Step 6 checks s=0 directly: lift z by the now surjective coefficient map and take all positive-degree corrections zero. Degree N=0 was also checked in step 2, where the empty product is 1 rather than an empty generating family. J=0, I=0, nilpotent I and the zero ring cause no failure.

Against delivery-errors B–E: no unsplit new node, no unintroduced auxiliary object, no invented source tag, no new search record without a matching actual invocation, and no transported conclusion or hidden lemma. Every proof use is quoted verbatim in citations.json. The only non-elementary step is the finite ideal-power expansion with its explicit cited statement; the other steps are coefficient calculations, recursion, or direct applications of the given reduction formula and cited definitions. Every step is below 2000 characters. The full item is not declared Mathlib merely because abstract surjectivity or ideal-power representation exists: I read `Ideal.mem_span_pow_iff_exists_isHomogeneous` at `MvPolynomial/Homogeneous.lean:671` and `surjective_of_mk_map_comp_surjective` at `AdicCompletion/Functoriality.lean:447`, and neither supplies the full compatible homogeneous witness assertion in one specialization. Existing inherited searches were retained, and the fresh msearch results and a second semantic phrasing were read and recorded as run.
