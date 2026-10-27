# Stage-1 report: lem-sfb-weak-sobolev-fourier-moments

Group Q57; 2026-10-24. Direct delivery; the maintainer is the independent reader.

## Files written

All node files are under `dag/nodes/sec-six-functors-basics/` in this sandbox.

- `lem-sfb-weak-sobolev-fourier-moments.json`: item, statement unchanged, five-step agent-written proof; no exact Mathlib match.
- `lem-sfb-l2-weak-derivative-fourier-identity.json`: new statement-only analytic node, unsplit. A single weak multi-index derivative in L2 transforms to the corresponding Fourier monomial; no Mathlib match under these hypotheses.
- `lem-sfb-euclidean-bracket-integrable.json`: new Mathlib leaf, `integrable_rpow_neg_one_add_norm_sq`, `Mathlib/Analysis/SpecialFunctions/JapaneseBracket.lean:147–154`.
- `lem-sfb-l2-product-integrable.json`: new Mathlib leaf, `MeasureTheory.MemLp.integrable_mul`, `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1085–1088`.

`citations.json` copies the statements used by steps 1, 3 and 4 verbatim. `searches.jsonl` contains the actual launcher search records. These auxiliary files and this report are in the sandbox; no repository or launcher file was written, and no Lean/compiler/build tool was run.

## Attachments

None. Searches by the exact blueprint tag, weak Sobolev terminology, weak derivatives and Fourier moments found no project declaration. The project Plancherel declarations concern finite-field Fourier transforms, not Euclidean L2 functions. No sorry declaration was treated as a completed proof.

## WANTED

WANTED: Demailly, *Complex Analytic and Differential Geometry*, June 21, 2012, VI §2 (2.1), printed p.289, for this item and `lem-sfb-l2-weak-derivative-fourier-identity`. The original PDF is not in the permitted local literature tree. I read the online recomposed excerpt at https://totomityann.github.io/pdf/lua_agbook.pdf, PDF page 152 (index 151): it states the weak-derivative Sobolev inclusion but does not give this Euclidean Fourier proof. Therefore this delivery explicitly marks the proof as agent-written. No download or literature edit was made. Neither the Fourier-identity prerequisite nor the Mathlib leaves is attributed to a nonexistent Stacks tag.

## Problems found and changes

The item was unsplit and the sandbox had no prior item or report. Its statement is mathematically correct; no hypothesis or conclusion has changed. The imported searches already identified that Bessel-potential Sobolev membership is not the weak-derivative hypothesis by definition. I retained those records and added actual Q57 searches. In particular, the tempting `MemSobolev.fourier_memL1` hit cannot close the item in one line.

The ordinary smooth Fourier-derivative formulas also do not apply to an arbitrary L2 weak derivative. I exposed exactly this missing input as a strictly smaller node. The item itself now constructs the weighted L2 factor, checks the exponent inequality for each j, and applies product integrability. The proof is not an instruction to apply a newly named version of its own conclusion.

I initially transcribed the Lp Fourier/tempered comparison location incorrectly while drafting. Reading the numbered source corrected it to `MeasureTheory.Lp.fourier_toTemperedDistribution_eq`, `Mathlib/Analysis/Fourier/LpSpace.lean:120–129`. The tempered derivative identity is at `Mathlib/Analysis/Distribution/TemperedDistribution.lean:568–573`.

The inherited blueprint ancestry has `from.node = null`; `tools/blueprint_refs.py ancestor` confirms that value. I retained its via chain and precise place, and prepended this item to each child's via chain. I read the current latest blueprint (`main-20261024`) direct-images statement and proof (3), and the chapter text. This is a lower-level Fourier prerequisite along the already specified analytic chain, with no new route at unit or chapter level. This item is not the unit's key statement, so no unit record was changed.

## Searches and source readings

Before writing the children I searched the entire DAG for their intended ids, Fourier/Plancherel and weak-derivative concepts, Cauchy–Schwarz/product integrability, both exact Mathlib declaration names and inverse-weight terminology. Whole-blueprint searches included Fourier, Plancherel, Cauchy.Schwarz, weak derivative, integrable, square.integrable, Lebesgue, derivative, integrable product and bracket. The finite-field Fourier nodes and Lie bracket nodes have different objects. Reading the nearby Sobolev bundle, symbol-operator, Rellich, closed-range and Fourier-representative statements showed that none supplies these Euclidean assertions. The Fourier-representative node assumes the moments that this item proves and cannot be used here.

For the weak-derivative node, LeanFinder was run with both the monomial identity and the compact-test/L2 phrasing; LeanSearch, Loogle and two greps were also run. I read the Schwartz, tempered-distribution and Lp comparison declarations. The tempered Fourier identity is related, but passing from compactly supported tests to Schwartz tests and passing from regular-distribution equality to almost-everywhere equality are additional mathematical steps. This node therefore stays unsplit, rather than being declared a Mathlib leaf on the basis of its related hits.

For the inverse-weight node, all four search kinds led to `integrable_rpow_neg_one_add_norm_sq`. I read lines 147–154 and its ambient assumptions: a finite-dimensional real normed space with Borel measurable structure and an additive Haar measure. Euclidean space and volume meet them. Substitution of exponent parameter 2s gives exactly the stated power and strict dimensional inequality.

For the product node, all four kinds found the general Holder product theorem (alongside inner-product variants). I read `MemLp.integrable_mul` at lines 1085–1088 and the Holder exponent definitions and 2,2 instance in `Mathlib/Data/ENNReal/Holder.lean`. Real-valued measurable L2 functions meet the two MemLp hypotheses; the instance supplies HolderTriple 2 2 1. No extra finite-measure or support assumption is required.

## Not duplicates

`lem-sfb-l2-weak-derivative-fourier-identity` vs `lem-sfb-weak-sobolev-fourier-moments`: the child identifies the Fourier transform of one weak derivative with a monomial multiple, without any threshold or L1 conclusion; the item obtains every indicated L1 moment by combining this identity with a finite-coordinate weight estimate and two independent analytic tools.

`lem-sfb-euclidean-bracket-integrable` vs `lem-sfb-weak-sobolev-fourier-moments`: the child is a scalar weight-integrability theorem with no function u or derivative hypothesis. `lem-sfb-l2-product-integrable` vs `lem-sfb-weak-sobolev-fourier-moments`: the child is product integrability for arbitrary real L2 functions and makes no reference to Fourier transforms. No shared Stacks tag or existing exact DAG duplicate was found.

## Argument retained for the unsplit child

For a future split of the weak-derivative Fourier identity, the intended argument is to test against cutoffs of Schwartz functions. If chi is smooth, compactly supported and identically one near zero, then chi(x/R)phi tends to phi with every derivative through the fixed order in L2. Leibniz's formula and rapid decrease show this explicitly: the term with no derivative of chi is a dominated tail, and each other term contains a bounded derivative of chi with a factor R to a negative power multiplying an L2 derivative of phi. The L2 pairings therefore extend the given weak identity to Schwartz tests. Fourier transformation of the resulting tempered derivative identity gives the monomial multiplier by iterating the single-direction identity; the L2/tempered Fourier comparison identifies the two transforms, and injectivity of regular distributions gives equality almost everywhere. The Fourier transform of v is L2, so division by the nonzero constant (2 pi i) to the multi-index order gives the monomial L2 assertion. This is a report hint only: the new node carries no proof and no proof dependencies.

## What could not be finished

No part of this one-level split remains unfinished. The new weak-derivative identity is deliberately left as an unsplit statement for the next stage-1 worker. The proof of the item uses that statement, not the proof hint above.

## Review by Q57

I checked the item against Demailly's Sobolev inclusion in the accessible excerpt, rather than pretending that the excerpt contains a Fourier calculation. The locally read analytic sources are the actual pinned Mathlib files: the Sobolev weighted-product argument at lines 241–275, the tempered derivative formula at 568–573, the Lp comparison at 120–129, the bracket theorem at 147–154, and the product theorem at 1085–1088. These support the stated proof route while leaving the genuine compact-test weak-derivative bridge as an explicitly open theorem. The statement of every new node introduces its own domain, measure, functions and hypotheses; its only external notion is the field convention, whose definition node I opened.

In step 1 I read the whole new weak-derivative statement and verified that it gives square integrability of xi_i to power t times h after taking alpha=t e_i. The parent's assumptions provide that exact derivative and the same bilinear compact-test identity; I did not substitute a classical derivative or a conjugated weak-pairing convention. Step 2 is the displayed maximum estimate with a finite sum of the square-integrable quantities from step 1; taking its nonnegative integral is all that is required, and there is no hidden equivalence of Sobolev norms. In step 3 the cited bracket statement really concerns the Euclidean norm and exponent s=t-j; the assumed strict bound t>r+m/2 gives s>m/2 for every j in range. Its conclusion dominates the square of the defined b. In step 4 the cited product statement applies to exactly the measurable real functions a and b already constructed; cancellation of the positive powers of w gives the desired integrand. Step 5 uses only equality off a null set and the definition of the Lebesgue integral. All three citation quotes were copied from the corresponding node statements.

I tested the analytic assertions on zero functions, m=1, alpha=0, j=0, and altered representatives on null sets. Alpha=0 correctly says v=u almost everywhere. At xi=0 and j=0 the power is 1; there is no singular inverse norm because w is at least 1. At the excluded boundary s=m/2 the inverse-weight integral diverges logarithmically, which confirms the need for the strict inequality in its stated range. A nonzero constant on the whole Euclidean space fails the parent's L2 hypothesis and is not an exception. Neither Mathlib leaf assumes compact support or finite total measure, and the Fourier-identity child does not assume intermediate weak derivatives. Its complex scalar has the positive 2 pi i sign required by the parent's negative Fourier exponent.

Against delivery-errors B–E, I found no statement sketch in a new node, no unintroduced analytic convention, no unsupported tag, no statement-versus-proof substitution, no circular use of the Fourier-representative conclusion, and no new node equal to a clause of the item. The elementary weight estimate and almost-everywhere argument stay in the item. Every non-elementary application cites the statement giving it. The actual proof-step lengths are 383, 523, 392, 316 and 287 characters; no long step hides a further lemma. I corrected the Lp source line after reading it and kept the original statement unchanged. I sign this split as Q57.
