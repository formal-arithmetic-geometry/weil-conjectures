# Q38 stage-1 repair report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-complete-toric-facet-valuations.json`: substantive split into 18 steps, using 15 existing DAG nodes. The statement is byte-for-byte unchanged from the current shared repository.
- `citations.json`: 26 verbatim statement quotations, one for each node use in each numbered proof step.
- `searches.jsonl`: retained the earlier searches and appended new searches of the item with the required search wrapper.

There are **zero new nodes and zero new Mathlib leaves**. The two clause-alias children from the returned branch are not delivered. Their retained files and provisional repair attempt are archived under `retained-returned-attempt/` in this sandbox, and their original search log is retained. Only the parent appears under the delivery's `dag/nodes/` directory.

## Attachments

None. The required search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag and toric, facet, and monoid-completion notions found no declaration stating the item. The read-only master remains reference material, not evidence of a completed proof.

## WANTED:

WANTED: Kato (1994), *Toric singularities*, for comparison with the toric divisor theory motivating this auxiliary item. This bibliographic request is retained from the returned report. The repaired proof does **not** invoke an unread Kato theorem, and in particular does not assert that Kato Theorem 11.6 supplies any missing inference.

WANTED: Nizioł (2006), Proposition 2.6, for comparison with the ancestor complete-local divisorial-recognition problem. It is not used in this proof.

## What was wrong and what changed

The maintainer's D1 return is correct: the previous two steps only applied new nodes that restated the cone and boundary-valuation clauses. Adding the same assertions under two names was not a mathematical split. I removed those two uncommitted children from the delivery and placed the arguments in the parent itself. No new clause-alias node replaces them.

The cone argument now starts with the existing lattice-cone and finite rational H-description theorems. It removes redundant inequalities, constructs a rational point strictly inside each remaining supporting face, proves those are exactly all facets, and normalizes each rational form on the lattice by clearing denominators and dividing by the gcd. Its uniqueness argument uses the exact image condition `ν_F(G)=Z`.

The ring argument uses the existing general coefficient-family description of completed monoid rings. It proves nonvanishing in the Cohen quotient by positive-weight induction on the equation `z^q=θb`. For a facet, coefficient projection onto the face is a surjective ring homomorphism; explicitly grouping coefficients by the finitely many excluded monoid generators proves its kernel is the indicated monomial ideal. Its quotient is another allowed complete model, so the existing saturated-model normality statement proves primeness.

For height one, the proof does not subtract global dimensions. It chooses `e∈G` with `ν_F(e)=1`, moves it into the monoid by adding a large multiple of a lattice point in the relative interior of `F`, and forms a monomial ratio `π` with denominator in the face. The same shift construction gives, for every `q∈P`, an actual unit `u_q` in the localization and an equality `z^q=u_q π^{ν_F(q)}`. This proves that the localized maximal ideal is `(π)`, so the existing DVR characterization and dimension bound apply. This actual ideal generator, rather than merely a primitive abstract character, proves the normalization of the valuation.

Finally, exhaustion of height-one monomial primes is written as a finite product contradiction: if a prime contains none of the facet ideals, choose one monomial outside that prime from each facet ideal and multiply them. The resulting exponent is strictly positive on every facet. A sufficiently large multiple dominates the exponent of the monomial in the prime, forcing a power of the chosen product into the prime. This contradicts primality. No unproved general face classification or toric divisor theorem is hidden in this step.

The source field is maintained from the current repository. The new `proof_origin` is explicitly `by: agent`; ILO is contextual material for the complete models. The item's chapter, unit, ancestry, created record and all other maintainer-owned fields are retained. Its statement dependencies remain the seven original definition nodes, and its proof dependencies are exactly the union of its proof-step uses.

## Review by Q38

I read the worker contract, stage-1 rules, SETUP's three blueprint levels and tool-lemma rule, GOAL, DAG sync instructions, and delivery-errors B--E. I read the chapter and unit records, the current main-20261015 proof of the blueprint ancestor, the current item and its complete-recognition parent, and every cited node's statement. The current ancestor proof is about contracting correspondences; this auxiliary toric item retains its existing historical nearby-duality/log-regular ancestry. I change no unit binding or route above the node level.

I read ILO Exposé VI 1.4 and 1.6 (printed pp. 69--70), VI 3.7 (p. 75), and VIII Remark 3.1.29 (p. 103), directly from the local PDF text. VI 1.6 displays the field and Cohen complete models but is not a proof of the boundary-prime theorem. VI 3.7 discusses the group splitting, and VIII 3.1.29 discusses fan desingularization; neither supplies the returned missing arguments. The repaired proof therefore does not present any of these places as a direct facet/valuation theorem. I also read the local Stacks source for Tags 00FN (`lemma-Noetherian-permanence`), 0316 (`lemma-completion-Noetherian-Noetherian`), and 00PD (`lemma-characterize-dvr`). The last explicitly gives the equivalence between a DVR and a Noetherian local domain with maximal ideal generated by a single nonzero element, exactly as the cited DVR node states. The dimension bound cited in Step 15 is the existing 00KQ tool.

For each numbered step I checked both the inference and the exact scope of the cited statements:

1. `lem-trf-sharp-cone-lattice-intersection` states finite freeness, pointedness, spanning, and `P=σ∩G`. These are exactly the inputs, with the zero lattice handled before the positive-dimensional cone argument.
2. `lem-trf-rational-cone-dual-finite` states a finite rational inequality presentation for the finite generator cone. Deleting redundant inequalities is finite, and summing generators gives a strictly positive rational point because every remaining form is nonzero and the generators span.
3. No further lemma is invoked: irredundancy gives a witness violating just one inequality; the explicitly chosen segment point has all other inequalities strict, and small basis perturbations in its kernel prove codimension one. This is a finite rational linear-algebra calculation.
4. No further face theorem is assumed: nonnegative generator expressions show that a supporting face is generated by precisely the zero-valued generators. Summing these forces an active inequality, and the given codimension-one hypothesis identifies the hyperplane. This proves the complete facet list.
5. The only cited additional fact is the lattice equality in the first node. The integral normalization is the denominator/gcd calculation on a finite lattice basis, uniqueness is `cZ=Z`, and scaling the point from Step 3 supplies the lattice point needed later. The one-dimensional sole-facet case permits the zero point.
6. The Cohen definition supplies a principal ideal domain and its nonunit `p`. `lem-weil-pbc-finite-type-algebra-noetherian` supplies Noetherianity of the finite-type monoid polynomial ring; `lem-weil-pbc-adic-completion-noetherian` supplies it for the completion; and `lem-weil-pbc-surjective-image-noetherian` supplies it for the quotient. No completion theorem is inferred merely from a definition.
7. `lem-trf-sharp-monoid-positive-grading` supplies the positive integral weight with the pointed lattice hypotheses from Step 1. `lem-trf-monoid-completion-coefficients` applies to the finitely generated embedded product monoid and to the complete Noetherian coefficient ring. Its statement, not its proof, explicitly identifies all coefficient families and finite convolution. The Cohen definition supplies the required completeness.
8. The coefficient statement and the Cohen ring's domain/nonunit-uniformizer properties give the displayed weight induction. The hypothesis `θ-p∈(nonzero monomials,t)` is used to identify the constant coefficient as exactly `p`; at the first possible nonzero coefficient of a putative factor one would obtain `p b=1`. This proves the asserted monomials stay nonzero in the quotient.
9. Using the fs definition, the face is finitely generated by the generators in it and is saturated by the explicit `Nν_F(g)=0` calculation. The coefficient lemma applies to this monoid embedded in the same finite free lattice, with the restricted positive weight.
10. The coefficient lemma permits all the grouped families `b_i`. The face property verifies multiplicativity coefficient by coefficient; the finite grouping formula proves the exact kernel as an algebraic ideal, not only its closure. No identification of completion and quotient is asserted without that kernel computation.
11. The explicit quotient identifies `R/p_F` with the allowed field model or with the Cohen model for `S` and `θ_S`. The latter still has the exact required congruence to `p`, including when the face quotient has equal characteristic. `lem-trf-log-regular-saturation-normality` states a nonzero normal domain for exactly these alternatives, proving primeness. Applying the already written coefficient argument for `S` proves the monomial membership criterion used later.
12. The relative-interior lattice point and that membership criterion distinguish the primes. A positive-valued generator gives nonzeroness. The localization definition states its maximal ideal. Localized Noetherianity is justified directly by generators of contracted ideals, and the domain inclusion is explicit.
13. Primitivity gives `e` of value one. All the other facet values of `f_F` are strictly positive, so the finite inequalities can be satisfied by a single sufficiently large `N`. The cited saturated lattice equality puts the numerator exponent in `P`. The membership criterion makes the denominator invertible and puts the numerator in the prime.
14. The same finite-inequality computation for `q-ν_F(q)e` constructs the unit `u_q`, with both its numerator and denominator in the face. Cancellation in the domain's fraction field verifies the formula exactly, and the finite ideal generators from Step 10 show the maximal ideal is generated by `π`.
15. The DVR node states precisely the Noetherian-local-principal-maximal-ideal characterization being applied. The generic dimension bound gives dimension at most one; the nonzero maximal ideal gives dimension at least one. Extension and contraction of prime ideals, with the fraction membership check written in the step, verifies the item's stated height-one convention.
16. `lem-sc-dvr-valuation-ring-characterization` states that a uniformizer has normalized value one and elements of the DVR have nonnegative values. `lem-sc-dvr-valuation-arithmetic` supplies additivity. Applying both to a unit and its inverse gives value zero, hence the already proved monomial factorization gives the exact formula. No ramification factor is silently set to one.
17. Only the half-space description already proved and the cited equality `P=σ∩G` are needed beyond elementary prime-ideal algebra. The chosen product avoids the prime; its facet values are all positive; a large power is divisible by the monomial that belongs to the prime. This proves exhaustion without appealing to an unread theorem.
18. For `P={0}`, the only chart monomial is `1`, so no prime meets the monomials. The empty intersection is the zero vector space. With `n=0` the product monoid is just `P`, so the same computations apply.

I checked the small cases mathematically. For `P={0}`, the facet/primes lists are empty even with parameter variables. For `P=N`, the sole face is zero, `e=1`, `f=0`, and `π=z`; in the allowed ramified example `θ=p-z^m`, `v(z)=1` while `v(p)=m`, as required. For `P=N^2` and `θ=p-xy`, the two prime quotients are the domains `k[[x]]` and `k[[y]]`, and the two localized generators are `x` and `y`. For the saturated parity monoid generated by `(2,0),(1,1),(0,2)` in its parity lattice, the primitive coordinate forms have image `Z`; at the first facet the unit `z^(0,2)` gives `z^(2,0)=(z^(1,1))^2/z^(0,2)`, so the construction gives values 2 and 1 with no unjustified coordinate-basis assumption. The mixed example `θ=p-t` also leaves the face quotient in the same allowed class. These checks include rank zero, rank one, non-free fs monoids, ramification, and arbitrary Cohen residue field.

I searched the whole DAG and blueprint for facet and monoid-completion statements. The existing generic cone, coefficient-family, normality, and Noetherian/DVR statements suffice; none is a duplicate of the whole item. The LeanFinder, Loogle, grep and LeanSearch searches of the item were actually run with `msearch.py`, their hits were read, and a second natural-language phrasing was tried. They return generic Dedekind/number-field/graded-prime or localization declarations rather than this completed toric theorem, so the item is not a Mathlib leaf. Its earlier search history remains alongside the new records.

The two off-unit non-Mathlib uses are declared in `split_report.tool_uses`: completion Noetherianity and normalized DVR valuation. They are generic algebra tools and do not replace the unit's proof route. No cited node reaches back to this item. There are no long non-elementary steps over 2000 characters (the longest step is 896 characters). No statement dispute was found, no source or target was weakened, and no SGA, Lean writing, compilation, Lake, build, or live-project mutation was used.

## Not duplicates

No new nodes are proposed. The two rejected clause aliases are absent from the delivered DAG files; the direct proof reuses existing generic nodes instead.

## What could not be finished

No mathematical argument remains deferred in this split beyond the existing cited DAG statements, which are the intended inputs of a one-level stage-1 split. The wanted literature is for comparison and the ancestor interface, not an additional uncited hypothesis or pending proof step.
