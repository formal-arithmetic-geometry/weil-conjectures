# Stage-1 delivery: lem-sc-affine-cap-section-open-algebra

## Files written

- `dag/nodes/sec-curve-estimates/lem-sc-affine-cap-section-open-algebra.json`: split into four proof steps; the statement is unchanged.
- `citations.json`: a verbatim statement excerpt for each cited node in each step.
- No new nodes; no new Mathlib leaves.

## Attachments

None. A search of `WeilConjectures/` and `Comparator/` in the read-only slopmaster2 source for the item tag, symmetric-algebra quotient, invertible-module section, and nonvanishing-locus terms found no declaration stating this item.

## Sources and corrections

I read the official Stacks Project Tag 01PV, Properties Lemma 28.27.4 and its proof at https://stacks.math.columbia.edu/tag/01PV. Its construction is precisely `B = Sym_R(N)/(s-1)` and its conclusion identifies `Spec(B)` with the nonvanishing open. The local `literature/stacks-project/` checkout is absent on this machine, so the official Stacks page supplied the source text. The item's inherited statement agrees with Tag 01PV; I changed no hypothesis or conclusion. I also read `dag/chapters/sec-curve-estimates.json`, `dag/units/sk-thm-curveestimate.json`, the parent node `lem-sc-affine-cap-section-open`, and the blueprint place inherited by this node. This is an algebra input below the unit route, not a replacement for a unit step.

The prior node had no proof, `proof_deps`, or `proof_origin`. I wrote the standard-open calculation implicit in the Stacks argument, exposed the three algebra identifications as separate steps, and used an existing target-locality lemma to justify the final gluing. Searches of the whole DAG, the blueprint index, and the Lean source found existing nodes for every non-elementary input, so I created none. The existing item's Mathlib searches already record LeanSearch, LeanFinder, and source grep; its result remains no exact match.

## Review by F1

I checked the statement against Stacks Tag 01PV: `R` is commutative, `N` is invertible, `s` belongs to `N`, and no Noetherian or domain assumption is used. The equivalence in the statement gives a finite standard-open cover on which `N` is free of rank one. On each `D(f_i)`, writing `s=a_i e_i` makes membership in `pN` equivalent to `a_i` belonging to the extended prime. This justifies step 1 directly from the item hypothesis, including the cases `s=0` and an empty `V`.

For step 2 I opened all three cited statements. `lem-weil-pbc-localization-quotient-commute` identifies localization of the quotient with the quotient of the localization; its ideal is `(iota(s)-1)`. `lem-weil-pbc-symmetric-algebra-base-change` identifies the localized symmetric algebra with `Sym` of `N_f`. `lem-weil-pbc-symmetric-algebra-free-module-polynomial` identifies the symmetric algebra of the chosen free rank-one module with the one-variable polynomial ring. These are exactly the three transitions in step 2; the base-change node is declared as a generic tool of another unit.

For step 3 I read `lem-weil-pbc-localization-away-polynomial-quotient`: it states `R[t]/(at-1) congruent R_a` for every commutative ring and element, including zero divisors and `a=0`. I read `lem-weil-pbc-principal-localization-open-immersion`: it says the induced spectrum map is an open immersion with image `D(a)`. Applying both over `R_f` gives the stated base change and its image without an extra domain hypothesis.

For step 4 I read `def-weil-pbc-fpqc-covering` and checked its two requirements: each standard localization is flat, and each affine open in `Spec(R)` has a finite affine refinement by the finitely many restricted principal opens. I read `lem-galois-fpqc-descend-open-immersion`, whose statement accepts precisely an fpqc family and open immersions after every base change; this supplies the global open immersion and is declared as a generic tool. I read `def-weil-open-immersion`, whose statement identifies an open immersion with an isomorphism onto an open subscheme. The image is `V` because on every `D(f_i)` it is exactly `D(a_i)`. No cited node is used for a conclusion outside its statement.

I tested the smallest cases explicitly: `N=R`, `s=a` gives `B=R[t]/(at-1) congruent R_a` and `V=D(a)`; `a=0` gives the zero ring and the empty open; `a=1` gives `B=R` and all of `Spec(R)`. These tests also show that no injectivity of `R -> B` is assumed. I checked `citations.json` against the cited statement text after writing the proof. No new-node statement needed an edge-case repair.

## Unfinished

Nothing in this one-level split. The cited unsplit generic tool nodes remain separate stage-1 items.
