# Stage-1 report: lem-trf-regular-local-ufd-boundary-factorization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-regular-local-ufd-boundary-factorization.json`: repaired the proof dependencies and the declared off-unit tool use.
- `dag/nodes/sec-trace-formula/lem-trf-regular-local-nonsquare-prime.json`: unsplit support statement; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-regular-local-pic-zero.json`: unsplit support statement; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-finite-projective-local-free.json`: Mathlib leaf, `Module.projective_of_localization_maximal`.
- `dag/nodes/sec-trace-formula/lem-trf-factorization-exists.json`: unsplit support statement; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-ufd-height-one.json`: unsplit support statement; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-nagata-invert-prime.json`: unsplit support statement; no Mathlib match.
- `citations.json`: verbatim statement quotes for every cited node at every proof step.
- `report.md`: this report.

## Attachments

None. I searched the read-only slopmaster2 source for the item id, regular-local UFD names, and the support statements. No sorry-free declaration states the complete item. The existing `lem-weil-pbc-regular-local-localization` node is used as a generic tool; it is not an attachment to this item.

## WANTED

None. The Stacks sources and the Mathlib source are present locally.

## What was wrong in the returned split

(1) The seven support nodes had corrupt source records `{document: "l", place: "i"}`. I replaced them with the actual Stacks tags and line locations, and recorded the Mathlib file and theorem lines for the Mathlib leaf. I also supplied complete `lean_audit` records (`master` and `slopmaster2`, each with state `none`, empty declarations, and empty missing lists) on every retained new node.

(2) `lem-trf-regular-localize` duplicated the existing `lem-weil-pbc-regular-local-localization` statement. I removed the duplicate file, repointed Step 4 and its citation to the existing statement, and declared that cross-unit node as the `sk-thm-p1` generic tool used by the local UFD route.

(3) Step 4 used the cotangent/Nakayama argument to choose $x\in\mathfrak m\setminus\mathfrak m^2$ and the induction criterion to make $\mathfrak pA_{\mathfrak q}$ principal, but omitted those statement dependencies. I added the cotangent-dimension, Nakayama, nonsquare-prime, existing localization, and height-one criterion nodes to that step and to `proof_deps`, with verbatim quotes in `citations.json`.

(4) `lem-trf-finite-projective-local-free` cited the categorical internal-module definition `def-sfb-finitely-presented-module`; its ordinary ring/module statement requires `def-sc-finitely-presented-module`. I corrected the statement, `stmt_deps`, and the Step 5 citation.

The duplicate node was also removed from the report and from the item's dependency list. The factorization-existence node remains an unsplit statement-only support node; its Mathlib searches did not establish the full ACC specialization.

## Not duplicates

- `lem-trf-regular-local-nonsquare-prime` vs `lem-weil-pbc-regular-local-hypersurface-criterion`: the new node concludes primality and domain of the quotient, while the existing node concludes only regularity of the quotient.
- `lem-trf-regular-local-pic-zero` vs `lem-sc-h1-gm-pic`: the new node concerns Picard triviality of a localization of a regular local ring; the existing node concerns a curve calculation.
- `lem-trf-finite-projective-local-free` vs `lem-weil-pbc-regular-local-mcm-free`: the new node is the general finitely presented/local-freeness criterion; the existing node is freeness of maximal Cohen–Macaulay modules over a regular local ring.
- `lem-trf-factorization-exists` vs `lem-trf-regular-local-ufd-boundary-factorization`: the support node supplies irreducible existence under ACC on principal ideals; the item additionally proves uniqueness, parameter primality, and the localization-unit characterization.
- `lem-trf-ufd-height-one` vs `lem-trf-regular-local-ufd-boundary-factorization`: the support node is the general Noetherian-domain height-one criterion; the item proves its hypotheses and the boundary factorization.
- `lem-trf-nagata-invert-prime` vs `lem-trf-regular-local-ufd-boundary-factorization`: the support node is Nagata's localization criterion for one irreducible; the item applies it inside the regular-local induction.


- `lem-trf-regular-local-nonsquare-prime` vs `lem-ag-cartier-reduced`: the existing node concerns smooth reducedness of a finite-type matrix group, while the new node concerns a nonsquare element in a regular local ring.
- `lem-trf-regular-local-nonsquare-prime` vs `lem-sc-regular-local-domain`: the existing node proves only that a regular local ring is a domain; the new node proves that a nonsquare element is prime and its quotient is a domain.
- `lem-trf-regular-local-nonsquare-prime` vs `lem-sbc-regular-cartier-generic-stalk-dvr`: the existing node concerns a generic stalk of an effective Cartier divisor and concludes a DVR; the new node concerns arbitrary nonsquare elements and concludes primality.
- `lem-trf-regular-local-nonsquare-prime` vs `lem-sbc-strict-hensel-regular-divisor-quotient-domain-part`: the existing node concerns a strict henselization quotient under a geometric-point hypothesis; the new node concerns the quotient of the original regular local ring by a nonsquare element.
- `lem-trf-regular-local-nonsquare-prime` vs `lem-weil-pbc-flat-polynomial-append-fibre-regular-sequence`: the existing node is a flat polynomial localization/fibre statement with a regular-sequence hypothesis; the new node is a primality criterion in a regular local ring.
- `lem-trf-regular-local-nonsquare-prime` vs `lem-weil-pbc-flat-polynomial-append-tensor-fibre`: the existing node proves flatness of a tensor fibre in a polynomial construction; the new node proves primality of a nonsquare local parameter.
- `lem-trf-regular-local-nonsquare-prime` vs `lem-weil-pbc-flat-regular-fibre-parameter-selection`: the existing node selects parameters for a flat regular fibre; the new node proves that any nonsquare element is prime.
- `lem-trf-regular-local-nonsquare-prime` vs `lem-weil-pbc-geometrically-regular-over-field-flat`: the existing node concerns geometrically regular local algebras and flat polynomial maps; the new node concerns a prime element criterion with no field or geometric-regularity hypotheses.
- `lem-trf-regular-local-nonsquare-prime` vs `lem-weil-pbc-global-complete-intersection-local-regular-sequence`: the existing node proves a regular sequence in a polynomial localization; the new node proves primality of one nonsquare element and domain of its quotient.
- `lem-trf-regular-local-nonsquare-prime` vs `lem-weil-pbc-hypersurface-derivation-regular`: the existing node uses a derivation with a unit derivative to prove regularity of a global quotient; the new node uses a local nonsquare condition to prove primality.
- `lem-trf-regular-local-nonsquare-prime` vs `lem-weil-pbc-popescu-find-sequence`: the existing node constructs generators with annihilator properties in a Noetherian localization; the new node states a primality result for a regular-local parameter.
- `lem-trf-regular-local-nonsquare-prime` vs `lem-weil-pbc-regular-local-generators-regular-sequence`: the existing node treats a full regular system of parameters and regular sequences/quotient dimensions; the new node treats one arbitrary element outside m² and concludes it is prime.

## Mathlib searches

The retained support nodes reuse the recorded `msearch.py` searches in `searches.jsonl`; no statement changed, so no search was repeated. The only Mathlib leaf is `lem-trf-finite-projective-local-free`, matched by `Module.projective_of_localization_maximal` in `Mathlib/RingTheory/LocalProperties/Projective.lean:131–133`. Searches for the regular-local localization, Picard, factorization, height-one, Nagata, and nonsquare-prime statements found only generic infrastructure or no match.

## Review by NV

I reread the item against Stacks More on Algebra Tag 0AG0 (the regular-local UFD proof) and the cited algebra sources: Tags 00NP, 00NQ, 0AFS, 0AFT, 0AFU, 034R, and 00NX, together with More on Algebra Tag 0AFZ. I opened the current statement of every existing node cited by the item and every retained new node. The item statement remains unchanged, including the empty parameter list and empty product.

Step 1 uses the regular-local and parameter definitions and the existing regular-local-domain statement. Step 2 uses the parameter definition, cotangent-dimension equality, and Nakayama; these give a basis of $\mathfrak m/\mathfrak m^2$ and hence put every parameter outside $\mathfrak m^2$. Step 3 uses the new nonsquare-prime statement, the existing hypersurface criterion, and the domain statement, so each parameter is prime.

Step 4 is the induction from Tag 0AG0. It checks the dimension-zero field case; in positive dimension it uses the Step 2 cotangent/Nakayama argument and the nonsquare-prime statement for $x$. For primes not containing $x$, the existing localization node gives regular local rings, and the height-one criterion is explicitly cited for the induction conclusion that each localized height-one ideal is principal. Step 5 uses the corrected ordinary finitely presented-module definition through the Mathlib projectivity leaf, then the Picard-zero statement to principalize the localized ideal. Step 6 cites ACC factorization and Nagata's criterion after clearing denominators. Step 7 applies the height-one criterion to the Noetherian domain. Steps 8 and 9 are the elementary finite-factor localization calculation, including $r=0$.

I checked the hypotheses at each use: the localized primes avoid $x$ in Step 4; the localized ideal is finitely presented over the Noetherian localization and locally free of rank one; the multiplicative set in Step 6 is generated by the prime $x$; and the height-one criterion is applied only after the domain and Noetherian hypotheses are established. I retested the empty list, dimension zero, a DVR, and $k[x,y]_{(x,y)}$ with $T=x$ and $T=xy$. The repair addresses every numbered return point without weakening the statement.

## What I could not finish

Nothing remains for this split; the required dry run is the remaining delivery check.
