# Stage 1 report: lem-sfb-left-resolution-bounded-minus

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-bounded-minus.json` — repaired item with an eight-step proof; no Mathlib match.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-objectwise-cochain.json` — statement-only objectwise resolution interface; no Mathlib match.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-bicomplex-total-exists.json` — statement-only support and diagonal-total interface; no Mathlib match.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-totalized-augmentation.json` — statement-only natural totalized augmentation; no Mathlib match.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-additive-total-transport.json` — statement-only bounded additive total-transport interface; no Mathlib match.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-single-row-total.json` — statement-only row-total identification; no Mathlib match.
- `citations.json` — verbatim excerpts for every cited node in every item step.

## Attachments

None. The read-only slopmaster2 source has no sorry-free project declaration tagged or named as this item.

## WANTED

None.

## Problems found and corrections

The returned split exposed two substantive errors. The old additive-transport child asserted `mapTotalIso` from mere existence of the two totals. That is false for arbitrary totals: an additive functor need not preserve an infinite diagonal coproduct. I replaced it with the source-level interface used by `preservesTotal_of_isStrictlyLE`: the bicomplex is strictly bounded above in the first index and every row is strictly bounded above in the second, so only finitely many summands on each diagonal can be nonzero. The present repair also supplies the missing finite-coproduct hypothesis on $C$; bounded support alone does not make those coproducts exist. The item step now cites those support hypotheses explicitly.

The old `total-upper-bound` child merely restated the parent item's elementary bound clause. I removed that child and put the complete argument in the functor-construction step: a nonzero diagonal term has `p ≤ b` and `q ≤ 0`, hence total degree `p+q ≤ b`.

I also repaired scope and typing. The child statements now introduce their own bicomplexes and diagonal totals rather than referring to an undefined `B`, `FB`, or target total; the totalized-augmentation statement explicitly includes the single-row total interface; and the statements do not cite the abelian first-quadrant definition for the preadditive resolution category. The objectwise child now says “cochain-complex resolution functor.” Finally, all blueprint places were changed from the inaccurate claim that the parent proof contains a bounded-minus construction to an honest reference to the parent sentence about K-flat resolutions and the concrete `CochainComplexMinus.lean` refinement.

## Not duplicates

- `lem-sfb-left-resolution-objectwise-cochain` vs `lem-sfb-unbounded-kflat-resolution-existence`: the existing node gives an unbounded K-flat replacement; this node gives the objectwise integer cochain resolution, augmentation, and degree support.
- `lem-sfb-left-resolution-bicomplex-total-exists` vs `lem-weil-pbc-total-bounded-below`: that node assumes lower bounds in the first index and nonnegative second index; this node handles the upper-bounded resolution bicomplex with resolution degree bounded above by zero.
- `lem-sfb-left-resolution-totalized-augmentation` vs `lem-sfb-left-resolution-bounded-minus-augmentation`: the returned child stated the final item clause; this node only gives the intermediate totalized map before additive transport and single-row identification.
- `lem-sfb-left-resolution-additive-total-transport` vs `lem-sp-cartan-eilenberg-mapped-total`: the existing node treats a Cartan–Eilenberg presentation with a natural-number resolution index; this node treats the uniformly bounded integer bicomplex and the resulting `mapTotalIso`.
- `lem-sfb-left-resolution-single-row-total` vs `lem-sp-double-complex-single-row-total-iso`: the existing node is a natural-indexed single-row total isomorphism; this node is the integer `up ℤ` row-zero identification used here.

## Review by Q54

I reread the returned item and all retained child files, the unit and chapter records, the complete parent blueprint proof, and the relevant source ranges in `LeftResolution/Basic.lean`, `LeftResolution/CochainComplexMinus.lean`, `BicomplexColumns.lean`, `TotalComplexMap.lean`, and `BicomplexRows.lean`. The source variables at `CochainComplexMinus.lean:32–36` provide the full and faithful preadditive embedding and zero-preserving resolution; finite coproducts of $C$ are assumed at line 93 and additivity of the embedding at line 208. The objectwise construction and its quasi-isomorphic augmentation are at `Basic.lean:20–145`; support and total existence are at `CochainComplexMinus.lean:48–108`; the bounded-total support instance is at `133–149`; totalized augmentation and its column comparison are at `160–206`; the preservation-of-total instance is at `208–220`; the functor laws are at `226–237`; and the final map and quasi-isomorphism are at `216–256`.

Step 1 packages the supplied `Q` and `π` as the source `LeftResolution` datum, with zero morphisms supplied by preadditivity. Step 2 uses the objectwise child for the functor, augmentation, quasi-isomorphism, and resolution-degree support. Step 3 uses the bicomplex child for both support directions and the two diagonal totals. Step 4 now defines $T(K)=\operatorname{Tot}(B_K)$ in $C$ and $S(K)=\iota(T(K))$ termwise in $A$. This directly gives the essential-image clause. For $n>b$, every diagonal summand of $T(K)^n$ is zero by $p\le b$, $q\le0$; the total and its additive image are zero. The construction and its maps depend on the bicomplex, not on a chosen witness for its upper bound. Step 5 uses the totalized-augmentation statement and the existing bounded-above column comparison, whose strict-bound and columnwise quasi-isomorphism hypotheses match the source. Step 6 uses the corrected additive-transport statement with the first-index and row bounds from Step 3 and explicitly verifies the zero object, finite coproducts, preadditivity, and additivity hypotheses. Finite coproducts are needed in the source of the embedding; abelianness of $A$ supplies its preadditivity. The transport identifies the mapped bicomplex total with precisely the $S(K)$ defined in Step 4. Step 7 uses the integer row-zero total isomorphism. Step 8 writes $a_K=r_K\circ\tau_K\circ e_K^{-1}$ and the naturality equality for $f:K\to L$ using the equations from Steps 5–7. Its source and target are $S(K)$ and $K$; both outer factors are isomorphisms, so the quasi-isomorphism assertion follows from that of $\tau_K$. The literal TAB before “au” has been replaced by the TeX command $\tau$.

I checked the zero complex and a one-term degree-zero complex: all omitted diagonal terms are zero, the only surviving row-zero summand is the expected term, the elementary upper-bound argument still applies for any chosen bound, and the composite augmentation reduces to the objectwise augmentation. I read and retained the earlier search results and ran four new searches for the strengthened finite-coproduct transport statement (LeanFinder, Loogle, grep, and LeanSearch). Loogle and grep locate `CategoryTheory.Functor.preservesFiniteCoproductsOfAdditive` (`Mathlib/CategoryTheory/Preadditive/AdditiveFunctor.lean:213`), but that is just finite-coproduct preservation, not the complete bounded total-complex statement. The child remains unsplit; the four duplicate search records were removed, and unknown-identifier queries are marked unavailable.

## Repair of the 2026-10-17 return

I compared the retained files with the current shared item: it remains unsplit, with the same statement and parent/unit binding. The five children are still absent from the shared DAG. The initial required dry run passed on the retained content (`d11f346e21`); that mechanical success did not repair the mathematical faults in returned head `53e5950421`. This delivery changes the actual statements and proof steps, not just their base.

1. **E2 — STATEMENT-DISPUTED:** the returned additive-transport child was false without finite coproducts. In the full preadditive subcategory of abelian groups on $0,\mathbf Z/2,\mathbf Z/3$, take $B^{0,0}=\mathbf Z/2$, $B^{1,-1}=\mathbf Z/3$ and all other terms and differentials zero. The bounds hold with $b=1$, but none of the three objects is a coproduct of these two nonzero terms. Thus the degree-zero total need not exist. I added a zero object and finite coproducts to the hypotheses on $C$, as in `BicomplexColumns.lean:746,874–912`. Under the repaired hypotheses, each degree $n$ has possible support only for $n\le p\le b$; the empty interval gives zero, a singleton gives its term, and a two-term interval now has the required coproduct. The additive preservation theorem then applies to these finite coproducts; `TotalComplexMap.lean:33–145` supplies the complex isomorphism and its naturality. No finite-coproduct hypothesis on $D$ is needed: the image coproducts exist by preservation of the source coproducts. The item already assumed finite coproducts in $C$, so its statement is unchanged.
2. **B3 and searches:** I removed the citation of the abelian first-quadrant definition from the preadditive transport child and defined its integer commuting bicomplex and signed diagonal total inline. Its only statement dependency is the actual definition of preadditivity. Four duplicate search records were removed; earlier distinct queries and the append-only search log are retained. I searched the current whole DAG for `preservesTotal` and `mapTotalIso` and the blueprint for “additive total”; no existing node replaces this interface. The Cartan–Eilenberg mapped-total node still assumes Grothendieck abelian categories and a different bounded-below index situation, so it does not subsume the repaired preadditive statement.
3. **E5/C3:** Step 4 now defines $S(K)$ as the termwise image of the $C$-valued total. Its terms are therefore themselves in the essential image of $\iota$; no closure claim about that image is being inferred from summands. Step 6 identifies the correct two complexes and explicitly checks finite coproducts. The support argument proves an upper bound for $T(K)$ and hence for $S(K)$ because the additive embedding preserves zero objects. The source `minusResolutionFunctor` and `totalπ` have exactly this construction.
4. **B4:** Step 8 contains the actual TeX command $\tau_K$, references Steps 5–7, and spells out the composite and its naturality in the correct order.
5. **Clerical:** `split_report.summary` now lists exactly five children and carries the upper-bound argument as an item step. The declared tool use names Step 5. I refreshed the verbatim transport excerpts in `citations.json`; every item-step citation still quotes the actual statement it uses. The longest item step is below 2000 characters, so there is no long non-elementary step hiding an additional lemma.

## What I could not finish

Nothing remains unfinished in this stage-1 split.
