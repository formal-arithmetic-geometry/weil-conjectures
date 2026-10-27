# Q132 stage-1 report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-smooth-branch-completed-differential-pullback.json`: item, statement; split into seven steps, no Mathlib match for the combined assertion.
- `citations.json`: thirteen literal statement quotations covering every use in all seven steps.
- `report.md`: this report. The sandbox also retains the actual searches in `searches.jsonl` and the item-writing script.

New nodes: 0. New Mathlib leaves: 0. The item statement and statement dependencies are unchanged. All prior search records and provenance are retained.

## Attachments

None. Searches in the current `lean/WeilConjectures/` for the exact blueprint tag and completed/smooth-branch differential notions found no declaration stating the item. Existing occurrences of `PowerSeries.derivative_subst` in zeta-series proofs cover a formal chain-rule component only, not this theorem. No Lean was written or compiled.

## WANTED

None. The item is an agent assembly of inputs already represented in the DAG; its combined assertion is not attributed verbatim to Stacks 0C4D or 0C4B.

## Problems found and corrected

The imported node had no proof. Its definition of continuous extension explicitly supplies no existence theorem, so the proof cites the existing completion comparison for existence and continuity rather than citing that predicate as a theorem. Likewise, the rational embedding is proved using a basis of algebraic differentials, not by asserting that differentiation is injective on functions (which would be false, especially in characteristic p).

The formal presentation relations require a chain rule for infinite series. The existing formal-relative-derivation expansion node gives exactly that identity, including the local-map hypotheses and empty-variable cases. No polynomial approximation theorem is assumed without a citation.

The latest blueprint chapter and unit, and the nearest blueprint ancestor's current proof, were read. They do not state this combined auxiliary algebra theorem; it belongs to the existing semistable/nodal-refinement ancestry recorded in the item. The proof retains that route. Blueprint searches for continuous differentials, formal parameter and differential pullback found no matching imported node. Whole-DAG searches found the existing comparison/free/chain-rule/localization tools, so creating additional nodes would duplicate them.

## Unfinished work

None for this one-level split. Existing unsplit dependency nodes remain separate queue items as required. No new unsplit dependency is introduced.

## Not duplicates

No new nodes are created. The item itself already existed; its seven steps use existing statements rather than creating copies of its clauses.

## Review by Q132

I read the source of the item in `curves.tex`, Tag 0C4D (`lemma-nodal`), especially the polynomial Jacobian presentation and passage to the completed local ring. I also read Tag 0C4B (`lemma-fitting-ideal-well-defined`), whose coordinate-change proof explicitly calls for the chain rule and omits details. Neither source by itself claims the full mixed completed/rational naturality assertion. The agent provenance now says precisely which existing nodes fill those details. There are no new nodes whose sources need separate review.

For Step 1 I opened the statements of `lem-trf-completion-kahler-differential-comparison` and `lem-trf-formal-power-series-continuous-free`. The first gives both the continuous extension and the differential inverse-limit isomorphism, including its action on algebraic differential symbols and all completed elements. The second gives a free basis and the coefficientwise derivative formula, not just freeness. D is the localization of a finite-type affine neighbourhood of the given smooth rational point, so its residue field is k and the finite-separable coefficient-section condition is satisfied by the identity k/k. The fixed complete local k-algebra coordinate isomorphism induces the needed quotient differential isomorphisms and their inverses. This constructs E without presupposing a completion theorem for all algebraic differentials of k[[t]].

For Step 2 I opened `lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension` and `lem-weil-pbc-kahler-differentials-localization`. I also read their sources: `morphisms.tex` Tag 02G1 and `algebra.tex` Tag 00RT, as well as the explicit quotient-rule extension in `more-algebra.tex` Tag 07PE. The given smooth one-dimensional curve has differential rank one at the point, and localization produces a basis over D and then F. E sends that basis to a unit multiple of dt because it is an isomorphism of rank-one free T-modules. Thus an F-coefficient cannot map to zero unless it is zero, using exactly the stipulated field embedding F into L. I checked the quotient formula for a/c explicitly; no separability of L/F, derivative injectivity on fields, or flat-completion theorem is silently used. The rank lemma is a generic off-unit tool, declared in `split_report.tool_uses`; it does not replace the local-term unit route.

For Step 3 the cited universal-property node states exactly the representing property for derivations and its symbol construction. The completion comparison states continuity and existence for A, whose hypotheses match the finite-type rational local ring of the item. Its quotient identifications supply representatives a_N in A of every completed element. Linearity and locality give the filtration estimate for the map to T dt; coefficientwise differentiation lowers order by at most one. The equality then follows coefficientwise from continuity and the explicitly dense image, rather than from an unspecified assertion that naturality survives completion. Tensor associativity is written with both maps.

For Step 4 I opened `lem-trf-formal-relative-derivation-expansion` and `def-trf-formal-power-series-partial-derivative`. The former states the exact relative chain rule for a local homomorphism between formal series rings, in arbitrary characteristic, including empty variable sets. The formal presentation is continuous and local, so every z_i(t) lies in (t). Differentiation after the presentation map is a relative derivation by the coefficientwise Leibniz rule supplied by the latter node. Applying the chain rule to g_j, whose image is zero, proves the relation. This is neither an appeal to the proof of the cited node nor a citation of a definition for a theorem it does not state.

Step 5 uses only the symbol generation from the cited universal-property/construction statement and the earlier proved formulas. Both maps are evaluated on da tensor c and give the same expression, so the extension to arbitrary rational coefficients is explicit.

For Step 6 the same formal-relative-derivation statement applies with one source and one target variable, because sigma is local and fixes k. Its conclusion gives the chain rule on every power series. I wrote out its extension to f/g by the quotient rule. Isomorphisms preserve maximal ideals; v therefore has order exactly one, and its derivative has nonzero constant term. The inverse-unit recursion and the fraction-field extension are explicit elementary arguments. This excludes an invalid characteristic-p parameter change t to s^p: it is not an isomorphism.

For Step 7 the inverse of nu is explicit, and the unit factor proves equality of the two power-series lattices. I evaluated all three naturality squares on their own differential generators; generation is exactly what the cited differential-symbol statement supplies. Rational scalar transport uses tau, and integral scalar transport uses sigma. Thus no compatibility is hidden behind the word transports.

I checked small cases: A=k with a constant map (all source differentials and pullbacks vanish); a smooth affine-line point with its usual parameter (E and delta send du to dt); a characteristic-p map u to t^p (beta is zero, consistent with every Jacobian identity); parameter changes t to a s plus higher terms with a nonzero (v' remains a unit even in characteristic p); zero formal variables (all sums empty); and repeated or zero defining equations (their displayed relations are zero). In characteristic p, d(z^p)=0 is compatible with injectivity of the *module map* delta because the differential itself is zero. No statement dispute or hypothesis correction was needed.

I checked delivery-errors B–E against the files: self-contained unchanged item, no fabricated or duplicate new nodes, no new unsplit proof sketches, correct literal TeX, every cited fact actually present in its statement, no cycle back to the item, agent proof provenance for the assembly, and no SGA source. Every proof step is below 2000 characters (the largest is 1232), and each non-elementary tool is cited. All actual Mathlib queries were made through msearch.py and their returned log records were retained verbatim; two semantic phrasings, Loogle and source grep were read. The closest hits concern polynomial differential functoriality, standard smooth freeness and Laurent-series ring completions, not the combined theorem.
