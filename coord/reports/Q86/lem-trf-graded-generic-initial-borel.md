## Worker report

Files written for delivery:

- `dag/nodes/sec-trace-formula/lem-trf-graded-generic-initial-borel.json`: existing statement, unchanged; 12 proof steps; status `split`; no Mathlib match for the whole theorem.
- `report.md`: this report, packaged by the delivery tool at its required project location.
- `citations.json` and `searches.jsonl`: sandbox validation evidence. Each cited statement was opened and the applicable statement copied verbatim. The sandbox also contains `write_split.py`, the local preparation script; it is not a delivery file.

New nodes: **0**. New Mathlib leaves: **0**. The proof reuses `lem-trf-monomial-upper-set-finite-basis`, an existing Mathlib leaf of the same unit, rather than adding a second Dickson lemma. The two original definition dependencies are retained.

Attachments: none. Searching `lean/WeilConjectures/` for the exact blueprint tag and for generic initial ideals, Galligo, Borel fixity and Groebner terminology produced no matching project declaration. A Mathlib theorem about homogeneous ideals or leading-term spans would not by itself provide either clause of this item.

WANTED: Bayer--Stillman, *A theorem on refining division orders by the reverse lexicographic order*, Duke Math. J. 55 (1987), the generic-initial-ideal result cited as Proposition 1 in the imported source record, for `lem-trf-graded-generic-initial-borel`.

WANTED: Bierstone--Milman, *Canonical desingularization in characteristic zero by blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), section 8 and the discussion before Theorem 9.6, printed pp.273 and 278, for the imported generic-coordinate context of `lem-trf-graded-generic-initial-borel`.

The local ILO volume was read at VIII 2.3.11--2.3.13, printed pp.93--94 (PDF pages 99--100). These paragraphs explain the resolution input and refer to Bierstone--Milman, but do not prove the generic-initial-ideal theorem. Neither supporting paper was found in the permitted local literature directory. Accordingly this delivery supplies and labels an **agent-written proof**; the step source records explicitly distinguish ILO's context from this proof. No assertion that ILO or a Stacks tag proves generic Borel fixity is made. No unavailable reference is used as an unproved step. An online search found descriptions of the Galligo--Bayer--Stillman theorem; the delivery does not depend on them or attribute the direct argument to them.

The imported node was statement-only, with no previous sandbox attempt. Its statement needs no correction. What was missing was the simultaneous finite open and the actual triangular-invariance argument, rather than a reference to the name of the theorem. Those are now supplied. No Lean was written, no compiler or build tool was run, and no repository or launcher file was changed.

Unfinished work: the supporting-paper comparison remains WANTED. The mathematical split itself is complete. The maintainer's independent content review remains the normal next stage after delivery.

## Searches and reuse

The recorded searches inherited from Q76 were retained. Five new searches were actually run through the required `msearch.py` command and recorded in `searches.jsonl` and the item's `mathlib_searches`:

- LeanFinder: `Generic initial monomial ideal of a homogeneous ideal is fixed by triangular linear changes of variables`.
- Loogle: `"MonomialOrder", "Ideal"`.
- Mathlib grep in `RingTheory`: `Borel.fixed|generic.?[Ii]nitial|Galligo|ginIdeal`.
- LeanSearch: `A homogeneous polynomial ideal has a generic initial ideal invariant under upper triangular matrices`.
- LeanFinder: `Galligo theorem generic coordinates Groebner leading ideal Borel fixed monomial ideal`.

The services all answered. The first semantic search returned homogeneous/irrelevant-ideal APIs; LeanSearch returned homogeneity characterizations; Loogle returned the two s-polynomial membership lemmas. The second semantic phrasing returned leading-term/monomial-span equalities and coefficientwise membership in a monomial ideal. Their displayed signatures contain no generic matrix, open set, or triangular-invariance assertion. They are not matches for the item. The grep returned zero hits. The explicit expansion in proof step 3 supplies the elementary monomial-span observation, so no separate node for it is needed.

DAG statement/title searches for Borel, generic initial, Dickson, Groebner, Grassmann and Pluecker terminology were read. The existing Dickson leaf supplies exactly the finite-antichain and minimal-domination assertions used in step 4. Whole-blueprint searches with `tools/blueprint_refs.py search` for `generic initial`, `initial ideal`, `monomial`, and `echelon` found no equivalent theorem. The eight `monomial` hits concern other constructions and do not state generic Borel fixity. `ancestor` returns `lem-trf-local-term-locality`, retained with its entire existing `via` chain. The proof place and `split_report.blueprint` now identify the historical resolution input, specifically step 2 of `lem-trf-generic-monotone-diagram`.

## Not duplicates

No new nodes are created. In particular the two clauses of this item have not been reintroduced as child nodes, and there is no new Dickson, row-reduction, finite-intersection, or specialization node. The proof gives the elementary coefficient arguments directly.

## Review by Q86

I read the item, its parent `lem-trf-generic-monotone-diagram`, the full statements of all three cited nodes, `dag/chapters/sec-trace-formula.json`, `dag/units/sk-i-curve-zero.json`, and the current main-20261015 proof of `lem-trf-local-term-locality`. The current local-term source uses contracting correspondences; this item is a descendant of the older resolution-input branch. I have split the assigned lower input without editing either the chapter or unit, or replacing their route. The unit key statement is not this generic-coordinate lemma, so its realization fields are not part of this delivery.

For sources I read ILO VIII 2.3.11--2.3.13, especially the explicit Bierstone--Milman reference in 2.3.13. As explained above, it supplies context only. The source record's supporting papers are not locally available, so this is openly an agent proof. There are no new-node source claims to audit. The only non-elementary combinatorial input is the existing Dickson statement: I opened its JSON and checked both clauses, rather than using an assertion hidden in its proof or its Mathlib search results.

Step 1 cites `def-weil-field`, whose statement explicitly says that a nonzero element is invertible, for the zero-variable ideals; and `def-weil-pbc-mv-polynomial-ring`, whose statement explicitly gives finite linear combinations of monomials, monomial multiplication and evaluation. These give precisely the polynomial coefficients and substitutions used. It removes the empty-variable, zero-ideal and unit-ideal cases explicitly. The remaining assumption that the ideal is proper is used only for its degree-zero space. All original cases are restored in the conclusion.

Steps 2 and 3 cite no external theorem: they write the elimination algorithm and show why the smallest surviving pivot is the least monomial. The upward-closure assertion is checked by multiplying a witnessing homogeneous polynomial by one monomial; the coefficient expansion describes the generated monomial ideal. Consequently the equality of degree dimensions used later is proved here, rather than imported as a Hilbert-function theorem. Homogeneity is essential: the witnessing polynomials and their monomial multiples stay in the specified degree.

Step 4 is the non-elementary step and cites `lem-trf-monomial-upper-set-finite-basis`. Its first clause supplies a minimal exponent below every exponent of the set, and its second says that an antichain is finite. Minimal exponents form an antichain by definition. Together these give exactly the displayed finite union of orthants. The rest of that step constructs the generic substitution explicitly by the adjugate inverse; its polynomial degrees stay homogeneous. No normality, Noetherianity, finite-generation or Groebner-basis theorem is assumed. The cited node is already a Mathlib leaf and has no dependency on this item or its parent.

Steps 5 and 6 form a **finite** product of actual nonzero denominators from the finitely many chosen minimal-exponent witnesses. The witnesses are expressed in bases of the original degree spaces, so specialization genuinely lands in the specialized ideal; merely specializing an arbitrary coefficient polynomial would not be enough. The first coefficient remains 1 by a rational identity. Inclusion of monomial ideals then becomes equality in each degree because both finite-dimensional spaces have the same dimension, proved in steps 2--4. This is why no countable intersection of opens or uniform degree bound is being assumed. The same argument works over any extension field and proves the intended geometric interpretation of nonempty open.

Step 7 uses characteristic zero only to ensure an infinite ground field, and writes the induction producing a rational point in the finite denominator open. The root bound is justified by division by a linear factor. For the remaining matrix argument, the nonzero degree space is fixed before its pivot minor is selected; the proof never demands one minor valid for infinitely many degrees.

Step 8 uses the formula `M_S^{-1} M`. Its denominators are regular at the chosen point because that point has exactly the generic pivot set. The zeros before pivots are identities over the rational-function field, so they remain zero on the later parameter curve. This avoids the false inference that a coefficient vanishing at one point vanishes nearby.

Step 9 explicitly checks the direction of the triangular group for **least** lexicographic exponents. The weights decrease with the variable index, and the conjugated transvection is `T_i -> T_i + lambda*t^(w_i-w_j)*T_j`; the exponent is positive for `i<j`. The chosen weights strictly distinguish every degree-q monomial. Thus the parameter curve specializes to the chosen generic matrix, making all the pivot denominators units at t=0. This computation does not silently exchange largest and least initial terms.

Steps 10 and 11 are the complete reduction comparison. Every tail coefficient gains a strictly positive power of t, leaving precisely the pivot monomials in the reduction. Both displayed bases span the same space over L(t), by the written conjugation identity. Their reductions cannot simply be identified without checking integrality of the change of basis: step 11 chooses a minor whose reduction is invertible and computes the change of basis by its adjugate inverse. Its coefficients are therefore regular at zero. Reduction gives the required inclusion, and equality of dimensions gives equality. These are explicit two-matrix computations; no flat-degeneration, properness, Grassmannian, Borel fixed-point, or uniqueness-of-limits theorem is invoked without a node.

Step 12 assembles the independently proved degree equalities for each transvection. The weights may vary with q, which does not alter the single open from step 5. Degree zero and the unit and zero ideals were checked separately. Both the stabilization clause and triangular-invariance clause have therefore been proved, not restated in new nodes.

For delivery-errors B1--B10, there are no new-node forms or Mathlib matches to validate. The item remains self-contained with its inline definitions of homogeneity, least initial ideal and open/nonempty, keeps its two correct definition dependencies, has single TeX escapes, retains the original searches and metadata, and now has filled blueprint provenance. For C1--C8, every non-elementary invocation is the exact existing Dickson statement, quoted in `citations.json`; the rest are the explicit finite coefficient calculations just reviewed. No statement from another unit is used as an undeclared tool. For D1--D5, no content is moved to a child or named theorem, no proof cites its own conclusion, and the two potentially hidden points (simultaneous specialization and equality after reduction) are fully written out. For E1--E7, I checked all degree, field, homogeneity, open and denominator hypotheses where they are used, and found no disputed statement requiring correction.

Small cases checked by direct substitution: n=0; J=0; J equal to the whole ring; n=1 (no required transvections); zero degree spaces; the full degree space; lambda=0; and the two-variable ideal J=(T_1). In the last example a generic generator a*T_1+b*T_2 with b nonzero has least monomial T_2, so B=(T_2), which the required substitution T_1 -> T_1+lambda*T_2 fixes. The opposite triangular direction would fail, so this example checks the sign and indexing in step 9. For J=(T_1^2,T_2^2) in characteristic zero the generic degree-2 pivots are T_2^2 and T_1*T_2, consistent with the same direction. The unit-minor calculation also covers r=dim(P_q); r=0 is explicitly omitted as already invariant.

I corrected no statement, created no nodes, and did not reuse any unrecorded Mathlib search. The main repair relative to the statement-only input was replacing the unavailable named-theorem shortcut with the finite denominator construction and the two regular row bases. No proof step is over 2000 characters; each was still read for a hidden lemma, and the comparisons have their matrix formulas written in the item itself. The initial server-only `review_split` returned PASS with 0 new nodes.

## Validation

Server-side `srvcheck.py ... review_split`: PASS, 0 new nodes. The full `deliver.py Q86 lem-trf-graded-generic-initial-borel --no-push` run exited 0 and printed `OK (not pushed)` with preflight passed (dry-run commit `2bcaafbded1`). This report records that result; the final repeat and the authorized direct push use the same delivery command, whose terminal output gives the definitive delivered commit. No mathematical changes followed the successful dry run.
