## Worker report

Q42, prop-every-iterate-trace, stage 1 repair, 2026-10-18. I retained the imported item and repaired the maintainer's returned batch-5 fault. The old route cited the unsplit Qbar trace theorem and used prop-trf-karoubi-independence for E-to-Qbar transport. I replaced that route with the batch-5 categorical assumption and a new explicit coefficient/operator comparison node. The item statement, hypotheses, and conclusions are unchanged.

## Files written

- dag/nodes/sec-zeta-weil/prop-every-iterate-trace.json: repaired seven-step split.
- dag/nodes/sec-zeta-weil/lem-zl-general-condensed-weil-realization.json: one new unsplit comparison statement.
- citations.json: verbatim full statements for every cited node at every proof step.
- searches.jsonl: the four real Mathlib searches for the new node, in addition to the retained item searches.
- report.md: this worker report and review.

## New nodes

- lem-zl-general-condensed-weil-realization, statement, no Mathlib match. It states the missing finite-stage E-to-condensed-Qbar_l realization, compact-support and fixed-stalk comparison, Frobenius intertwining, fixed-point identification, and right-dual consequence. It deliberately asserts no trace identity.

## Attachments

None. The existing declarations were read in the read-only source tree; none is a sorry-free declaration of this item or of the new comparison statement.

## Not duplicates

lem-zl-general-condensed-weil-realization vs lem-zl-assumed-trace-determinant-bridge: the existing node is only the constant E_Y object and explicitly has no global trace comparison; the new node covers arbitrary finite-stage E-Weil complexes and operator intertwiners.

lem-zl-general-condensed-weil-realization vs lem-zl-condensed-global-frobenius-comparison: the existing node is only the constant coefficient unit and geometric-Frobenius comparison; the new node gives the general E-Weil realization needed to invoke the categorical trace assumption.

lem-zl-general-condensed-weil-realization vs lem-zl-condensed-point-supertrace: the existing node compares traces after an object is already realized at the coefficient point; the new node constructs the global/stalk realization and intertwines the geometric operators before any trace conversion.

## WANTED

None. The comparison is recorded as an agent-formulated obligation using the current blueprint and existing coefficient interfaces; no unavailable external source was required for this stage-1 statement.

## Problems found and corrections

The returned fault was valid. Step 3 previously cited prop-trf-karoubi-independence, whose dependency closure contains the trace-formula and Lefschetz–Verdier proof chain. That citation has been removed. Step 2 previously cited the imported, unsplit thm-weil-grothendieck-lefschetz-trace, whose closure reaches the same chain and whose descendants have coefficient hypotheses absent from this item. That citation has also been removed.

The new comparison node is intentionally smaller than the item: it only supplies a condensed realization and operator intertwiners, identifies fixed points, and supplies right duals from finite-dimensionality. The categorical equality itself now comes solely from nt-assume-trace-formula. The categorical-to-alternating conversion now comes solely from lem-zl-condensed-point-supertrace, whose statement explicitly gives the injective E-to-End(Qbar_l_s) scalar map and the signed cohomology trace formula. prop-trf-trace-formal-laws is no longer cited, so its D^b_c(s)[[Qbar_l]] scope issue is removed.

## Review by Q42

I reread the item statement, its main-20261015 proof paragraph, the full returned review, nt-assume-trace-formula, lem-zl-condensed-point-supertrace, lem-zl-assumed-trace-determinant-bridge, lem-zl-condensed-global-frobenius-comparison, lem-zl-point-realization-coefficient-comparison, and the fixed-point theorem. I also reread every statement named in the repaired item's proof and generated citations.json directly from those statement fields.

1. Step 1 uses lem-weil-point-counts-finite for finiteness of Y_0(F_{q^n}), prop-cohomological-finiteness for bounded finite-dimensional global E-cohomology and Frobenius, and def-weil-local-frobenius-trace for bounded finite-dimensional stalk cohomology and the exact local alternating trace. Their hypotheses are the separated finite-type datum and the stated E-Weil complex. This establishes all finite-sum and trace-existence claims.

2. Step 2 uses lem-zl-general-condensed-weil-realization for the actual bounded constructible condensed Weil object, compact-support and fixed-stalk comparison maps, operator intertwining, fixed-point identification, and right-dual consequence. Those are precisely the facts the old route lacked. Step 1 supplies finiteness of the fixed-point index set and finite-dimensionality. Applying nt-assume-trace-formula therefore meets its separatedness, finite fixed-point, Weil-object, and dualizability hypotheses. The assumption is used only for its categorical trace equality; its stated exclusion of alternating cohomology traces is respected.

3. Step 3 uses the same comparison node for operator intertwining and lem-zl-condensed-point-supertrace for right duals, the categorical trace computation, the alternating cohomology formula, and injectivity of the scalar map. Thus both sides of the categorical equality are images of exactly the displayed E-valued sums. Injectivity descends the equality to E. No Karoubi representative-independence theorem or trace-formula descendant is used.

4. Step 4 is elementary finite-sum subtraction and injectivity: changing one geometric-point choice while fixing all other choices cancels the common summands. The empty index set is handled separately.

5. Step 5 uses the displayed definitions of the canonical constant Weil structure, point transport, local trace, endomorphism trace, and point-count convention. Following a constant section gives the identity at every finite level, after completion, and after rationalization; the one-dimensional trace is one.

6. Step 6 uses the Frobenius-equivariant proper comparison in prop-cohomological-finiteness and basis-independent trace from def-weil-endomorphism-trace. Induction gives the intertwining for every power, so compact and ordinary cohomology traces agree.

7. Step 7 uses the smooth/proper/geometrically connected/pure-dimension clause of prop-cohomological-finiteness for vanishing outside [0,2d], def-weil-endomorphism-trace for zero-space traces, and def-weil-smooth-proper-cohomological-family for the notation V_{i,ell}, F_{i,ell}. The d=0 case is included.

Small cases checked: empty Y_0, a point with arbitrary finite-dimensional invertible Frobenius, A^1 and P^1 point counts, the constant rank-one stalk, a shifted complex, E=Q_l, and d=0. The new node is not a restatement of the item and contains no trace identity. All repaired proof steps are under 2000 characters. No SGA 4 source is cited. The retained route repair for the Euler-product node is untouched.

The server preflight also required two format repairs: I added bracketed node citations for every project notion in the new comparison statement, and normalized its TeX commands to single backslashes in the JSON-rendered statement. The proof’s scalar inclusion is written with `\to`; citations.json was regenerated after both changes.

## Unfinished work

No part of the repaired stage-1 split remains unfinished. The required server dry run and delivery are the next operations.
