# Stage-1 report: lem-coef-relative-join-fixed-source-prism

## Files written

- `dag/nodes/sec-six-functors/lem-coef-relative-join-fixed-source-prism.json`: existing statement node split into four direct degreewise proof steps; no new nodes; no Mathlib match.
- `citations.json`: eight verbatim citations, one for each definition used by each proof step.
- `report.md`: this report.

## Attachments

None. I searched both named `WeilConjectures/` trees for the item id, its blueprint tag, and the fixed-source relative-join terminology. No sorry-free project declaration states this item. The existing node supplied by Q09 is statement-only and is the item being split here.

## WANTED

WANTED: an archived copy of Lurie, *Higher Topos Theory*, Lemma 5.4.4.2 (printed pp. 432–433), specifically the second specialization on printed p. 433, for the fixed-source prism construction. The source is available online at `https://people.math.harvard.edu/~lurie/papers/HTT.pdf` but is not archived under `literature/`; the proof below is written directly from the explicit degreewise simplicial formulas and the current relative-join definition. No Stacks or SGA source is relevant, and no SGA source is used.

## Findings and corrections

The item already existed in the shared DAG as an unsplit statement-only node added by Q09, so I copied that current statement into the isolated Q138 sandbox and changed only its proof fields, `proof_origin`, `status`, and `split_report`. The statement, hypotheses, exact endpoint restrictions, statement dependencies, source, and blueprint ancestry are unchanged. No new node was warranted: the construction is a direct degreewise calculation from the existing definitions of products/pullbacks, joins, and relative joins.

The required Mathlib searches were run with `msearch.py Q138 lem-coef-relative-join-fixed-source-prism`: LeanFinder, Loogle, grep in `AlgebraicTopology`, and LeanSearch. LeanFinder and LeanSearch returned only pointed-simplex, horn, and model-category cylinder declarations; Loogle returned no hits; grep returned ordinary cylinder/path-object declarations but no relative simplicial join. None is an exact statement or a one-line specialization, so no Mathlib leaf is claimed. The raw search records are in `searches.jsonl` in this sandbox.

No statement dispute, duplicate node, hidden quasicategory hypothesis, fibration hypothesis, filteredness hypothesis, or colimit hypothesis was introduced. The proof uses only the degreewise formulas. In the J construction, the pointwise minimum `epsilon = delta wedge t` makes the zero block consist of the cylinder part followed by a possible `p` tail; the quotient relation at `t = 0` makes that tail canonical. This is the only compatibility detail beyond the displayed join formulas.

## Review by Q138

I read the current item node and the parent proof step that invokes it (step 8 of `lem-coef-filtered-cocartesian-section-cofinality`). I then read the full statements of `def-cbc-enhanced-diagrams-cones` and `def-coef-infinity-relative-join`. The first says that products and pullbacks are formed degreewise with operators acting coordinatewise; the second gives the relative-join simplex pair, its simplicial operator, and the pure-factor inclusions. The item’s third statement dependency, `def-coef-infinity-relative-cone`, is part of the imported vocabulary but is not needed by this direct proof.

Step 1 uses the degreewise product/pullback statement and the relative-join simplex-pair formula. For a cone simplex with parameter `delta`, it labels the initial relative-join block by `j(z, sigma|I)` and the final block by `sigma|I^c`; the two structure maps agree because `a` is projection on `Z times X` and the second relative-join map is the identity on `X`. I checked pure `Z`, mixed, and apex blocks separately, including the formal empty block.

Step 2 uses the same two statements. For a pair `(u,t)`, it sets `epsilon = delta wedge t`, labels the zero block by `k c(z,t)` and a degenerate last-vertex extension on any `delta = 1, t = 0` tail, and labels the one block by the constant simplex at `x`. The map from all of `C_Z` is constant at `x`, so the relative-join pullback equation holds. I checked that the quotient `c(Z times {0}) = p` makes the tail constant and that the construction respects every ordinal operator.

Step 3 uses the relative-join operator and inclusion formulas. At `t = 0`, all labels collapse to `k(p)`, giving the initial restriction. At `t = 1`, `epsilon = delta`, the cylinder endpoint is `c_1` and the final block is `x`, giving exactly `P(-,x)`. On the pure `Z` subobject the formula is `k c`, and on the apex it is the relative-join edge from `k(p)` to `x`. These are the four exact restrictions in the item statement, not merely vertex-level equalities.

Step 4 checks the edge case `Z` empty directly: both pushouts reduce to a point, `P` is the final-factor inclusion, and `J` is the unique relative-join edge. I also checked a one-point `Z`, a pure cylinder simplex, a mixed cone simplex, and degenerate interval parameters. No step relies on an unproved existence theorem or on a property absent from a cited definition. The four proof steps are elementary blockwise constructions; none exceeds 2000 characters.

## Not duplicates

No new node was created, so there are no new-node duplicate pairs. The item itself is distinct from `lem-coef-relative-join-prism-comparison`, which gives an inner-anodyne filtration for ordinary joins and does not construct the fixed-source cylinder prism with these endpoint restrictions.

## Unfinished work

Nothing remains for this one-level split apart from the required server dry run and delivery. No Lean file, compiler, Lake/build tool, live project file, or launcher file was written or run.
