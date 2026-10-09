# Stage 1 report: `def-weil-pbc-conormal-sheaf-formally-unramified`

## Files written

- `dag/nodes/sec-proper-base-change/def-weil-pbc-conormal-sheaf-formally-unramified.json`: split the definition into four well-definedness steps.
- `coord/reports/G1/def-weil-pbc-conormal-sheaf-formally-unramified.md`: this report.

## Sources and dependencies

The definition follows More on Morphisms Definition 04F4, item (2), with its
universal-thickening input from Lemma 04F3 and Section 04F2. The ideal sheaf
and square-zero quotient use Tags 01R2 and 04EX; the pullback module is the
existing public node `def-pc-module-pullback` (Stacks Tag 0095). No new child
node was introduced, and no proof lemma is private to this definition.

## Review by G1

I checked that the statement introduces the universal thickening, its closed
immersion, ideal sheaf, square-zero condition, and module pullback exactly as
04F4. Step 1 cites the existing 04F3 existence and uniqueness node. Step 2
uses the first-order condition to identify `I/I^2` with `I`. Step 3 applies
the existing module-pullback definition to obtain the conormal O_Z-module.
Step 4 transports the ideal and quotient along the unique compatible
isomorphism of universal thickenings, establishing canonical independence.
All proof dependencies are existing DAG nodes, and the definition retains
unit `sk-thm-p1` and its exact Stacks source tags. No Lean was written or
compiled.

Validation is recorded by `review_split.py`, `check_dag.py --cycles`, and
`git diff --check`; repository reachability warnings are pre-existing.

## Incomplete work

The referenced universal-thickening existence lemma remains unsplit for a
later Stage 1 worker.
