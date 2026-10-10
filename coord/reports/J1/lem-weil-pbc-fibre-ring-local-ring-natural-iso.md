# lem-weil-pbc-fibre-ring-local-ring-natural-iso

## Worker report

Split the natural local-ring identification of Stacks Algebra Remark 0H9M into three steps. The existing nodes for the fibre quotient, localization after localization, and localization of a quotient give the result with its formula on fractions. No new node, Lean attachment, or missing source. `review_split.py` passes.

## Review by J1

I read Algebra Remarks 00E6 and 0H9M in `algebra.tex` and compared the statement hypothesis by hypothesis: the prime of the fibre ring contracts to a prime of `B` over `p`, and the desired map sends `b/s` to `j(b)/j(s)`. Step 1 uses the cited fibre localization quotient node to identify `C` with `D/pD`; its displayed contraction calculation proves the required prime lies over `p`. Step 2 uses clause (2) of the cited localization-prime node to identify `B_q` with `D_r`, then the quotient localization node gives a surjection with kernel `pD_r`. The composite has exactly the displayed fraction formula. Step 3 applies the first isomorphism theorem; that last step is elementary. The cited statements provide these maps themselves, not merely existence of unrelated isomorphisms.

I checked A-F of `coord/delivery-errors.md`. No new node or cross-unit tool is present, and the proof makes no unstated finiteness or injectivity assumption on `A→B`. For the edge case where the fibre ring has no primes, the statement is vacuous; when `p=0` in a field, the map specializes to ordinary localization at `q`. The whole-blueprint searches recorded in the node found no equivalent blueprint node; its lineage and split-report place follow B9. No mathematical correction was needed after the worker's split.
