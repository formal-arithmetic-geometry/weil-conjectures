# def-weil-pbc-analytically-unramified

## Worker delivery

File written: `dag/nodes/sec-proper-base-change/def-weil-pbc-analytically-unramified.json` and this report. No new nodes; no Lean attachments; no WANTED source. The Stacks source `algebra.tex` was read from the F2 checkout.

The statement is unchanged and matches Algebra Definition 032X: a Noetherian local ring is analytically unramified when its maximal-adic completion is reduced, and a prime is analytically unramified when the quotient ring has that property. The item already cites the Noetherian ring and adic completion definition nodes; reducedness is defined inline. The existing three Mathlib searches have an absence verdict for the analytically unramified predicate. Whole-blueprint searches for the phrase, the tag, and the completion condition found no matching blueprint node, so `blueprint.same_as` is empty. There is no proof to split for a definition; `status` is now `split`.

Nothing in the node, blueprint, or brief required correction, and no work remains in this item.

## Review by H1

I read Algebra Definition 032X in `algebra.tex` and compared each clause with the unchanged node: a Noetherian local ring, reduced maximal-adic completion, and the same condition on the quotient by a prime. `def-weil-pbc-noetherian-ring` and `def-weil-pbc-adic-completion` provide the only external notions; reducedness is stated inline. There are no proof steps for a definition and no new nodes. The zero ideal in a reduced complete local ring and a quotient by a prime both fit the stated clauses. The recorded blueprint and Mathlib searches support `same_as=[]` and the absence of a direct predicate. I sent nothing back to the worker.
