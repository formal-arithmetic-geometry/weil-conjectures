# Stage 1 delivery: `lem-weil-pbc-integral-scheme-ideal-generic-stalk`

## Worker report

Split the item in four steps using the existing affine generic-point and quasi-coherent ideal nodes. No new nodes or Lean attachments. I read the third paragraph of the proof of Stacks 01YL in `coherent.tex`, where the nonzero ideal and proper-support consequences are used without proof. The supplied affine-local proof is marked agent-written. The item's statement is unchanged.

The full-blueprint searches for `generic stalk ideal integral scheme`, `generic point`, and `01YL` found no blueprint node with this statement; `blueprint.same_as` is empty. The split traces to the essential-surjectivity paragraph of `thm-weil-pbc-finite-etale-lifting` through the item's existing `blueprint.from.via` chain.

`tools/review_split.py` passes after setting `blueprint.same_as` to `[]`. `tools/check_dag.py` cannot complete in this checkout: it raises `KeyError: 'lem-weil-pbc-grothendieck-regular-sequence-flat'` while reading unrelated unit reachability. No files for that node were edited.

## Review by H1

I read the third paragraph of Stacks Cohomology of Schemes 01YL in `coherent.tex` and compared the unchanged item statement with the nonzero ideal and generic-support facts used there. The source leaves this affine calculation implicit, so the agent proof is correctly labelled. I checked the statements of `lem-weil-pbc-affine-open-spec-points`, `lem-weil-pbc-spec-domain-stalks-function-field`, and `lem-weil-pbc-quasi-coherent-ideal-zero-set-affine`: they supply respectively the affine chart, the zero-prime function field, and the equivalence between a full ideal stalk and an affine ideal not contained in the prime. Steps 1 and 2 use exactly those clauses; step 3 is the sheaf-germ argument and step 4 is the two-ideals calculation in a field. A nonzero ideal on an affine domain and the zero ideal test both directions, including the properness condition in the source. No new node was made; I checked the recorded whole-blueprint searches and `same_as=[]`. I sent nothing back to the worker. The reported `check_dag.py` KeyError came from the concurrent write of a different item; the isolated delivery is checked again before push.
