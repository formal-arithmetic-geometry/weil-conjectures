# Delivery report: lem-weil-pbc-descend-separated

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-descend-separated.json`: repaired the Stage 1 split proof.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-diagonal-immersion.json`: added the unsplit public 01KJ prerequisite node.

## Repair performed

- The stage-0 diagonal is written as `X_0 -> X_0 x_{Y_0} X_0`.
- Step 1 explicitly uses `lem-weil-pbc-immersion-base-change-lft` clause (2) for the locally-finite-type hypothesis of Stacks 01ZP.
- Step 1 derives quasi-compactness and quasi-separatedness of `X_0 x_{Y_0} X_0` through clauses (1)--(3) of `lem-weil-pbc-qcqs-morphism-permanence`.
- Step 2 records the canonical identifications `(X_0 x_{Y_0} X_0) x_{S_0} S_i` with `X_i x_{Y_i} X_i`, and with `X x_Y X` over `S`, compatibly with diagonals.
- Step 1 cites the new public `lem-weil-pbc-diagonal-immersion` node, whose statement is exactly Schemes Lemma Tag 01KJ.

## Sources and checks

The proof follows Limits Lemma Tag 01ZQ at line 1851, applying 01ZP to the diagonal; the immersion and qcqs prerequisites are cited by public DAG nodes. No private module was introduced. The lead should perform the final source review and run the repository DAG checks before accepting this repair.

## Review by E1

I checked each returned point against Limits Lemma 01ZQ. The repair now uses the correct diagonal target $X_0\\times_{Y_0}X_0$, explicitly identifies its base changes with $X_i\\times_{Y_i}X_i$ and $X\\times_YX$, and states compatibility with the diagonals. It cites the locally-finite-type clause of the public immersion node and derives qcqs of the fibre product through the public qcqs-morphism-permanence clauses. The two proof steps therefore address every requested correction, retain the exact 01ZQ source, and introduce no private module or new node; `status: split` and `split_report` are present.
