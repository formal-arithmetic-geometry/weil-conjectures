1. Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-henselian-pair-prime-connected.json`: split into three proof steps; no new nodes.

2. Attachments

None.

3. WANTED

None. The Stacks source is available as `literature/stacks-project/more-algebra.tex` on the project server; the proof was checked at Lemma 15.11.16 (Tag 09Y6).

4. What was wrong or incomplete

The imported node had an empty proof and was unsplit. The source's phrase "Thus it suffices" hides the quotient-spectrum identification, and the use of the affine connectedness criterion requires showing that the quotient ring is nonzero. These are now explicit: the quotient by the prime is integral and henselian, its spectrum identifies with the stated closed subset, and the zero-quotient case contradicts unique idempotent lifting. The remaining idempotent argument follows the source and uses only existing nodes. No statement or blueprint text was changed.

5. What could not be finished

No Lean writing, compilation, or module attachment was performed, as required for Stage 1. `python3 tools/review_split.py lem-weil-pbc-henselian-pair-prime-connected` passes. `check_dag.py` reports unrelated pre-existing warnings for other nodes, but no issue involving this item.

## Review by C1

I independently read the server copy of `more-algebra.tex` around lines 2948--2970 and checked the cited DAG statements. Step 1 correctly applies the existing integral-over-henselian-pair statement to $A\to A/\mathfrak p$ and uses the existing quotient closed-immersion leaf plus affine-spectrum definition to identify the subspace. Step 2 correctly handles the nonzero-ring side condition: for $I=A$, the idempotent of the zero quotient has distinct lifts $0$ and $1$ in the nonzero domain. Step 3 correctly turns a proper nonempty clopen from a disconnection into a nontrivial idempotent, lifts it by the defining henselian condition for the finite algebra $A$, and contradicts the domain equation $e(e-1)=0$. The cited nodes are present and unmerged, every step is represented in `proof_deps`, and the item already records LeanSearch, Loogle, and Mathlib-source searches with no match. The proof remains on the Stacks 09Y6 route, and no reusable helper statement was hidden or needed. Review result: pass.
