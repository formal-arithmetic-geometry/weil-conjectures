# def-sc-divisor

## Files written

- `dag/nodes/sec-abelian-varieties/def-sc-divisor.json`: split definition. Its data now cites the curve, function field, DVR, constant-sheaf and finite-support nodes. The item remains outside Mathlib.
- `dag/nodes/sec-abelian-varieties/lem-sc-divisor-finite-support.json`: new unsplit statement. Its exact Lean theorem is reported below for L to verify and attach; `lean_audit.slopmaster2.state` remains `none`. No Mathlib match after LeanSearch, Loogle and source search.

## Attachments

- `AlgebraicGeometry.Scheme.finite_setOf_ord_ne_zero` belongs to `lem-sc-divisor-finite-support`: `WeilConjectures/AlgebraicGeometry/Curve/Divisor.lean:103-144`, no sorry in its source or dependencies according to `local/sorry_map_slopmaster2_71d63dcf.jsonl.gz`. L must verify and attach it. Its hypothesis is `IsIntegral X` and `IsNoetherian X`; its conclusion is the finite set `{x : X | X.ord f x != 0}` for `f != 0`. The new node spells out `IsNoetherian X` as a finite affine Noetherian cover and `X.ord` as the local length-difference order in codimension one, zero elsewhere.
- The following five sorry-free declarations cover **parts** of `def-sc-divisor`, not its whole statement: `AlgebraicGeometry.Scheme.Divisor` (lines 51-56), `AlgebraicGeometry.Scheme.Divisor.degree` (58-63), `AlgebraicGeometry.Scheme.div` (153-170), `AlgebraicGeometry.Scheme.principalDivisors` (178-182), and `AlgebraicGeometry.Scheme.DivisorClassGroup` (185-189), all in the same source file. The module `O_C(D)` defined as a subsheaf of the function field is explicitly unavailable in `WeilConjectures/AlgebraicGeometry/Curve/Picard.lean:53-56`. Thus there is no exact closed attachment for the full item.

## Missing Source

WANTED: restore `literature/blueprint/master/blueprint/sec-abelian-varieties/sk-def-av-pic/def-sc-divisor.md` (and its unit/chapter files) in the local literature checkout for `def-sc-divisor`. Only the imported DAG statement is present here; no literature tree was regenerated in this worker worktree. The exact finite-support statement and its Lean proof were read directly from the read-only slopmaster2 source.

## Statement Corrections

- The imported statement allowed an arbitrary connected curve while using DVR valuations at every closed point. A singular connected curve, such as a nodal plane cubic, need not have DVR local rings. The revised statement uses a smooth connected curve over algebraically closed `k`, the domain in which the cited regularity and DVR nodes apply; disconnected smooth curves are handled componentwise.
- The imported formula for `O_C(D)(U)` applied `div` to `f=0`, where `div(0)` is undefined. The revised formula includes zero separately and applies valuations only to nonzero rational functions.
- On the empty open, the imported formula gave all of `k(C)`, whereas a sheaf of modules has the zero module there. The formula now applies to nonempty opens and states the empty case separately.
- The imported node omitted the constant-sheaf dependency and a finite-support justification for its divisor sum; both are now cited. I found no exact duplicate of the finite-support theorem in the DAG or whole blueprint index. `ClassGroup` in Mathlib concerns fractional ideals of a ring, and `MeromorphicOn.divisor` concerns analytic functions, so neither is this definition.

## Verification

- `python3 tools/review_split.py def-sc-divisor`: PASS.
- `python3 tools/check_dag.py`: 0 cycles; 7 reach and 11 route errors outside this item, involving proper-base-change constructibility nodes already present in the worktree.
- `git diff --check`: PASS.
- `proof_origin` is `null` on the split definition and on the new unsplit statement, which has no proof steps pending L's attachment.

## Review by F1

I compared the imported definition with the public `def-sc-curves`, `def-sc-function-field`, `lem-sc-smooth-regular`, and `lem-sc-regular-dim1-dvr` statements and read `WeilConjectures/AlgebraicGeometry/Curve/Divisor.lean:46-189` and `Curve/Picard.lean:53-56` in slopmaster2. The original arbitrary connected-curve formula used a DVR valuation without a smoothness assumption: a singular closed point need not have a DVR local ring. The new smooth connected hypothesis is needed for the displayed valuation construction and is within the smooth-curve setting that `def-sc-curves` assigns to the Picard category. The imported definition also applied `div` to zero and assigned the constant field to the empty open; the separate zero and empty-open cases now give the intended submodule sheaf. This is a correction of an ill-defined imported definition, not a theorem shortcut. The blueprint markdown itself is missing locally, as the worker's WANTED entry says, so L must compare the corrected wording with that source when merging.

I checked each clause against the available Lean source: `Scheme.Divisor` is the free abelian group on closed points, `Divisor.degree` sums coefficients, `div` is the homomorphism from nonzero rational functions, `principalDivisors` is its range, and `DivisorClassGroup` is the quotient. Those five sorry-free definitions cover only these clauses; `Picard.lean:53-56` explicitly notes the missing associated subsheaf construction, so I rejected an attachment of the full item. The `O_C(D)` nonempty-open sections use the normalized valuations supplied by the two cited regularity/DVR nodes, with zero adjoined; the empty-open section is the zero module. Testing `D=0`, `f=1`, `f=0`, the empty open, and a nodal curve exposes exactly the corrected boundary cases.

For the new finite-support node I checked B1-B7 and E1-E6 against `Curve/Divisor.lean:103-144`. It is an unsplit, self-contained input strictly smaller than the definition, with integral scheme cited through `def-pc-integral-scheme`, Noetherianity stated by a finite affine Noetherian cover, and order at codimension one spelled out. Pinned Mathlib `AlgebraicGeometry/OrderOfVanishing.lean:52-61` defines zero order off codimension one, while `RingTheory/OrderOfVanishing/Basic.lean:36,324` gives the length/field-fraction construction used in its wording. The Lean theorem has the same Noetherian integral hypotheses and finite-set conclusion and its displayed proof has no sorry. I sent the first draft back under B3/B10 because the terms were not defined and it marked its own Lean audit closed; the worker repaired the statement and reset audit to `none`. The exact declaration/file/line remains in the attachment report for L's sorry-map check. DAG/blueprint searches found no existing duplicate, and no proof or off-route tool was introduced. The one-item shape, blueprint provenance, no-cycle result and `review_split.py` were checked under A-F.

