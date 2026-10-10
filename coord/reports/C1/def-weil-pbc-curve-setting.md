# Stage 1 delivery: `def-weil-pbc-curve-setting`

## Files written

- `dag/nodes/sec-curve-estimates/def-weil-pbc-curve-setting.json`: split the existing definition using three existing definition nodes; no new nodes.
- `coord/reports/C1/def-weil-pbc-curve-setting.md`: this worker report.

## Attachments

None. `AlgebraicGeometry.IsCurve` in `WeilConjectures/AlgebraicGeometry/Curve.lean:75-78` states only the geometric condition and is already attached to `def-sc-curves`. It does not state the pair with a torsion abelian sheaf. The search found no Lean declaration for the whole curve coefficient pair.

## WANTED

None for a proof: this item is a definition. The cited master blueprint file `literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd/def-weil-pbc-curve-setting.md` is absent from this checkout, so its exact text could not be reopened. The imported node records its sentence and place (order 1001); the unit record `dag/units/sk-prop-cd.json` and the independent descriptions in `WeilConjectures/AlgebraicGeometry/Curve.lean:13-16` and `Curve/Assertions.lean:14-16` agree with it.

## Source and dependencies

The item defines one pair, not an additional type of curve. Its imported statement requires an algebraically closed field `k`, a separated finite-type `k`-scheme `C` with `dim C <= 1`, and a torsion abelian sheaf `F` on the small etale site of `C`. `def-sc-curves` states exactly the geometric condition and is Lean-closed by `AlgebraicGeometry.IsCurve`. `def-weil-pbc-abelian-etale-sheaves` defines `Ab(C_et)`, and `def-weil-pbc-torsion-etale-sheaf` defines the torsion condition as the isomorphism `colim_n F[n] -> F`. Its equivalent local-section and geometric-stalk forms are stated in `lem-weil-pbc-torsion-sheaf-characterizations`. These three nodes replace the two generic imported dependencies; the defining hypotheses and conclusion are unchanged.

The blueprint search `tools/blueprint_refs.py search 'curve coefficient pair'` found this node and nodes using it, but no second blueprint definition of the same pair, hence `blueprint.same_as = []`. The item is not the key node of `sk-prop-cd`, so its unit's `realized` fields were not changed. The definition has no proof steps or proof dependencies.

## Lean and Mathlib checks

The refreshed audit has `lean_audit.slopmaster2.state = none` for this item. Read-only searches for its id and for curve/coefficient-pair terms in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration for the pair. `Curve.lean:75-78` defines `IsCurve` as separated, locally finite type, quasi-compact and dimension at most one; `Curve/Assertions.lean:14-16,31-35` describes torsion coefficients but its predicates use sheaves of modules and do not define this pair. No attachment was added.

LeanSearch for the curve paired with a torsion etale sheaf returned unrelated `IsProper`, `IsEtale` and sheaf declarations. LeanFinder returned `Scheme.Etale`, `WeierstrassCurve` and other unrelated names. Loogle for `"IsCurve"` returned no Mathlib declaration. A grep of the available Mathlib source under `/home/ubuntu/Poincare-MorganTian/.work/helpers/codex-m47-line/.lake/packages/mathlib/Mathlib` found no curve-coefficient-pair or torsion-sheaf predicate. The component notions already have DAG nodes; there is no Mathlib match for the bundle.

## Boundary cases and corrections

The definition permits the empty scheme (`dim = -infinity`), zero-dimensional schemes, disconnected or nonreduced schemes, and the zero sheaf. It does not add smoothness, properness, connectedness, constructibility, or a fixed torsion exponent. The torsion condition is local; it does not require every group of sections `F(U)` to be torsion. The imported dependency on `def-weil-pbc-scheme-conventions` was too broad, while the imported `def-weil-pbc-etale-sheaves` bundled more notions than this item uses. No mathematical error in the statement was found.

## Verification

`python3 tools/review_split.py def-weil-pbc-curve-setting` passes with zero new nodes. `python3 tools/check_dag.py` reports zero cycles; its seven reach and eleven route warnings name other nodes. No Lean was written or built.

## Review by C1

I compared the revised sentence with the imported blueprint sentence (order 1001) and with the unit record `sk-prop-cd`. The blueprint markdown is unavailable in this clone; the read-only source `AlgebraicGeometry/Curve.lean:75-78` and `Curve/Assertions.lean:14-16` independently confirm the geometric and torsion-coefficient setting. The item has precisely the original hypotheses: algebraically closed `k`, separated finite-type `C/k` of dimension at most one, and torsion `F` in `Ab(C_et)`. It defines the pair and claims no theorem.

I opened the statements of `def-sc-curves`, `def-weil-pbc-abelian-etale-sheaves`, and `def-weil-pbc-torsion-etale-sheaf`. The first permits empty, disconnected and zero-dimensional curves and states the exact geometry; the second defines the small-site abelian-sheaf category; the third defines torsion by the filtered colimit of the subsheaves killed by positive integers. None silently requires a globally bounded exponent. There are no proof steps or new nodes, so B1-B7 and C1-C7 impose no new-node or step checks. The worker searched the blueprint and DAG for an existing pair and the read-only Lean source for an exact declaration; the existing `IsCurve` covers only one component. No cross-unit proof route or cycle was introduced.

I checked the empty curve and zero sheaf as boundary cases: both remain allowed, and the statement does not introduce smoothness or constructibility. The worker's first version already preserved these hypotheses, so I requested no correction. The only available literature text for this definition is the imported blueprint sentence; that limitation is recorded above. The delivery changes only this item and its report, and I checked delivery-errors A-F against those files.
