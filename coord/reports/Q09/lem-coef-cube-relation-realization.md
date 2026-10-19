## Worker report

The module defines the finite inclusion poset `coefficientFace`, the relation poset
`coefficientRelation`, the cube-face subtype `coefficientCube`, its characteristic
coordinate function, the two canonical order-preserving projection functors, and the
realization proposition. The theorem `CategoryTheory.coefficient_cube_relation_realization`
states that for every `n : ℕ` and `i : Fin (n + 1)` there is a homeomorphism from the
ordinary realization of the nerve of the relation poset to the coordinate subspace
`coefficientCube`, with the barycentric characteristic-vector formula on every simplex.
The proposition also states the continuous one-poset coordinate map, its formula,
coordinate bounds, and that the two projection nerves compose with it to the two
coordinates of the homeomorphism. `Fin (n + 1)` represents exactly `0 ≤ i ≤ n`,
and the strict inequality `i < j` represents the tail `j > i`.

The theorem proof is `sorry`, as required at stage 2. The theorem docstring records the
finite Boolean encoding, quotient compatibility, sorted-coordinate inverse, and
projection argument from the DAG proof.

The dependency declaration used for the enhanced realization convention is
`SSet.Enhanced.coneCategory` from `Sheaf.CategoryTheory.EnhancedDiagramsCones`;
the module also imports the realization normal-form module
`Sheaf.AlgebraicTopology.RealizationCWSubcomplex` for the proof plan. The public
realization characteristic is expanded through `SSet.toTop.map` and `SSet.yonedaEquiv`
so the statement does not introduce a second realization notion.

Edge cases checked: `n = 0` and `i = 0` give the empty independent-coordinate set and
singleton cube; empty lower or tail coordinate ranges are handled by the quantified
conditions; zero barycentric weights are included by the simplex formula; and all
coordinates, including the fixed `i` coordinate, are retained.

Searches made before writing: `msearch.py ... leanfinder` for the characteristic-coordinate
homeomorphism of a finite Boolean relation-poset realization (no exact match; returned
standard-simplex and Cech-nerve declarations); `msearch.py ... loogle` for
`CategoryTheory.nerve, SSet.toTop` and for `OrderComplex, Nerve, geometric realization,
Homeomorph` (no exact match); and `msearch.py ... grep` for realization/nerve/cube and
Boolean-lattice homeomorphism patterns (no exact match in Mathlib). `rg` over
`WeilConjectures` and the project `lean/Sheaf` found no declaration of this node.

## Second reading by Q09

Read the node and its proof clauses again against the module. The `Fin (n + 1)` binder
is the node's `0 ≤ i ≤ n`; `coefficientFace` imposes containment of `i`; the relation
subtype imposes equality of all coordinates with `i < j`; and `coefficientCube` imposes
`p_i=q_i=1`, equal tail coordinates, and unit-interval bounds on every coordinate.
The realization formula sums barycentric weights times the two characteristic vectors.
The final conjunct uses the explicit nerve maps of the two order projections and states
both coordinate equalities. No node statement was corrected and no additional node was
needed. Compilation with `scompile.py` is clean.


## Maintainer second reading correction

Independent immutable review of a21e0d421dab2b3a97258d066764c4bf7a13f8b3 found
an exact existing attachment in the read-only group clone:
`Sheaf.AlgebraicTopology.CubeRelationRealization`, `SSet.CubeRelation.realization`.
Use that declaration with `existing: true` and omit the duplicate delivered module.
This repairs H4 and also avoids the delivered module's H8 documentation omissions,
H9 topic-directory defect. The recorded original signature agrees after whitespace
normalization; no mathematical signature change is required.
The original Worker report and Second reading by Q09 above describe the original
artifact; their no-duplicate claim is superseded by this correction.

The existing `Face` is the inclusion poset of all subsets containing i;
`RelationPoset` imposes equality of membership for every j > i and inherits product
inclusion. `CoordinateSpace` uses unitInterval in both coordinate functions, fixes
both i coordinates to one, and equates the tails. Product and subtype topology give
the required ordinary finite real subspace topology. `realization` quantifies over
all n and i : Fin (n+1), gives a homeomorphism, specifies both real-valued
characteristic formulas for every simplex and parameter, specifies the continuous
face chart by the same formula, and states both realized projection identities.
No hypotheses, conclusion clauses or universe cases change. In particular n=i=0,
i=0, i=n, ties, zero weights and repeated chain vertices are included.

Read HTT Section 2.2.2, printed p.76, PDF page 94, both the cubical quotient before
Remark 2.2.2.6 and the remark. This lemma is correctly described as an agent expansion,
not a verbatim HTT theorem. Read the full statement-dependency node and its recorded
EnhancedDiagramsCones module, the realization normal-form proof-dependency node and
module, Mathlib nerve/nerveMap, SSet.toTop, and SimplexCategory.toTopHomeo and its
naturality. The existing theorem's six-step docstring follows exactly the DAG proof.
The only theorem proof is sorry; all five helpers are real constructions with source
and blueprint docstrings. No new node or dependency repair is required.

Independent rg searches for characteristic homeomorphisms, Boolean lattices,
cubical realization, and the delivered names in project Lean, Mathlib algebraic
topology and upstream WeilConjectures found the exact existing project implementation.
The original module reproduced cleanly through scompile.py (sandbox and library,
1.9 seconds each). The existing replacement attachment was separately checked
through the same per-file wrapper: sandbox and library both clean, 1.5 seconds each.
