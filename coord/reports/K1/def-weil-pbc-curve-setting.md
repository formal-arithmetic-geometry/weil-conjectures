## Worker report

`AlgebraicGeometry.CurveCoefficientPair` bundles the curve, its structure morphism over
the field, and a torsion abelian sheaf on its small etale site. It contains no proof
or deferred data.

The node's algebraically closed field `k` is represented by `(k : Type u) [Field k]
[IsAlgClosed k]`. Its curve `C` is `C : Scheme.{u}` with structure morphism
`toSpec : C ⟶ Spec (.of k)`. The separated, finite type, dimension-at-most-one
conditions are exactly `isCurve : IsCurve toSpec`; `IsCurve` includes
`IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, and `topologicalKrullDim C ≤ 1`.
The abelian sheaf `F ∈ Ab(C_Et)` is
`F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}`. Its torsion condition is
`isTorsion : C.IsTorsionAbelianSheaf F`, namely that the canonical colimit map
of the positive-integer torsion subsheaves is an isomorphism.

Dependencies used: `WeilConjectures.AlgebraicGeometry.Curve`,
`AlgebraicGeometry.IsCurve`; `Mathlib.CategoryTheory.Sites.Sheaf`,
`CategoryTheory.Sheaf` (specialized to `C.smallEtaleTopology` and `AddCommGrpCat`);
`Sheaf.AlgebraicGeometry.TorsionEtaleSheaf`,
`AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf`.

Edge cases: the empty scheme, a disconnected curve, and a zero-dimensional curve
are all permitted by `IsCurve`; no smoothness, properness, or connectedness is
imposed. The zero sheaf satisfies the torsion predicate and is permitted. No
characteristic restriction is imposed on `k`.

Searches: `msearch.py leanfinder` for "pair of a curve over an algebraically
closed field and a torsion abelian sheaf on its small etale site" returned
unrelated etale schemes and Weierstrass curves, no pair. `msearch.py loogle`
for `IsCurve, IsTorsionAbelianSheaf` returned no hit. `msearch.py grep` for
`CurveCoefficientPair|curve coefficient pair|IsTorsionAbelianSheaf` in Mathlib
AlgebraicGeometry and CategoryTheory returned no pair. `rg` for those terms in
Mathlib, the project Lean files, and the source repository found only the
separate torsion sheaf definition. `grep -rn def-weil-pbc-curve-setting` in
the source repository and `rg` in `dag/nodes` and `dag/lean_names_upstream.json`
found no preexisting declaration for this pair. The blueprint file named in
the node's source record is absent from this machine's read-only repository;
the node statement and its reviewed split report supply the wording here.

## Earlier second reading (a previous round; superseded)

Preliminary rereading by the statement writer; the independent K1 reader must
replace this paragraph. The field assumptions are `Field k` and `IsAlgClosed k`.
`C` and `toSpec` give the curve over `k`; `isCurve` carries separatedness,
finite type, and dimension at most one. `F` is on `C.smallEtaleTopology` and
`isTorsion` is the required torsion condition. I found no mismatch and made no
mathematical change during this rereading.

## Second reading by K1

The node introduces: (1) an algebraically closed field `k`; (2) a curve `C`
over `k`, meaning a separated finite-type scheme with dimension at most one;
(3) an abelian sheaf `F` in `Ab(C_Et)`; (4) the requirement that `F` is
torsion; and (5) the resulting pair `(C,F)`, called a curve coefficient pair.
The node has no theorem clause or proof obligation.

The Lean rendering is `structure CurveCoefficientPair (k : Type u) [Field k]
[IsAlgClosed k]` in `AlgebraicGeometry.CurveCoefficientPair`. Its fields render
the list exactly: `C : Scheme.{u}` and `toSpec : C ⟶ Spec (.of k)` introduce
the scheme and its map to `k`; `isCurve : IsCurve toSpec` supplies separated,
locally finite type, quasi-compact, and topological Krull dimension at most one;
`F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}` is `Ab(C_Et)`; and
`isTorsion : C.IsTorsionAbelianSheaf F` is the torsion condition. The structure
has no additional fields, hypotheses, or conclusions.

I read the dependency declarations. `AlgebraicGeometry.IsCurve` in
`WeilConjectures.AlgebraicGeometry.Curve` is precisely the curve notion in
`def-sc-curves`; it does not impose smoothness, properness, connectedness, or
nonemptiness. `CategoryTheory.Sheaf` specialized to
`C.smallEtaleTopology` and `AddCommGrpCat` is the recorded Mathlib realization
of `Ab(C_Et)`. `AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf` is the recorded
definition from the torsion dependency and uses the positive-integer torsion
subsheaf colimit map. No dependency was unusable and no private replacement
was introduced.

Edge cases checked: `IsCurve` admits the empty scheme, disconnected schemes,
zero-dimensional schemes, and nonreduced schemes; the structure preserves all
of these. The zero sheaf satisfies the torsion predicate. The field has no
characteristic restriction, there is no integer parameter (hence no `n = 0`
case), and the universe `u` is shared consistently by `k`, `C`, and its site;
the sheaf category is at `u + 1` as required by the dependency declaration.

Searches were repeated with `msearch.py` LeanFinder and Loogle queries for a
curve coefficient pair, and with `rg` over Mathlib, `WeilConjectures/`, and the
project's `lean/Sheaf`; only the separate `IsCurve` and torsion-sheaf notions
were found. No exact declaration exists, so the module is required. The source
blueprint file is absent in this checkout; the node's recorded sentence and
the source `Curve.lean` declaration agree. I found no mismatch and made no
change to the node or module.

Citer checks: `def-weil-pbc-C1` through `def-weil-pbc-C8`,
`def-weil-pbc-eight-curve-assertions`, and the other nodes returned by
`rg -rl '"def-weil-pbc-curve-setting"' dag/nodes` all use the pair only as the
node defines it, so each use holds unchanged.
