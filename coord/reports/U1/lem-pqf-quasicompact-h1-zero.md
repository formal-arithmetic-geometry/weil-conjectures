## Worker report

The module states `AlgebraicGeometry.quasiCompact_affine_of_h1_ideal_zero`.
The scheme is `X : Scheme.{u}`; quasi-compactness is the explicit
`[QuasiCompact (𝟙 X)]` hypothesis. A quasi-coherent ideal sheaf is represented
by `I : X.IdealSheafData` with `I.toModules.IsQuasicoherent`; its vanishing
`H^1` clause is `Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace
1).obj I.toModules)`. The conclusion is `IsAffine X`.

Dependencies used: `def-pc-scheme` via Mathlib `AlgebraicGeometry.Scheme`;
`pqf-def-coherent` via `Sheaf.AlgebraicGeometry.Coherent` conventions and
Mathlib `SheafOfModules.IsQuasicoherent`; `pqf-def-cohomology` via
`Sheaf.Paper.PQFCohomology`, declaration
`AlgebraicGeometry.sheafCohomologyAndHigherDirectImages` and the recorded
`RingedSpace.moduleCohomology`.

Edge cases checked: the universe `u` is shared by the scheme, ideal sheaf and
cohomology object; `p = 1` is explicit; the zero cohomology object is covered
by `Subsingleton`; the empty and affine schemes are not excluded by the
binders. The module compiles with only the expected `sorry` warning.

Searches: `msearch.py leanfinder` for Serre quasi-compact H1 criterion (no
match); `msearch.py loogle` for `IsAffine`, cohomology and quasi-compactness
(no match); grep of Mathlib AlgebraicGeometry and project `WeilConjectures`
for Serre/H1 criterion (no match). Existing declarations inspected as above.

## Earlier second reading (a previous round; superseded)

Independent rereading confirms that the Lean binders match the node: `X` is a
scheme, `[QuasiCompact (𝟙 X)]` is quasi-compactness, `I : X.IdealSheafData`
with `I.toModules.IsQuasicoherent` is a quasi-coherent ideal, and the explicit
`Subsingleton` condition is H¹ vanishing. The conclusion is exactly `IsAffine
X`; no hypothesis or conclusion was changed.

## Second reading by U1

The node introduces a scheme `X`, assumes quasi-compactness, assumes
`H^1(X, I)=0` for every quasi-coherent sheaf of ideals `I ⊆ O_X`, and concludes
`IsAffine X`.  The Lean renders these items as follows:

- `X : Scheme.{u}` is the scheme object from `AlgebraicGeometry.Scheme`.
- `[QuasiCompact (𝟙 X)]` is the quasi-compactness hypothesis on the identity.
- `I : X.IdealSheafData` is Mathlib's bundled ideal sheaf datum, and
  `I.toModules.IsQuasicoherent` restricts it to quasi-coherent ideal sheaves.
- `Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
  I.toModules)` expresses vanishing of the degree-one cohomology object.
- `IsAffine X` is exactly the node's conclusion.

The quantifier order and implication are unchanged, and no additional
finiteness, separation, characteristic, or universe assumptions occur.  The
shared universe `u` covers the scheme, ideal sheaf, and cohomology object;
degree one is explicit.  Empty schemes, affine schemes, zero ideal sheaves,
and a zero H¹ object remain permitted by the binders and `Subsingleton` clause.

I read the dependency records and declarations: `AlgebraicGeometry.Scheme`;
`Sheaf.AlgebraicGeometry.Coherent`'s recorded quasi-coherence convention; and
`Sheaf.Paper.PQFCohomology`, whose recorded cohomology is
`RingedSpace.moduleCohomology`.  Searches were repeated with
`msearch.py leanfinder` (Serre/quasi-compact/H¹ criterion),
`msearch.py loogle` (IsAffine, cohomology, quasi-compactness), and `rg` over
Mathlib, `WeilConjectures`, and `lean/Sheaf`; none found an existing equivalent
statement.  The source place is Stacks Tag 01XF, lines 283--388, and the
expanded declaration docstring records all five proof steps and their proof
nodes.

No semantic mismatch was found, so the theorem statement and node statement
were left unchanged.  The only change was expanding the declaration docstring
with the source, blueprint, and step-by-step proof required by stage 2.
