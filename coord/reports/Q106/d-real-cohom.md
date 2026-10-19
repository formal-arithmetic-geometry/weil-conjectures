## Worker report

The delivery states `d-real-cohom` in
`Sheaf.Paper.RealSheavesCohomologyEulerSeries` and repairs the recorded
`def-wf-iota-real` interface in `Sheaf.Paper.AdicLocalCharacteristicFactor`.
The source read is the current main-20261015 blueprint,
sec-purity-real-sheaves/sk-d-real-cohom/d-real-cohom.md (order 2947), together
with its unit _section.md (order 2946). The recorded DAG statement retains
those clauses and explicitly names the existing cohomology and Frobenius
nodes. No statement correction or new node is required.

Clause and hypothesis comparison:

- The finite field, algebraic closures, primes p and l with l != p, and the
  unital field embedding iota into C are exactly `RealSheaves.Setup` from
  `Sheaf.Paper.RealSheavesSetup`. Universes u (schemes and base fields) and
  v (the specified coefficient closure) are independent. The real-data
  conversion `Setup.finiteFieldDatum` retains all fields literally; its
  cardinality proof only converts Fintype.card to Nat.card.
- A curve is precisely `(hC : D.IsCurve C₀.left)`. This retains nonemptiness,
  separatedness, smoothness, finite type, pure dimension one and geometric
  connectedness from d-real-setup. In `eulerSeries`, its finite-type and
  separatedness witnesses provide the interfaces needed by the factors;
  these are extracted from hC, not extra assumptions about the curve.
  Bundled `C₀ : Over (Spec (.of D.k₀))` supplies the structure morphism.
- The arbitrary constructible Weil sheaf is
  `sfCommonStageWeilSheaf D.finiteFieldDatum D.l D.l_ne_p C₀ D.Qbar`,
  the recorded full heart-carrier subcategory of the common-stage fixed
  pairs. There is no lissity, reality, purity or properness assumption.
- The ordinary abelian-sheaf convention is the already recorded
  `AlgebraicGeometry.Etale.rightDerivedGlobalSections` and
  `AlgebraicGeometry.Etale.cohomology` in
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: the latter is
  RΓ followed by homology in integer degree i. For a sheaf A, apply this
  functor to `(DerivedCategory.singleFunctor _ 0).obj A`. The former is
  the total right derived global-sections functor computed by injective
  resolutions. The convention is publicly imported and documented,
  rather than given a second definition.
- For a Weil object, ordinary and compact cohomology use the recorded
  `sfCommonStageWeilForget`/`sfWeilForget` before the existing cohomology
  constructions. The public import
  `Sheaf.Paper.CommonStageCompactWeilCohomology` retains
  `WeilConjectures.weilSections`, `weilCohomology`,
  `qbarWeilSections`, `qbarWeilSheafCohomology`, `qbarWeilCohomology`,
  and the finite, integral, rational and common-stage constructions in
  `Sheaf.Paper.OrdinaryCompactCohomology`. The independent-universe
  coefficient-module forms are `adicOrdinaryCohomology` and
  `adicCompactCohomology`. Their RΓ and RΓ_c are the geometric point
  fibres of Ra_* and Ra_!, respectively. Compactifications are
  presentations of proper support, not assumptions that C is proper.
- The adic convention is reused from those same constructions:
  `integralImage`/`integralCompactSections` take the recorded derived
  finite-level inverse limit, `rationalImage`/`rationalCompactSections`
  rationalize the integral objects, and the common-stage constructions
  extend the finite coefficient field. Inverting its uniformizer
  inverts l, since l is a unit times a positive power of the uniformizer.
  No discrete constant-Qbar sheaf is substituted for the adic object.
- Frobenius is the geometric Frobenius in the finite-field datum.
  `WeilConjectures.globalGeometricFrobenius` and
  `globalGeometricFrobeniusOnCohomology`, publicly imported from
  `Sheaf.Paper.GlobalGeometricFrobenius`, are the recorded finite-stage
  ordinary/compact transport followed by the Weil isomorphism and its
  maps on homology. Coefficient extension retains this convention.
- Constant twists reuse `AlgebraicGeometry.WeilSheaf.constantTwist`
  (`WeilConjectures.WeilSheaf.Tensor`): the Weil structure is multiplied
  by b, giving b^e_x at a closed point. The normalization is the
  imported `AlgebraicGeometry.WeilGroup.tateLine` and `constLine`
  (`WeilConjectures.EtaleCohomology.Purity.RealSheaves.Basic`), which
  define Qbar(n) = B_(q^(-n)). These conventions are not redefined.
- Local characteristic factors are the repaired dependency's
  `WeilConjectures.sfLocalCharacteristicFactor`, computed from the
  actual `localClosedFrobeniusCohomology ... 0` and `LinearMap.charpolyRev`
  at a finite Weil stage, then included into the specified closure.
  It is uniquely characterized over all finite-stage presentations and
  compatible geometric points. Multiplicities are retained by the
  determinant, rather than using a set of eigenvalues.
- The product runs over precisely
  `{x : C₀.left // x ∈ closedPoints C₀.left}`. The exponent is the
  recorded `D.closedPointDegree C₀.left x = [κ(x):k₀]`.
  `eulerFactor` maps the polynomial coefficients along `D.iota`,
  substitutes `Polynomial.X ^ e_x`, coerces to `PowerSeries ℂ` and
  takes its formal inverse, in that order.
- `eulerSeries` is the product `∏' x, eulerFactor ... F x` in the
  coefficientwise topology (`PowerSeries.WithPiTopology`). The named
  theorem `eulerSeries_spec` states bounded-degree closed-point
  finiteness; finiteness of the set of factors not congruent to one
  modulo X^(n+1) for every n; `HasProd` of the displayed factors with
  exactly this series as value; and constant coefficient one, the
  condition defining membership in 1+T C[[T]]. Its proof is `sorry`.
  These are the final paragraph and well-definedness clauses of the
  definition, not an analytic convergence claim.

Dependency declarations were read with their signatures and docstrings:
`RealSheaves.Setup`, `Setup.IsCurve`, `Setup.closedPointDegree`;
`WeilConjectures.sfWeilComplex`, `sfCommonStageWeilComplex`,
`sfCommonStageWeilSheaf`, `sfCommonStageWeilForget`, `sfWeilStageObject`
from `Sheaf.Paper.SfWeilSheafComplex`;
the cohomology, Frobenius and twist declarations listed above;
`SfPunctualEigenvalue` in `Sheaf.Paper.AdicPunctualWeights`;
`HasCommonStageLisseLattice` in `Sheaf.Paper.CommonStageLisse`;
and `localPointComplex`, `localClosedPoint`,
`localClosedFrobeniusCohomology` in `Sheaf.Paper.LocalFrobeniusTrace`.
The latter constructs local geometric Frobenius by the residue-degree
iterate, including geometric point reparametrization. The lattice
predicate retains an actual finite locally free completed integral
model and requires no Frobenius-stable lattice.

Edge cases checked mathematically before accepting the drafts: the
zero sheaf has zero-dimensional stalk, determinant 1 and Euler series
1; zero stalks at individual closed points contribute 1. A punctual
constructible sheaf is allowed and contributes its finite local
factors, so a representation-only interface would not suffice. Degree
zero does not occur for closed points over the finite field, and the
coefficient n=0 in the local-finiteness condition asserts the constant
coefficient convention. All integer cohomology degrees and both signs
of Tate twists remain available from the dependencies; n=0 is the
trivial Tate line and the geometric Frobenius eigenvalue of Qbar(1) is
q^(-1). Smooth affine curves remain allowed. The empty scheme is
excluded only by the explicitly recorded chapter curve convention;
the local-factor dependency itself allows it vacuously. The coefficient
embedding needs no continuity or surjectivity.

Searches actually run with msearch.py in this session:

- LeanFinder: "Etale cohomology and Euler series as a formal product of
  local Frobenius characteristic polynomials for constructible Weil
  sheaves" returned eight hits about period rings, etale loci, Witt
  isocrystals and etale presentations; no matching declaration.
- Loogle: "PowerSeries, HasProd" returned four partition/pentagonal
  generating-function products; none uses constructible Weil sheaves.
- Mathlib grep: "eulerSeries|EulerSeries|localCharacteristicFactor"
  returned zero hits.
- LeanSearch: "Local Frobenius characteristic polynomial det one minus
  T times Frobenius on constructible Weil sheaf stalk" returned eight
  hits including Matrix.charpolyRev and LinearMap.charpoly, together
  with Witt-vector Frobenius declarations. These supply linear algebra
  but not the required sheaf/stalk interface.
- Mathlib grep in CategoryTheory/Sites:
  "WeilSheaf|EulerSeries|eulerSeries|localCharacteristicFactor"
  returned zero hits.

Direct rg searches were also made in the complete upstream
WeilConjectures source, dag/lean_names_upstream.json, and the project's
lean/Sheaf for `eulerSeries`, `EulerSeries`, `sfLocalCharacteristicFactor`,
`sfFiniteStageLocalCharacteristicFactor`, `SfIsReal`, and
`Setup.finiteFieldDatum`. None of the proposed declaration names exists.
The upstream `d-real-cohom` search found the sk-d-real-cohom comments in
LFunction.lean. Its source was read in full: the existing
`AlgebraicGeometry.WeilGroup.eulerSeries` at lines 120-121 accepts a
single Weil representation and does not define the product for an
arbitrary constructible object of the recorded common-stage heart.
It therefore is not an exact match for this item. The recorded older
`WeilSheaf.IsReal`, `IsRealizable`, `constantTwist` and `tateLine` were
also opened, not inferred from their names.

All definitions have real data. The only two postponed proofs are
`WeilConjectures.sfLocalCharacteristicFactor_existsUnique` (descent and
well-definedness of the dependency's determinant) and
`RealSheaves.eulerSeries_spec` (the item's local finiteness and unit
constant coefficient). Each has the owning DAG node's blueprint tag
and a complete natural-language argument in its docstring. Neither is
an arbitrary map or a choice of an undetermined stalk operator.
No STATEMENT-DISPUTED issue was found.

Validation: scompile.py compiled both delivered files individually in
dependency order against the private published-library overlay, with
no errors or unexpected warnings. Both auto-implicit options are false;
all universe and variable binders are explicit; all Lean lines are at
most 100 characters. The required deliver2.py dry run is recorded below
once complete.

## Dependency modules

`def-wf-iota-real`: the previous `WeilConjectures.WeilSheaf.Stalk`
record supplies `AlgebraicGeometry.WeilSheaf.IsRealizable` for the older
`AlgebraicGeometry.WeilSheaf k₀ l X` over `PadicAlgCl l`, whereas the
recorded definition of Weil sheaf in this DAG is the actual
`sfCommonStageWeilSheaf` in the rationalized/common-stage adic heart.
The declarations cannot be applied to the latter. The dependency repair
uses that recorded heart, the recorded finite-stage local Frobenius,
and the actual finite locally free completed lattice condition. It
supplies P_x, its unique descent characterization, coefficientwise
reality and realizability as a Weil retract of a real lisse sheaf.
`sfLocalCharacteristicFactor_existsUnique` postpones only the proof
that the explicitly prescribed finite-stage determinants descend;
its uniqueness determines the polynomial used by the definition.
The original node's statement, dependencies, source and all fields
other than lean are unchanged. Its lean.note records the old interface
failure and this replacement. The local factor is defined for the
node's separated finite-type schemes, not merely curves.

Delivery validation: `deliver2.py Q106 d-real-cohom --no-push` printed
`OK (dry run): commit 3f89714290 passes the preflight and compiles; nothing pushed`.
The checked packet consists of the two modules, the item's lean record,
the dependency's lean-only repair and this report. Both modules compiled
in dependency order without unexpected warnings.

## Second reading by Q106

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
