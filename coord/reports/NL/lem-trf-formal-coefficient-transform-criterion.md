## Worker report

The module `Sheaf.AlgebraicGeometry.FormalCoefficientTransformCriterion` states
`lem-trf-formal-coefficient-transform-criterion` in nine theorem declarations. All nine
proofs are `sorry`. Ten auxiliary definitions/structures specify the constructions in this
same statement; none chooses data from a postponed existence theorem. No node statement,
proof, or proof dependency changed. The returned H2 ownership defect is repaired by a new
definition node recording the existing transverse-coefficient operator.

### Sources read

Read ILO VIII 2.3.11--2.3.13, printed pp.93--94, from the local PDF. This passage specifies
the characteristic-zero embedded resolution input and its smooth functoriality adjustment.
For the actual local assertions read BM, Invent. Math. 128 (1997), Theorems 7.20--7.21,
printed pp.268--269, and Theorem 9.4, Remarks 9.5 and its proof, printed pp.277--278.
The published BM PDF was fetched into the item's scratchpad from
https://mahalex.net/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf .
It explicitly distinguishes saturated permissible transforms, exceptional-intersection total
transforms, and the line operation. The proof in the node was read in full (steps 1--14).

### Hypotheses and clause mapping

All names below are in `AlgebraicGeometry.HilbertCoefficient` unless qualified.

- Characteristic-zero field: `[Field k] [CharZero k]` on geometric declarations and
  `[Field L] [CharZero L]` on formal declarations. Field extensions have their own universe
  `v` in `coefficient_field_extension`; all geometric schemes and their ground field use
  `u`. Variables, numbers and universes are explicitly bound (`autoImplicit false`).
- Closed finite-type X in smooth M: `[IsClosedImmersion i] [Smooth p]` and
  `[LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)]`. The item does not assume
  reducedness, and none is added. The existence dependency assumes reducedness only to
  construct data; the criterion takes existing data directly and also handles nonreduced X.
- Distinguished point and Taylor ideal: `(a : X)` and
  `D : RegularHilbertCoefficientDatum p i a m n s α Q`. Its existing fields `straight`,
  `taylorU`, `taylorN`, `f`, `coeff`, `expansion`, `center`, and `b0` provide the actual
  regular model and Taylor ideal, rather than any unconstrained ring maps.
- Vertices, orders and all five conditions: `orderedVertices α`,
  `formalConditions α pick β Q K f`, `hpick`, `hprefix`; regular data uses its corresponding
  recorded fields. Orders are `(α l).degree`. The finite derivative cutoff is bound by
  `hQ : ∀ l, (α l).degree - 1 ≤ Q`, the bound in BM 9.4(iii).
- Extended H: existing `extendedHilbert K` is quotient module length over the formal ring;
  over a field it equals the finite vector-space dimension in the node. Regular statements
  use `HilbertSamuel.function`, with its transcendence-degree summation at nonclosed
  points. The jet-control interface identifies these extended conventions. We never replace
  this function by the unnormalized local Hilbert function.
- Local equality locus: `coefficient_equality_germ` produces an open `V` containing
  `D.center`. At every ambient `y ∈ V`, existence of a point of the actual embedded
  pullback X with the retained level is equivalent to `y ∈ D.j '' D.orderLocus`.
  `orderLocus` is precisely the regular maximal-ideal-power test for every l and γ of
  degree below d_l. Its image under `D.j` implements Z=0. The assertion is set equality
  in a neighborhood, not equality of nonreduced subschemes.
- Smooth coordinate center contained in this germ: regular
  `coefficient_regular_permissible` takes the ideal `J` on N,
  `[Smooth (J.subschemeι ≫ D.j ≫ D.e ≫ p)]`, and
  `hC : J.support ⊆ D.orderLocus`. Locally every such smooth closed flag has the coordinate
  description in the source. The ambient center is its actual image `J.map D.j`.
  Formal `coefficient_permissible_chart` uses `Y : Finset (Fin m)` and
  `coefficientCenterVariables Y = Y ⊔ {all Z}`; `hC` is exactly coefficient membership in
  `(Y)^(d_l-|γ|)`, which the source derives from the smooth regular center condition.
- Blowup and scheme-theoretic strict transform: regular statements use
  `(J.map D.j).blowup`, `.blowupMap`, and existing `strictTransformMap` /
  `strictTransformToSource` over the complement of the center support. Formal
  `coefficientStrictTransform` is contraction of the extended total ideal from
  `Localization.Away (X h)`, hence saturation by every exceptional power. Its generation
  by the individually divided f_l is an explicit conjunct of the formal theorem.
- Every exceptional point: `coefficient_regular_permissible` quantifies over all points
  `x'` of the actual strict transform lying over `D.center`. It concludes
  `HilbertSamuel.le` and the exact equality iff below. The formal theorem gives the
  stronger coordinatewise jet inequality, as node proof steps 7 and 11 establish.
- Equality iff on N' and the coefficient bounds: regular iff explicitly produces
  `b'` on `(J.map D.j).strictTransform D.j` over the same ambient point, a principal
  exceptional germ e, and the divided coefficient germs in maximal-ideal powers.
  Formal iff requires a tangent denominator and zero transverse direction components,
  exactly membership in N'; its remaining inequalities use `coefficientWeightedTransform`.
- Regularity of quotients: the first conjunct of the regular permissible theorem is
  `∃! c'` solving `e^(d_l-|γ|)*c' = sigma*c_lγ` at every point of N', for every local
  exceptional generator. No division in a fraction field or arbitrary map is assumed.
  Formal exact divisibility is stated for every f_l and every low-order coefficient.
- Same five conditions, same diagram at equality: formal implication returns
  `formalConditions α pick β Q` on the saturated ideal and the explicit transformed f_l.
  Regular implication returns `Nonempty (RegularCoefficientTransform D J x')`, whose
  datum has the same m,n,s,α,Q. Its coefficient scheme is cartesianly the actual N',
  `principal` identifies the exceptional ideal, and `coefficients` is the weighted
  division formula for all γ. For |γ|≥d_l the formula is multiplication by a nonnegative
  power; for smaller degree it is the exact quotient identity. The defining regular
  coefficient-datum expansion determines the transformed series from these coefficients.
- Boundary intersection transverse to N: `coefficient_boundary_chart` uses two distinct
  W indices, leaves Z fixed, uses `coefficientTotalTransform`, returns unchanged H,
  `formalConditions` with α, and the ordinary coefficient pullback formula. Swapping the
  indices gives the other chart. Regular `coefficient_regular_boundary` uses
  `coefficientBoundaryCenter D h j`, the actual ideal of two coordinate hyperplanes;
  `hne` makes them distinct. It uses the scheme-theoretic pullback of X, never its
  saturated transform. `ha` and `hx'` express the statement's corresponding closed points.
  The returned `RegularCoefficientPullback ... 0` records the same coefficients on the
  cartesian inverse image of N and all five conditions.
- Independent variable: `coefficient_free_variable` extends K through the actual
  `MvPowerSeries.rename (Sum.map Fin.castSucc id)` ring homomorphism. It states all five
  conditions with one additional W variable, the inclusive sum of H, and the ordinary
  coefficient rename. `coefficient_regular_line` uses actual relative affine space with
  one variable, the total pullback of X, any lift of the distinguished point, and
  `HilbertSamuel.summation`. Its `RegularCoefficientPullback ... 1` has m+1 coefficient
  variables and cartesian coefficient pullback.
- Residue extensions: `coefficient_field_extension` takes every `L →+* E` in independent
  universes, maps K and every f_l by Mathlib's actual coefficient map, and states
  preservation of all five conditions and the full Hilbert sequence. The formal chart
  theorems range over any characteristic-zero L, so apply after passage to each exceptional
  residue field. There is no rational-point-only hypothesis.
- Étale localization of regular models: `coefficient_regular_etale` handles every
  étale `g : V ⟶ D.U` and every lift x', with no surjectivity or residue-isomorphism
  assumption. The level is unchanged and the cartesian regular model has ordinary
  pulled-back coefficients. The other regular clauses also return data on a common
  étale neighborhood, as allowed by the item.

### Dependency declarations read and reused

Read the full signature and docstring of every original statement dependency:

- `Sheaf.AlgebraicGeometry.RegularHilbertCoefficientData`:
  `exists_regularHilbertCoefficientDatum`; its public dependency
  `Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum`:
  `RegularHilbertCoefficientDatum`, `formalConditions`, `orderedVertices`,
  `fullVertex`, `homogeneousDivision`, `extendedHilbert`, `taylorIdeal`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`; its derivative module:
  `MvPowerSeries.pderiv`. The recorded derivative dependency is a Mathlib match and
  needs no added Lean record. Substitution, rename, coefficient map, and localization
  reuse Mathlib's actual operations. The exact-division coefficient shift matches the
  construction in `MvPowerSeries.X_pow_dvd_iff`, Basic.lean:600ff, which has no named
  division operator; it is not a replacement for an existing division definition.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `.blowupMap`.
- `WeilConjectures.Compactification.StrictTransform`: `AlgebraicGeometry.strictTransform`,
  `strictTransformMap`, `strictTransformToSource`, and ideal-sheaf strict transform.
- Mathlib morphism modules `FiniteType`, `QuasiCompact`, `ClosedImmersion`, `Smooth`:
  `LocallyOfFiniteType`, `QuasiCompact`, `IsClosedImmersion`, `Smooth`.

Additional statement dependencies (no replacement modules):
`def-trf-regular-hilbert-coefficient-datum` for the data structure;
`def-trf-implicit-transverse-coefficient` owns the existing
`implicitTransverseCoeff` (import is public because this helper appears in signatures);
`lem-trf-implicit-taylor-coordinate-calculus` remains a proof dependency only;
`def-trf-hilbert-samuel-invariant` for `HilbertSamuel.function`, `.le`, `.summation`;
`def-trf-marked-ideal-order` for `HilbertSamuel.stalkIdeal`;
`def-sbc-affine-space` for `AlgebraicGeometry.AffineSpace` (the recorded Mathlib match);
`def-weil-etale-morphism` for `Etale` (already publicly imported by the datum module).
Read their node statements and recorded declarations. The affine-space `over` instance is
its first projection, and `ULift (Fin 1)` is the node's one-variable specialization.

Stated proof dependencies imported: `FormalHilbertStratumMinors`,
`ImplicitTaylorCoordinateCalculus`, `JetDiagramHilbertControl`, and
`RegularHilbertCoefficientData`. The coordinate-blowup division-generators and homogeneous
continuous-division prerequisites have no Lean records yet; their mathematical uses are
retained explicitly in the theorem proof docstrings. No proof dependency was removed.

### Searches actually run

- msearch LeanFinder: `Hilbert Samuel equality stratum coefficient order criterion under
  permissible blowup strict transform`: eight hits, mainly prime-spectrum chain and
  one-variable Weierstrass factorization/division lemmas; no statement matching this node.
- msearch Loogle: `MvPowerSeries.order, Ideal`: zero hits.
- msearch grep: `HilbertSamuel|coefficientTransform|controlledTransform`: zero hits.
- msearch LeanSearch: `Hilbert Samuel equality locus coefficient ideals and their transforms
  under permissible blowups`: eight hits on leading-coefficient ideals, homogeneous ideal
  cores, smooth locus and one-variable division; none states the node.
- rg in project `WeilConjectures` and `Sheaf`: coefficient-transform, HilbertCoefficient,
  boundary-blowup patterns, plus the item id in `WeilConjectures`. Found the regular datum,
  the minors/calculus/jet modules and the consuming local-presentation module; no existing
  theorem states this criterion. The consumer mentions the item only in proof docstrings.
- rg in Mathlib MvPowerSeries for division, coefficient shift and coordinate substitutions:
  found `subst`, `substAlgHom`, `rename`, `map` and `X_pow_dvd_iff`; reused the existing
  operations. No named multivariate monomial division operator or coefficient criterion.
- Full proposed declaration names were searched in `lean/WeilConjectures`, `lean/Sheaf`
  and `dag/lean_names_upstream.json`; no clashes. No repair note for this item was present.

### Edge cases and validation

Checked s=0, n=0 and zero coefficients: empty sums give K=0; formal conditions have empty
Jacobian determinant 1 and empty support tests. A center with no tangent or transverse
coordinates has no denominator chart, matching the empty blowup of the whole ambient;
the regular strict-transform statements quantify over its actual points. The empty center
is also allowed; its exceptional fibre over the distinguished point is empty when that
point is outside it. Empty/deleted N' charts contribute no points, rather than an arbitrary
coefficient map. Tested the formulas on K=(Z^2-W^3), K=(Z), K=(Z^d) and the empty family:
weighted permissible transforms divide by the individual d_i; a boundary blowup leaves
Z^d unchanged. At degree q=0 the free-variable sum has one summand. |γ|=d_i uses the
zero exceptional power, high γ uses multiplication, and zero coefficients have infinite
order. A nonzero normal direction never satisfies equality; the formal iff excludes it.
Field extensions may enlarge universes and need not be algebraic. Nonclosed points use the
extended function throughout. No extra reducedness or equal-universe condition was added.

Compiled the complete delivered module through the prescribed `scompile.py`; both its
sandbox and library module names compile cleanly under the 60-second per-file limit, with
no errors and no warnings. Every theorem proof is exactly `by sorry`; all helper data are
explicit and no private notation, private instances, auto-bound variables or axioms occur.

## Second reading by NL

No second worker reading: the dispatcher explicitly forbids starting another agent and
requires direct delivery. The maintainer's independent review is the independent reading.
The author checked the clauses above against the node, the source and the compiled file.

## New nodes

`def-trf-implicit-transverse-coefficient` owns the already landed plain definition
`AlgebraicGeometry.HilbertCoefficient.implicitTransverseCoeff` in
`Sheaf.AlgebraicGeometry.ImplicitTaylorCoordinateCalculus`, with `lean.existing: true`.
For a field L, arbitrary m,r, a transverse exponent δ and a formal series f, its W^α
coefficient is the W^α Z^δ coefficient of f. These are exactly the binders and body of the
existing definition, including its absence of characteristic-zero or positivity assumptions.
The notion serves the transverse expansion in BM 1997, Theorem 9.4 and Remarks 9.5,
pp.277--278. The new node depends only on the existing multivariate-power-series definition.
LeanSearch returned coeff/subst operations; Loogle returned coeff_rename lemmas; Mathlib grep
returned zero matches. Project rg found the exact existing definition at line 175 and its
uses at 273 and 327; DAG rg found only the calculus theorem, with no owning definition node.
Blueprint searches for implicitTransverseCoeff and transverse coefficient both returned
zero nodes. The exact search logs are in the new node's mathlib_searches. This is a record
of the existing operation, with no new module or duplicated definition. For r=0 it extracts
the unique transverse exponent, for m=0 it is a constant series, and f=0 gives zero.
No finite-support condition is imposed on the series. All field universes are retained.

## Repair of returned delivery

H2 at immutable head e388c4dc0f05: replaced the calculus theorem in the item's stmt_deps
with `def-trf-implicit-transverse-coefficient`, whose existing record owns the actual
plain coefficient-extraction definition. Kept the calculus theorem in proof_deps, unchanged.
The nine theorem signatures, ten helpers and the entire delivered Lean file are byte-identical
(SHA256 4d0455cd204a0cfb89c9d4fb5712ba019ff7c16c1a33a477d82cba0d5e3bceab).
The source statement and every mathematical conclusion are unchanged. The saved packet was
compared with the current shared node: before repair only lean and stmt_deps differed.
The prescribed delivery wrapper rebases the repaired packet on the current live branch.
H11 was advisory; the dispatcher still forbids another agent. The new existing declaration
was checked directly against its full signature, docstring and coefficient formula.

## Reachability repair of returned head 7a4c893b4bb2

The independent review returned the new definition node because it is not reached
from a target and lacked the corresponding import flag. The first required dry run
on the retained packet confirmed the current preflight requires `import_flags` on
new definition nodes. Added `"import_flags": ["unreachable"]` to
`def-trf-implicit-transverse-coefficient`, identifying its historical resolution branch
as unreachable, as the return requires. No existing node metadata, mathematical
statement, dependency list, or Lean declaration changed in this repair.

Compared the retained packet with the current shared source without running Git:
the item differs only in its earlier `lean` attachment and added `stmt_deps`; the
new definition node is still absent from the shared tree. The delivery wrapper
rebases the packet on the current live branch. Re-read the recorded existing
`implicitTransverseCoeff` definition and its coefficient formula. The delivered
Lean source remains byte-identical (SHA256
`4d0455cd204a0cfb89c9d4fb5712ba019ff7c16c1a33a477d82cba0d5e3bceab`).
