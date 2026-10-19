## Worker report

The module `Sheaf.AlgebraicGeometry.PrimeToOrderSNCKummerCharts` states
`AlgebraicGeometry.Scheme.primeToOrder_snc_kummerCharts`, with `sorry` as its only proof.
No definition is introduced. The preserved sandbox contained no prior Lean file, node copy,
report, or running delivery. Q68's existing review concerns the stage-1 split, not a Lean
statement; the current item has no `lean` binding. This delivery leaves that split intact.

I read the item, all statement dependencies and their recorded interfaces, the current
`FSLogChart` implementation, the log structures and divisorial presheaf implementations,
and ILO IX Proposition 2.1 and its proof, printed pages 133--134. The module's docstring
carries all seven proof steps, including the named dependencies. The already-published
ancestor consumer `TameNormalizationLogRegular` also unpacks the connected cover's
integral structure and canonical function-field algebra existentially.

The theorem unpacks the objects already denoted by k(V')/k(Y), without adding an
integrality hypothesis on the cover: `IsIntegral C.Z` is an existential conclusion.
The following existential algebra is fixed by the generic-morphism equation, and
`FiniteDimensional Y.functionField C.Z.functionField` expresses the stated finite
extension. The hypothesis that this extension's normalization is finite is retained
as `_hb` in an implication after those dependent witnesses. Thus the chart conclusion
still requires finiteness; it does not silently assert finiteness of normalization.

The hypothesis and conclusion correspondence is as follows.

| Node clause | Lean rendering |
| --- | --- |
| Integral regular Noetherian Y | `Y : Scheme.{u}`, `[IsIntegral Y]`, `_hY : IsRegularScheme Y`, `[IsNoetherian Y]` |
| Strict normal crossings boundary T | `T : Y.IdealSheafData`, `_hT : IsStrictNormalCrossingsBoundary T` |
| V is the boundary complement | `Scheme.Opens.toScheme T.support.compl` and `Scheme.Opens.ι T.support.compl` |
| M is the divisorial log structure | `M : EtaleLogStructure Y`, `eM` to `divisorialLogPresheaf` of that inclusion, and `_heM` identifying the structural maps |
| M is fine saturated | `hM : M.IsFineSaturated` |
| Finite group with invertible order on Y | `(G : Type v) [Group G] [Finite G]`, `_hG : IsUnit (Nat.card G : Γ(Y, ⊤))`; invertibility of the global constant is equivalent to invertibility in all local rings by the sheaf property |
| Connected finite etale G-torsor over V | `C : Scheme.GaloisCoverAction G ...`, `[ConnectedSpace C.Z]`; the recorded structure supplies the finite etale surjective morphism, the action, simple transitivity, and quotient |
| Normalization in the finite function-field extension | `Y.normalizationIn C.Z.functionField`, with the existential integral structure, algebra, `FiniteDimensional`, and generic-morphism equality specifying the induced extension |
| Canonical b is finite | `_hb : IsFinite (Y.fromNormalizationIn C.Z.functionField)` |
| fs log structure N on Z | existential `N`, `hN : N.IsFineSaturated`; `hZ` supplies local Noetherianity required by the published fs-log-scheme interface, which follows from the assumed finite map to Noetherian Y |
| Log morphism over b | existential `f : EtaleLogHom` between exactly those bundled log schemes, and `f.base = Y.fromNormalizationIn C.Z.functionField` |
| Every geometric z over y | arbitrary algebraically closed `Ω : Type u` and `z : Spec (.of Ω) ⟶ Z`; y is its actual composite with b |
| Pointed etale W and U with W to U over b | `c : FSLogChart f`, source lift `w`, target lift `y`, `w.left ≫ c.map = y.left`; `c.map_over` is built into the chart |
| Compatible charts P, Q and h | `c.chartY`, `c.chartX`, `c.g`, their `IsChart` fields and `chart_compatibility` |
| P and Q fine saturated | `c.fineP`, `c.fineQ` |
| Both monoids sharp | `∀ p, IsUnit p → p = 1` and the corresponding Q clause; the published log interface uses multiplicative notation |
| Chart maps identify the characteristics at the selected points | both `Function.Bijective` clauses for the specific chart germs followed by `Associates.mk`; `EtaleLogStructure.characteristic` is exactly that quotient |
| Injective h | `Function.Injective c.g` |
| Every q has a positive multiple in h(P) | `∀ q, ∃ n : ℕ, 0 < n ∧ ∃ p, c.g p = q ^ n` |
| Injective group map, finite cokernel | `Function.Injective c.groupMap ∧ Finite c.cokernel` |
| Positive invertible annihilator on U | existential positive n, `∀ a : c.cokernel, a ^ n = 1`, and `∀ t : c.W.left, IsUnit (n : c.W.left.presheaf.stalk t)` |
| Canonical comparison is etale | `Etale c.comparison`; this is the prescribed pullback lift using the chart-to-spectrum maps and `MonoidAlgebra.mapDomainRingHom` |
| Spec Z[P], multiplication z^p z^q = z^(pq) | the published chart interface uses Mathlib `MonoidAlgebra ℤ P`, the finitely supported free abelian group with convolution multiplication |
| Empty boundary allowed; no excellence or log-regularity conclusion | no nonemptiness condition on T, no excellence binder, and no log-regularity conjunct |

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`, which
  includes local Noetherianity and the upstream stalkwise `IsRegular` predicate.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsNoetherian`, `IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`.
- `Sheaf.AlgebraicGeometry.NormalScheme`: `Scheme.GaloisCoverAction`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale` and `.Finite`: `Etale`, `IsFinite`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`: `Scheme.normalizationIn`,
  `Scheme.fromNormalizationIn`, `Scheme.fromSpecOfAlgebraFunctionField`.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `EtaleLogStructure`,
  `EtaleLogStructure.IsFineSaturated`, `FineSaturatedLogScheme`, `EtaleLogHom`, the chart
  germ and characteristic interfaces.
- `Sheaf.AlgebraicGeometry.LogRegularPair`: `divisorialLogPresheaf`,
  `divisorialStructuralMap`, `IsFineSaturatedMonoid`.
- `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`: `FSLogChart`, `.comparison`, `.groupMap`,
  `.cokernel`; these use the actual monoid algebra and canonical comparison maps.

I added the already-landed definition nodes `def-trf-log-regular-pair` and
`def-per-fs-log-smooth-etale` to `stmt_deps` because those are the owning nodes of the
published divisorial and compatible-chart constructions. No private copy or new node
is needed. Four available proof-dependency modules are imported without `public`:
`RegularBoundaryDivisorialChart`, `InvertibleKummerChartLogRegular`,
`AssociatedLogUniversalStalks`, and `LogRegularDivisorialStructure`.
The affine-spectrum fibre-product leaf has the Mathlib match `pullbackSpecIso`, so
`Mathlib.AlgebraicGeometry.Pullbacks` is also imported. The two root/invariant algebra
proof dependencies have no recorded Lean modules and hence contribute no imports.

Edge cases checked before writing: empty boundary (the sharp chart monoids can be
trivial); the trivial group and degree-one cover; nontrivial ramification along a
single component (the group cokernel may be nonzero); intersections of multiple
components (no regularity of Z is asserted); generic/interior points (trivial sharp
characteristics); arbitrary group universe v independent of scheme universe u; and
absence of any excellence assumption. The empty scheme is already excluded by the
item's integral-base hypothesis. Connectedness includes nonemptiness of the cover.
An arbitrary selected geometric z determines exactly its geometric image y, with
pointed lifts required to commute, so no closed-point or merely underlying-point
restriction replaces the node's requirement.

Searches made:

- `msearch.py leanfinder`, query “Finite etale torsors of invertible group order over
  complement of strict normal crossings divisor admit sharp Kummer charts on the finite
  normalization”: eight unrelated standard-etale and normalization-cover hits, no match.
- `msearch.py loogle`, query `AlgebraicGeometry.FSLogChart,
  AlgebraicGeometry.Scheme.normalizationIn`: no hits; FSLogChart is not in Mathlib.
- `msearch.py leansearch`, query “Kummer charts for finite normalization in a torsor of
  invertible order along a normal crossings boundary”: eight hits concerning Kummer-Dedekind
  algebra and generic scheme normalization, no such log chart statement.
- `msearch.py grep`, query `Kummer|kummer|normalizationIn` in Mathlib AlgebraicGeometry:
  no hits returned by that search endpoint.
- Direct `rg` of the upstream WeilConjectures tree and `lean/Sheaf` for the node id and
  SNC/Kummer theorem-name variants: only the ancestor's proof-plan reference; no existing
  statement. Direct reading found the generic FSLogChart API and its log-regularity
  consequence, neither of which states existence for these torsors.

No statement dispute or source correction was needed. No shared file or launcher script
was edited. All work is in the assigned sandbox. The sole sorry is the named item theorem.
Initial `scompile.py` found only the need to spell `Scheme.Opens.ι`/`.toScheme` explicitly;
that was repaired. The subsequent wrapper run compiled both the sandbox and exact library
module names cleanly, with no warnings (3.0 and 3.1 seconds respectively). The delivery dry
run repeats compilation after the final explicit Mathlib proof import.

## Second reading by Q40

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
