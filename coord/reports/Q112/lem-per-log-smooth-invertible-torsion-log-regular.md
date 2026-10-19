# Q112: lem-per-log-smooth-invertible-torsion-log-regular

## Worker report

The module `Sheaf.AlgebraicGeometry.LogSmoothInvertibleTorsionLogRegular` states
`AlgebraicGeometry.logSmooth_invertibleTorsion_logRegular` with proof `sorry`.
Its helper structure `AlgebraicGeometry.InvertibleTorsionFSLogChart` bundles exactly
this theorem's compatible chart condition. It is listed in `lean.declarations` and
has the owning node's source and blueprint docstring. No new independent notion,
new DAG node, dependency repair, statement correction, or proof is introduced.
Only the item's `lean` record changes.

The previous worker's stale-assignment diagnosis confused the stage-1 split with
stage-2 completion. Q108's report supplies the four-step natural-language proof;
the current node has no Lean binding or stage-2 review. Thus this is its first
Lean statement, rather than a replacement of a reviewed declaration.

Clause-by-clause correspondence:

- The locally Noetherian fs log schemes `(X,M_X)` and `(Y,M_Y)` are
  `X Y : FineSaturatedLogScheme.{u}`. Its fields `scheme`, `locallyNoetherian`,
  `logStructure`, and `fineSaturated` give exactly these objects and conditions.
- The morphism of log schemes is `f : EtaleLogHom X Y`, including the underlying
  scheme morphism and the compatible natural maps on log sections.
- Log regularity of the target is `hY : Y.IsLogRegular`. This is the recorded
  geometric-stalk regular-stratum quotient and Krull-dimension/rank formula.
- “Étale locally on source and target” is `hcharts`: for every algebraically
  closed field `Ω : Type u` and geometric source point `t`, there exists a chart
  `c` with `Nonempty ((Scheme.pointSmallEtale t).fiber.obj c.V)`. The object `c.V`
  is an étale source neighbourhood admitting a lift of that point; `c.W` is an
  étale target neighbourhood. `c.map` and `c.map_over` make them neighbourhoods
  compatible with the given morphism. No global chart is required.
- The node's monoids `A,B` are the helper's `P,Q : Type u`, with commutative
  monoid structures `instP,instQ`. `fineP,fineQ` use the existing
  `IsFineSaturatedMonoid`, including finite generation, integrality and saturation.
- The charts `A → M_Y` and `B → M_X` are `chartY` and `chartX`, together with
  `chartY_isChart` and `chartX_isChart`. They use the dependency's actual
  associated-stalk chart condition `EtaleLogStructure.IsChart`.
- The node's homomorphism `h` is `g : P →* Q`. `chart_compatibility` says its
  composite with the source chart equals the target chart pulled back by `f`.
- Injectivity of `h^gp` is `gp_injective`, applied to the canonical
  `Algebra.GrothendieckGroup.lift ((Algebra.GrothendieckGroup.of (M := Q)).comp g)`.
  Group completions use multiplicative notation, which represents the same
  abelian groups as the additive notation of the node.
- Its cokernel is the actual quotient `Algebra.GrothendieckGroup Q ⧸ gpMap.range`;
  `gpMap` here is an explanatory abbreviation for the displayed canonical lift,
  not an additional declaration or arbitrary map. `CommGroup.torsion` is the
  Mathlib torsion subgroup of that quotient. `torsion_finite : Finite (...)`
  expresses finiteness without choosing an enumeration.
- The order is exactly `Nat.card (CommGroup.torsion (...))`.
  `torsion_order_invertible` asserts this integer is a unit in `Γ(V.left, ⊤)`.
  This is equivalent to invertibility on the source neighbourhood: evaluation
  preserves units, and local inverses of a section glue uniquely to a global
  inverse. It requires no invertibility on all of the original target.
- The monoid rings are Mathlib `MonoidAlgebra ℤ P` and `MonoidAlgebra ℤ Q`.
  Their elements are finite sums of integral monomials, with the stated monomial
  multiplication. `MonoidAlgebra.single p 1` is the node's `z^p`.
- The chart-induced morphisms to the spectra are `y,x`; `y_chart,x_chart` fix
  their values on every chart monomial through `Scheme.ΓSpecIso`. Ring maps from
  these integral monoid rings are determined by those values, so these are the
  canonical chart morphisms, with no extra choices or assumptions.
- The comparison lands in `pullback y (Scheme.Spec.map (...).op)`, the stated
  ordinary scheme fibre product. The ring map inside is precisely
  `MonoidAlgebra.mapDomainRingHom ℤ g`. `comparison_fst` and `comparison_snd`
  prescribe its two projections to be `map` and `x`, hence uniquely characterize
  the induced comparison. It is not an unconstrained chosen map.
- The smoothness clause is `Smooth c.comparison` in `hcharts`, using the recorded
  Mathlib definition. The conclusion is exactly `X.IsLogRegular`.
- The final clarification permitting nonzero torsion is respected: neither
  `Subsingleton` of the torsion subgroup, torsion-freeness, nor Kummer-ness of
  the whole original chart map is assumed. This clarification is not an extra
  mathematical conclusion requiring another conjunct.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `AlgebraicGeometry.FineSaturatedLogScheme`, `AlgebraicGeometry.EtaleLogHom`,
  `AlgebraicGeometry.EtaleLogStructure.IsChart`, and
  `AlgebraicGeometry.FineSaturatedLogScheme.IsLogRegular`; their full definitions
  and docstrings were read. The fs monoid predicate comes through its recorded
  import `Sheaf.AlgebraicGeometry.LogRegularPair`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map` and
  `Scheme.Spec`; the functorial form is the same spectrum construction.
- Mathlib's monoid algebra, Grothendieck group, group range, group quotient and
  `CommGroup.torsion` definitions supply the existing algebraic constructions.

The already-stated proof dependencies are imported privately:
`Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks`,
`Sheaf.AlgebraicGeometry.LogSmoothLogRegular`,
`Mathlib.AlgebraicGeometry.Pullbacks` (the recorded `pullbackSpecIso` match), and
`Mathlib.RingTheory.FiniteType` (the recorded
`Algebra.FiniteType.isNoetherianRing` match). The two still-unstated proof lemmas
`lem-per-fs-chart-torsion-factorization` and
`lem-per-invertible-kummer-chart-log-regular` have no modules to import; neither
is required to type the statement. Their proof roles remain explicit in the
four-step theorem docstring and unchanged DAG. No import cycle is introduced.

Edge cases checked before writing:

- An empty source has no geometric source points; both `hcharts` and the
  pointwise log-regularity conclusion are vacuous. No nonempty scheme assumption
  is added, and invertibility on an empty chart is interpreted in its zero ring.
- A trivial torsion subgroup has order one, so its invertibility clause holds
  automatically. Identity charts and torsion-free chart cokernels are retained.
- The chart `ℕ → ℕ`, `a ↦ n*a`, has group cokernel `ℤ/nℤ`. For `n > 1` with
  invertible `n` it is allowed; no clause forces its torsion to vanish. In residue
  characteristic dividing `n` its order is not invertible on a nonempty chart,
  and the hypothesis correctly excludes it.
- The group cokernel can have a nonzero free part; finiteness is required only
  for its torsion subgroup. Neither chart is required sharp or torsion-free.
- The geometric points, schemes, chart monoids and site universes all use the
  existing `u` convention. There is no independent smaller test-field universe
  and no restriction to closed points or rational points. Every finitely
  generated chart monoid admits a representative in this universe.

Sources read: the local ILO PDF, Exposé VI 1.1–1.8 (printed pp.69–70), and
Exposé XVI 3.6.3 (printed p.252). VI 1.8 gives the preservation theorem; XVI 3.6.3
explains the finite invertible chart-cokernel torsion. The docstring records the
node's agent-origin reduction, rather than claiming Kato's proof was available.

Existing-declaration searches:

- `msearch.py` LeanFinder, query “Log smooth morphisms of fine saturated log
  schemes with finite invertible chart torsion preserve log regularity”: ordinary
  smooth-morphism results only; no matching logarithmic statement.
- `msearch.py` LeanSearch, query “Log smooth morphisms with finite invertible
  torsion in compatible fine saturated charts preserve log regularity”: eight
  ordinary smooth/formally smooth results; no logarithmic match.
- `msearch.py` Loogle, query `AlgebraicGeometry.logSmooth_logRegular`: no hits
  (unknown identifier in the Mathlib search service).
- `msearch.py` Mathlib grep, query `logSmooth|LogSmooth|log.?regular` under
  `AlgebraicGeometry`: zero hits.
- `rg` of the upstream `WeilConjectures` tree for
  `logSmooth|LogSmooth|log_smooth|log.?regular|LogRegular`: zero hits. Exact
  blueprint-id search likewise found no attachment.
- The same `rg` search in `lean/Sheaf` found the existing
  `AlgebraicGeometry.logSmooth_logRegular` and `InjectiveFSLogChart`, whose full
  module was read. Their hypothesis requires torsion-free group cokernel and
  their conclusion also includes the divisorial structure. They do not state
  this node's theorem and their chart structure cannot represent its allowed
  nonzero torsion. The new helper reuses all underlying notions and bundles the
  different chart condition of this node; it does not redefine log schemes,
  charts, log regularity, group completion, cokernel, torsion, or smoothness.

No statement dispute or node fault was found. Every variable and universe is
explicitly bound (`set_option autoImplicit false`). The sole theorem has the
whole proof `by sorry`; the structure contains real chart data and constraints.

Validation: `scompile.py Q112 lem-per-log-smooth-invertible-torsion-log-regular`
compiled the module separately in sandbox and library contexts within the
60-second per-file limit, with no errors or non-sorry warnings. The delivery dry
run below repeats compilation and the server preflight on the final packet.

## Second reading by Q112

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
