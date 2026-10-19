## Worker report

Existing-declaration delivery. The definition
`AlgebraicGeometry.WeilSheaf.traceEnergy` and the theorem
`AlgebraicGeometry.WeilSheaf.le_sub_one_of_traceEnergy_le` already occur in
`WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy`, at local source lines
91–94 and 611–623. Both docstrings explicitly identify this blueprint item.
The published source was also read with `scompile.py --source`; its theorem
signature and energy definition agree with the local source (published line
numbers differ). The record names both declarations, with the theorem primary,
and copies its signature verbatim. No Lean module is delivered and no definition
or theorem is recreated. Only the item's `lean` field changes.

Read the complete node, its ten proof steps, all six statement-dependency nodes,
their recorded declarations and docstrings, and the main-20261015 statement and
proof. No repair note exists for this item. The upstream proof uses the L²-weight
interface and reaches postponed statements, as the item's audit already records.
Attaching the existing statement at stage 2 does not certify that proof, close the
audit, or replace the node's ten-step proof plan. Nothing is proved in this delivery.

Hypothesis and clause correspondence:

1. The setup's finite field is `{k₀ : Type u} [Field k₀] [Finite k₀]`;
   `q` is `Nat.card k₀`. The assumptions `{l : ℕ} [Fact l.Prime]
   [Fact (ringChar k₀ ≠ l)]` are exactly primality and exclusion of the
   characteristic. The geometric fibre uses `AlgebraicClosure k₀`.
   `PadicAlgCl l` is the chosen algebraic closure of the l-adic coefficient
   field. The fixed isomorphism `ι` is passed as its underlying ring homomorphism
   `PadicAlgCl l →+* ℂ`; this forgets no data used in the norms or purity.
   The existing declaration also accepts embeddings without asking for a
   surjectivity proof; it applies directly to every isomorphism in the setup.
2. The curve is `{V : Scheme.{u}} [V.Over (Spec (.of k₀))]`. Affineness is
   `[IsAffine V]`; smoothness and dimension one are
   `[SmoothOfRelativeDimension 1 (V ↘ Spec (.of k₀))]`;
   `[GeometricallyConnected (V ↘ Spec (.of k₀))]` requires connected
   geometric fibres, including nonemptiness. These are the standard scheme
   predicates collected by the convention dependency, not private replacements.
   `[LocallyOfFiniteType ...]` spells out the source's standing finite-type
   situation: affineness makes the structure map quasi-compact, and smoothness
   already implies local finite presentation. Thus this binder does not restrict
   the smooth affine curves of the source. Over a field, a smooth curve of pure
   dimension one is exactly smooth of relative dimension one. The dependency
   `FiniteFieldDatum.IsSmoothOfPureDimension` packages smoothness and the
   specified geometric fibre's pure dimension; the existing signature uses the
   equivalent standard relative-dimension predicate, not another definition.
3. The object is `(N : WeilSheaf k₀ l V)` with
   `(hN : ¬ Limits.IsZero N)` and `(hlisse : N.IsLisse)`. The carrier is a
   constructible rational Qbar-l sheaf on the geometric fibre with an invertible
   Weil isomorphism. `IsLisse` applies to its underlying adic sheaf. There is no
   assumption that the Weil automorphism preserves an integral lattice, and no
   assumption of semisimplicity, rank one or geometric irreducibility.
4. `{v : ℝ}` and `(hpure : N.IsPunctuallyPureOfWeight ι v)` encode purity.
   The predicate quantifies over finite closed points and uses
   `FrobeniusModule.IsPureOfWeight`; its body says for every eigenvalue `α`,
   `‖ι α‖ = (q_x : ℝ) ^ (v / 2)`. For schemes of finite type over the finite
   field these are precisely the closed points in the source.
5. The sum `S_n` is the actual definition `N.traceEnergy ι n`:
   `∑ᶠ x : (V ↘ Spec (.of k₀)).fieldPoints
     (FiniteField.galoisExtension k₀ n), ‖ι (N.traceFunction n x)‖ ^ 2`.
   `fieldPoints` is the type of base-compatible scheme maps from the extension
   field's spectrum. It realizes the `Over` Hom type of the field-valued-points
   dependency. `FiniteField.galoisExtension k₀ n` has degree n for n positive.
   `Scheme.Hom.finite_fieldPoints` shows this index type is finite under the
   theorem's hypotheses, so `finsum` is the ordinary finite sum, with no use of
   its infinite-support junk convention. The norm is Mathlib's complex norm,
   the square root of `Complex.normSq`, exactly the absolute-value dependency.
6. The relative Frobenius clause is in the real `traceFunction` definition:
   it takes `LinearMap.trace` of `(N.stalkAt _ n hs).frobeniusEnd`, using the
   geometric point over x obtained from an embedding of the extension field
   into the algebraic closure. Its return witness is the n-th geometric Galois
   Frobenius compatibility, and its Weil map is `frobeniusPowIso n`.
   Thus it is Frobenius relative to F_(q^n), not a single closed-point Frobenius
   reused at every extension degree. The local-trace dependency constructs the
   same local operator/alternating trace for complexes; on the sheaf heart,
   degree zero is the only cohomological term and the trace is ordinary linear
   trace. The existing declaration uses its already defined sheaf trace, so
   no duplicate local-operator construction or dependency repair is needed.
7. `{C B : ℝ} (hC : 0 < C)` binds one positive constant independent of n.
   `(hS : ∀ n : ℕ, 1 ≤ n → N.traceEnergy ι n ≤
     C * (Nat.card k₀ : ℝ) ^ ((n : ℝ) * B))` is every growth hypothesis,
   including its positive-degree range and real exponent nB. There is no
   restriction that B be positive or integral and no extra n = 0 condition.
8. The conclusion is literally `v ≤ B - 1`. No conclusion about H_c¹,
   cancellation of every pole, or any additional weight inequality is added.

Dependency sources read:

- `sk-d-dl-a1-setup`: `WeilConjectures.DeligneLaumon.AffineLine.Defs`,
  `AlgebraicGeometry.WeilSheaf.IsGeometricallyConstant` and
  `.IsUnramifiedAtInfinity`; its geometric-Frobenius and punctual-weight
  conventions are implemented for the sheaf in `WeilSheaf.Category` and
  `WeilSheaf.Stalk`. Neither extra predicate is a hypothesis of this item.
- `def-weil-geometric-hypotheses`: `Sheaf.Paper.GeometricHypotheses`,
  `WeilConjectures.FiniteFieldDatum.IsSmoothOfPureDimension`; its module
  explicitly reuses `AlgebraicGeometry.GeometricallyConnected`. The existing
  theorem uses Mathlib `SmoothOfRelativeDimension 1` on the same structure map.
- `def-weil-pbc-scheme-conventions`: a convention record with no declaration;
  `AlgebraicGeometry.IsAffine`, `LocallyOfFiniteType`, smoothness and the
  geometric-connectedness predicates keep their recorded standard meanings.
- `def-weil-local-frobenius-trace`: `Sheaf.Paper.LocalFrobeniusTrace`,
  `WeilConjectures.localFrobeniusTrace`, taking the finite-field datum,
  coefficient datum, finite coefficient field, Weil complex, positive degree
  and extension point. Its extension operator, transport and trace docstrings
  were read. The sheaf analogue used by the existing theorem is
  `WeilConjectures.WeilSheaf.Stalk`,
  `AlgebraicGeometry.WeilSheaf.traceFunction`.
- `def-weil-field-valued-points`: Mathlib `CategoryTheory.Over`,
  `Mathlib.CategoryTheory.Comma.Over.Basic`; `Over.Hom` is a commuting
  triangle, implemented as base-compatible scheme maps by `fieldPoints`.
- `def-weil-complex-absolute-value`: `Complex.instNorm`,
  `Mathlib.Analysis.Complex.Norm`; its body is `√(normSq z)`.

Edge cases checked: the zero sheaf is excluded by `hN`; without this exclusion
purity is vacuous at every weight and the conclusion can fail. Geometric
connectedness excludes the empty curve. The growth hypothesis deliberately
starts at n = 1, so the degree-zero extension's junk value has no effect.
An individual energy S_n may vanish and no positivity of each S_n is assumed.
Negative/nonintegral weights and growth exponents are included. The constant
rank-one sheaf on A¹ has S_n = q^n and weight zero, so C = 1 and B = 1 make
the conclusion sharp. Non-diagonalizable Frobenius is allowed. An infinite
rational-point index is impossible for the finite-type curves here. There are
no new independent universe variables or a restriction on the field's size.

Searches on 2026-10-18:

- `msearch.py ... leanfinder` with "A nonzero lisse pure Weil sheaf on a
  smooth geometrically connected affine curve has weight at most B minus one
  if its sums of squared Frobenius traces grow at most C q to nB": eight
  unrelated sieve, discriminant and Lie-weight results; no Mathlib match.
- `msearch.py ... loogle` with
  `AlgebraicGeometry.WeilSheaf.traceEnergy,
  AlgebraicGeometry.WeilSheaf.le_sub_one_of_traceEnergy_le`: zero hits;
  upstream names are unknown to the Mathlib search service.
- `msearch.py ... leansearch` with "trace energy squared Frobenius traces
  pure lisse Weil sheaf affine curve weight bound": eight results on finite
  field matrix traces, normalized traces and other unrelated topics; no match.
- `msearch.py ... grep 'traceEnergy|le_sub_one_of_traceEnergy_le'`: zero
  Mathlib hits. `rg` of those names under upstream `WeilConjectures` finds
  both exact declarations in `DeligneLaumon/AffineLine/TraceEnergy.lean` and
  their consumers. The same `rg` under project `lean/Sheaf` found no duplicate.
- `rg -n 'sk-l-dl-a1-energy'` upstream identifies both tagged docstrings.
  `dag/lean_names_upstream.json` independently names both declarations, and
  the item's audit points to their exact source module.
- The current upstream module was retrieved through
  `scompile.py --source WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy`;
  its energy and theorem signature were compared with the local source.

Validation: a sandbox-only scratch file imports the existing module, sets
`autoImplicit false`, and checks all implicit arguments of both attached
names, the trace function and the purity predicate. The first probe printed
universes and produced a development-option warning; that option was removed
for the final clean run, which passed without warnings in both sandbox
and published-library checks (7.9 s and 9.5 s). This scratch file is not a
delivered module. The
required dry run and delivery also check existing-name resolution.
No statement correction, new nodes, dependency modules or statement dispute.

## Second reading by Q57

No second worker was started: the dispatcher brief explicitly forbids other
agents and assigns the independent reading to the maintainer. I reread the
node against both full source signatures and their definition bodies. I checked
in particular the extension-degree Frobenius, positivity and independence of C,
the n ≥ 1 guard, nonzero object condition, and the curve hypotheses described
above. No mathematical mismatch or node change was found. The only validation
change was removal of a printing option that caused a style warning.
