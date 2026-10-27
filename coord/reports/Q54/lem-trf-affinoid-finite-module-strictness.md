## Worker report

The module `Sheaf.Analysis.Normed.Module.AffinoidFiniteModuleStrictness` states
`RestrictedSeries.affinoid_finite_module_strictness`, with its only proof `sorry`.
No definition, dependency repair, new node, or statement correction is needed.
Only the item's `lean` field changes.

Hypothesis and conclusion comparison with the node:

| Node clause | Lean rendering |
| --- | --- |
| K is a field with a nontrivial real-valued absolute value | `[NontriviallyNormedField K]`, extending `NormedField` and hence `Field`; its norm has codomain ℝ and is multiplicative. Its nontriviality condition is equivalent to a nonzero element of norm different from one. |
| The field is complete and nonarchimedean | `[CompleteSpace K] [IsUltrametricDist K]`. |
| A is nonzero | `[Nontrivial A]`. |
| A is a quotient of a restricted-series ring with its Tate quotient Banach norm | `[NormedCommRing A] [Algebra K A]` and `hA : IsAffinoidQuotient K A (algebraMap K A)`. The existing predicate includes completeness, an existential number of variables, a surjective ring map compatible with constants, and equality with the infimum of the Gauss norms of all representatives. It allows any number of variables, including zero. |
| M and N are finitely generated A-modules | `[Module A M] [Module.Finite A M]` and the analogous N instances. |
| Each has a complete nonarchimedean K-vector-space norm | `[NormedAddCommGroup M] [NormedSpace K M] [IsUltrametricDist M] [CompleteSpace M]` and the analogous N instances. NormedSpace over a normed field gives exact scalar homogeneity, not merely continuity. |
| The K-vector-space structures are those of A-modules over K | `[IsScalarTower K A M]` and `[IsScalarTower K A N]`, with the specified algebra structure on A. These express the usual compatibility of the Banach-module scalar actions; independent, unrelated K-actions are not substituted for them. |
| The scalar actions are bounded by some positive constants c_M, c_N | `hM` and `hN` each assert `∃ c : ℝ, 0 < c ∧ ∀ a m, ‖a • m‖ ≤ c * ‖a‖ * ‖m‖` (with N in the latter). No bound of one or additional normed A-module structure is assumed. |
| Every A-linear map u | The arbitrary binder `(u : M →ₗ[A] N)`, without continuity in its type or hypotheses. |
| u is continuous | First conjunct `Continuous u`. |
| u has closed image | Second conjunct `IsClosed (Set.range u)`. This is actual image closedness, not closedness of its closure. |
| If u is injective there is a real H > 0 bounding the source norm by H times the image norm, for every m | Third conjunct `Function.Injective u → ∃ H : ℝ, 0 < H ∧ ∀ m : M, ‖m‖ ≤ H * ‖u m‖`. |
| Zero modules are permitted | Neither M nor N has a `Nontrivial` or positive-rank hypothesis. |

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field` in `Mathlib.Algebra.Field.Defs`, inherited
  through `NontriviallyNormedField`; its normed refinements were read in
  `Mathlib.Analysis.Normed.Field.Basic`.
- `def-trf-restricted-series-presentation`:
  `RestrictedSeries.IsAffinoidQuotient` in
  `Sheaf.RingTheory.RestrictedSeriesPresentation`, using its exact signature,
  source docstring, scalar compatibility, completeness, and quotient norm formula.
- `def-weil-finitely-generated-module`: `Module.Finite` in
  `Mathlib.RingTheory.Finiteness.Defs`, namely finite generation of the top submodule.

Stated proof dependencies are imported non-publicly as the stage-3 proof plan:

- `RestrictedSeries.affinoid_polynomial_closed_point_comparison` in
  `Sheaf.RingTheory.AffinoidPolynomialClosedPointComparison`, for Noetherianity
  of the Tate ring by taking the polynomial ideal zero.
- `IsNoetherianRing` in `Mathlib.RingTheory.Noetherian.Defs` and
  `Submodule.FG.of_le` in `Mathlib.RingTheory.Noetherian.Basic` for finite
  generation of the closure submodule.
- `ContinuousLinearMap.exists_preimage_norm_le` in
  `Mathlib.Analysis.Normed.Operator.Banach`, the recorded Mathlib match for
  `lem-trf-banach-surjective-bounded-lifts`. It gives a positive real uniform
  preimage bound for continuous surjections between complete normed spaces.

The theorem docstring includes the node's full four-step proof plan: establish
Noetherianity and completeness of finite powers; obtain bounded representatives
in finite generators and automatic continuity; approximate generators of the
closure and sum geometrically decreasing corrections to prove closed image;
apply bounded lifts to the injective corestriction for the lower norm bound.

Source check: opened Kedlaya's
[A little p-adic functional analysis (part 2 of 2)](https://kskedlaya.org/18.727/p-adic2.pdf),
PDF p. 1, Lemma 1. It establishes closedness of submodules of finite Banach modules
over a Noetherian Banach algebra. Its proof uses the same closure-generator and
successive-approximation argument. The node explicitly includes the standard
finite-generator/open-mapping corollary and bounded-action version, as reflected
in the supplied proof. The node also cites Bosch section 1.4 Proposition 2(i) for
Tate Noetherianity, represented here by the already recorded comparison theorem.
The node's source says archival copies are WANTED; no literature files were changed.

Edge cases checked before writing:

- M = 0: continuity and closed zero image hold; H = 1 supplies the last clause.
- N = 0: the map is zero and closed; injectivity forces M = 0, again allowing H = 1.
- Noninjective and zero maps: the first two conclusions remain asserted, and the
  third is only conditional, exactly as stated.
- A nonzero is retained. A zero quotient is allowed by the dependency predicate,
  but is intentionally excluded here by the node's explicit A ≠ 0 hypothesis.
- Presentations in zero variables and zero relation ideal remain included by hA.
- No characteristic, discrete valuation, finite K-dimension, fixed presentation,
  fixed generating set, or common universe of K, A, M, N is imposed.

Searches for an existing declaration, all via the prescribed msearch wrapper:

- LeanFinder: `Every linear map between finite Banach modules over a Tate affinoid
  algebra is continuous has closed image and an injective norm lower bound`.
  Eight hits, including `LinearMap.isClosedEmbedding_of_injective` (requires finite
  dimension over a field) and
  `ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range` (assumes both
  continuity and closed range). Neither states this node.
- Loogle: `IsModuleTopology.continuous_of_linearMap,
  ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range`: zero hits for
  this combined query.
- LeanSearch: `Every linear map between finitely generated Banach modules over an
  affinoid algebra is continuous and has closed image`. Eight hits, including
  `IsModuleTopology.continuous_of_linearMap`, which assumes the module topology,
  and finite-dimensional continuity results. None gives this affinoid conclusion.
- Mathlib grep in Analysis: `affinoid|TateAlgebra|isClosed.*[Ss]ubmodule|continuous_of_linearMap`.
  Eight hits concerning closed submodules, finite-dimensional spaces, and existing
  closed-range assumptions; no match.
- Project/source `rg`: `affinoid|Affinoid|finite_module_strictness|lem-trf-affinoid-finite-module-strictness`
  across `lean/WeilConjectures` and `lean/Sheaf`. Found the existing presentation and
  polynomial comparison modules, but no finite-module strictness statement.
- Additional name search `affinoid_finite_module_strictness|AffinoidFiniteModuleStrictness|finite.*module.*strict`
  in `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and `lean/Sheaf` found no
  exact declaration (only unrelated finite-module occurrences).
- Literal node-id grep in `lean/WeilConjectures` found no occurrences.

Validation: the prescribed `scompile.py` successfully compiled both its isolated
sandbox check and the library-named module on the server, with no errors or
unexpected warnings. Auto-bound implicits are disabled, all four universes and all
binders are explicit, and every Lean line is at most 100 characters.

## Second reading by Q54

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
