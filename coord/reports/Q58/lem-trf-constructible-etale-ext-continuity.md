## Worker report

This repairs the returned immutable head `3e31d969ee70`, preserving the mathematical
node statement. The saved packet was inspected first and the prescribed initial dry
run passed mechanically (`d9b04d34a8`); its mathematical defects identified by the
maintainer remained, so this delivery repairs them rather than re-pushing that packet.
The current shared node was compared with the sandbox: every non-`lean` field agrees.

The module `lean/Sheaf/TraceFormula/ConstructibleEtaleExtContinuity.lean` states
`AlgebraicGeometry.Etale.constructible_etale_ext_continuity` and supplies its canonical
maps and named compatibility clauses. There are no free diagrams, comparison maps,
legs, or hypotheses purporting to make an arbitrary map canonical.

Hypothesis and clause correspondence:

- The small nonempty directed set is `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. The schemes have the same index universe.
- The inverse system is `D : Iᵒᵖ ⥤ Scheme.{u}`. The instance
  `[∀ i : Iᵒᵖ, IsNoetherian (D.obj i)]` supplies precisely Noetherian schemes,
  including compactness and quasi-separatedness: Mathlib's `IsNoetherian` extends
  `IsLocallyNoetherian` and `CompactSpace`, and
  `IsLocallyNoetherian.quasiSeparatedSpace` supplies the latter property. The vacuous
  `QuasiSeparated (𝟙 _)` hypothesis has been removed.
- Affine transitions are `[∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]`.
  The limit and its projections are `c : Cone D`, `hc : IsLimit c`, and `c.π.app`.
  `i : I` fixes the initial stage, so all later stages satisfy `i ≤ j`.
- The finite commutative coefficient ring is `{A : Type (u + 1)} [CommRing A]
  [Finite A]`. This is the published module-sheaf encoding, with the required
  coefficient/site universes and no additional universe equality.
- `P Q : Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} A)` are the two
  initial module sheaves; `hP` and `hQ` use the recorded
  `Scheme.IsConstructibleEtaleModuleSheaf` predicate. No projectivity, local
  constancy, finite Tor amplitude, or flatness assumption is added.
- Inverse images are exactly `upperStar (ModuleCat A) f`. The definition
  `affineLimitExtHom f P Q p q` is the Hom between their single complexes in
  cochain degrees `-p` and `-q`. Thus `p = 0`, `q = n` represents
  `Hom_D(f*P,f*Q[n])`, exactly the node's ordinary module-derived Ext group.
  This fixes a further sign defect of the saved packet: `singleFunctor n`
  represents `Q[-n]`, not `Q[n]`. The sign was checked against Mathlib's
  `DerivedCategory.singleFunctors` and its `shiftIso` usage in `Ext/Basic.lean`.
- `∀ n : ℕ` ranges over precisely the integers `n ≥ 0`. Its first conjunct says
  every limit Ext class is `affineLimitExtLeg` of some later-stage class.
  Its second conjunct quantifies over representatives at ANY two later stages
  and says equal images agree at a common later stage. These are the surjectivity
  and injectivity statements for the canonical filtered-colimit comparison.
  The maps are additive because they are compositions of an additive exact
  derived functor's Hom map with pre- and postcomposition by fixed isomorphisms;
  consequently this is also bijectivity of the group comparison, as required.
- The later-stage map is `affineLimitExtTransition D hij hjk`, from Ext on `X_j`
  to Ext on `X_k` when `j ≤ k`. This is COVARIANT in later stages; there is no
  opposite-tail colimit. In particular, the initial stage is not treated as a
  terminal stage of the Ext system.
- `affineLimitExtSingleIso` is the composite of the actual `upperStarComp` on a
  sheaf with the inverse of `mapDerivedCategorySingleFunctor`. The definition
  `affineLimitExtPullback` conjugates `(upperStar _ g).mapDerivedCategory.map a`
  with these isomorphisms. `affineLimitExtLeg` supplies the cone equation to this
  definition, and `affineLimitExtTransition` supplies `D.map_comp`. Thus all legs
  and all transitions are tied to exact inverse image by their definitions.
- The node's composition clause is the named theorem
  `affineLimitExtPullback_comp`, for arbitrary sheaves and arbitrary integer
  source/intermediate/target shifts. This includes composition of Ext morphisms
  after the appropriate shifts. `affineLimitExtPullback_trans` states compatibility
  with successive scheme pullbacks, and `affineLimitExtLeg_transition` states
  the precise later-stage/limit-leg equality. All are recorded in
  `lean.declarations` and carry the owning node's source and proof docstrings.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` (the correct id, replacing the report's typo):
  a convention node with no declaration; Mathlib `Scheme`, `IsNoetherian`,
  `IsLocallyNoetherian.quasiSeparatedSpace`, and `IsAffineHom` render its conventions.
- `lem-weil-pbc-limit-affine-transition`:
  `AlgebraicGeometry.exists_limit_affine_transition` from
  `Sheaf.AlgebraicGeometry.LimitAffineTransition` (limit cone and affine projections).
- `def-weil-pbc-etale-constructible-sheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` from the recorded
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`; its finite-stratum,
  finite-value module-sheaf definition was read in full.
- `def-weil-pbc-derived-categories`: the published encoding
  `AlgebraicGeometry.Etale.DerivedCategoryModule` is the ordinary `DerivedCategory`
  used here, from `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
  The recorded module `WeilConjectures.AlgebraicGeometry.DerivedCategories` was
  also read with `scompile.py --source`; its docstring expressly identifies the
  encoding and refers to the same coefficient module.
- Mathlib `CategoryTheory.Functor.mapDerivedCategory` and
  `mapDerivedCategorySingleFunctor`, from
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, and upstream
  `AlgebraicGeometry.Etale.upperStarComp`, from
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, give the canonical data.
  Their full signatures, directions and docstrings were read. The published
  `preservesHomology_upperStar` supplies exact inverse image. Recorded modules
  of already stated proof dependencies are imported without `public`; no
  independent replacement notion or dependency module is introduced.

Searches retained from the first delivery and repeated for the repair:

- `msearch.py ... leanfinder "Ext continuity for constructible etale module sheaves
  over affine inverse limits"`: no matching theorem (generic condensed objects
  and affine-limit section lemmas).
- `msearch.py ... loogle "DerivedCategory, upperStar, Ext"`: no hits; `upperStar`
  unknown to that index.
- Repair `msearch.py ... leanfinder "Canonical exact inverse image maps on Ext of
  etale module sheaves commute with composition and affine inverse limits"`:
  eight unrelated cotangent-complex/ring-etale hits, no matching declaration.
- Repair `msearch.py ... loogle '"mapDerivedCategorySingleFunctor"'`: eleven
  exact-functor API hits, including the single-functor comparison and composition
  comparison lemmas; these APIs are used, not redefined.
- `msearch.py ... grep "constructible.*etale.*Ext|Ext.*colimit" Mathlib`: no hits,
  repeated in the repair with the same result.
- `rg` for `constructible.*etale.*Ext|ext.*continuity|Ext.*colimit` over upstream
  `WeilConjectures/` and shared `lean/Sheaf`: only unrelated general/condensed
  Ext and colimit infrastructure, no theorem for these etale inverse limits.
- `rg` for the exact node id over upstream `WeilConjectures/`: no declaration.
  Searches for the new helper names found no existing occurrence.

Edge cases checked: singleton directed sets are allowed; preorders need not be
antisymmetric; the two representatives may come from distinct or identical stages;
`n = 0` gives ordinary Hom descent; all positive degrees use the correct negative
single-complex degree; zero sheaves, the zero ring, and empty schemes are allowed.
The finite-field tower example from the return no longer asserts that Ext at the
initial stage equals Ext at the limit: classes may die or appear only after further
transition, exactly as expressed by the representative clauses. The singleton case
reduces to the canonical equivalence attached to the limit projection.

Every definition has real data. The postponed proofs are precisely the main theorem
and the three named compatibility theorems, each owned by this same DAG statement
and carrying a natural-language proof. No mathematical node statement was changed;
there is no `statement_change` and no disputed statement.

## Second reading by Q58

A separate self-review pass, not a second agent (the dispatcher prohibits spawning),
read the node, the repaired file and the return side by side. It checked all hypotheses
and each conclusion above. The old free-map hypotheses are absent; inspecting the
bodies traces each new map to `mapDerivedCategory.map`. The single-complex comparisons
have the correct directions, and the shift convention is now `-n`. The limit leg uses
`(c.w ...).symm`, while the transition uses `D.map_comp`, so both compare the prescribed
composite inverse image rather than an arbitrary isomorphism. The second representative
clause uses a common upper bound for two arbitrary stages. The composition and
later-stage compatibility conclusions are explicit named theorems, not prose claims.
No hollow quasi-separatedness condition remains, and the convention-node id is fixed.
No changes outside the item's `lean` record are required.

Validation: the final file passed `scompile.py Q58
lem-trf-constructible-etale-ext-continuity` cleanly in both the sandbox and actual
library module-name checks (exit 0, no errors or warnings). Source checks confirmed
that `lean.statement` is the exact multiline main signature, all nine declarations
are recorded, all lines meet the 100-character bound, and precisely the four named
theorems have `sorry` proofs.

The first repaired dry run hit a confirmed 60-second timeout. The Hom type helper
was changed from an eagerly expanded `abbrev` to a `def` with explicit result
universe, reducing expansion while preserving its exact Hom type. A sandbox-only
profiling copy compiled both ways; the main theorem elaborated in under 0.1 seconds
and the final module linter accounted for about 24 seconds. The profiling option
is absent from the delivered module. The unchanged 60-second wrapper is used for
the final checks.
The final non-profiling file then passed `scompile.py` with exit 0 and no warnings:
sandbox check 32.8 seconds, actual library-name check 36.6 seconds.
