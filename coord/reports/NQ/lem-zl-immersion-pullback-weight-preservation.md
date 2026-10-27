## Worker report

States `WeilConjectures.zlImmersionPullbackWeightPreservation` in
`Sheaf.Paper.ZlImmersionPullbackWeightPreservation`, with precisely the two
assertions of the node as the two conjuncts. Its only proof is `sorry`.
No definitions, auxiliary theorems, or new nodes are introduced.

Source read: the current main-20261015 blueprint,
`sec-deligne-laumon-general/sk-l-dl-general-excision/lem-zl-morphism-open-closed-reduction.proof.md`,
the complete Restriction paragraph. The docstring gives all three DAG proof steps:
intertwining preserves eigenvalues and punctual purity; exact pullback restricts
the finite filtration; the Weil cohomology comparison gives every degree w+a.
It includes the cited point-transport naturality and composition argument for
invariance under Weil isomorphism.

Hypothesis and clause correspondence:

- Finite field k₀ of characteristic p, q=p^a, and its chosen algebraic closure k:
  `(D : FiniteFieldDatum.{u})`. The existing geometric-fibre and Frobenius
  constructions in the imported declarations use this fixed datum.
- Prime l distinct from p: `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
- Algebraic closure Qbar of Q_l: `(Qbar : Type v) [Field Qbar]
  [Algebra (Padic l) Qbar] [IsAlgClosure (Padic l) Qbar]`.
  The coefficient universe v is independent of the scheme universe u.
- Specified field isomorphism iota: `(iota : Qbar ≃+* ℂ)`;
  `iota.toRingHom` supplies the recorded predicates. This retains surjectivity
  in the hypothesis; the predicates themselves only need its ring homomorphism.
- Separated finite-type k₀-schemes: `(W₀ X₀ : Over (Spec (.of D.k₀)))`,
  with `[LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
  [IsSeparated W₀.hom]` and the same three instances for X₀.
  Locally finite type together with quasi-compact is finite type.
- Morphism over k₀: `(h₀ : W₀ ⟶ X₀)` in the over category.
- Locally closed immersion: `[IsImmersion h₀.left]`. Mathlib's
  `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists` is exactly factorization
  as a closed immersion followed by an open immersion; its signature and
  docstring were read, as were both recorded immersion classes.
- Base change h to k: `zlFiberMap D h₀`, inside `zlPull`; this is literally
  the map of `Over.pullback` along Spec(k) → Spec(k₀).
- Induced Weil structure: `zlFrobeniusSquare D l hl Qbar h₀`, formed from
  normalized composition comparisons and Frobenius naturality. Its induced
  fixed-pair pullback is `IsoAlgebra.mapOfNatIso` of that square.
- Bound: `(w : ℝ)`; no positivity or integrality assumption.
- Assertion 1: for every `F : sfCommonStageWeilSheaf D l hl X₀ Qbar`,
  `SfIsMixedOfWeightsAtMost ... X₀ iota.toRingHom F w` implies the same predicate
  on W₀ for `((zlWeilPull D l hl Qbar h₀).obj F)`.
  The latter is the existing full-heart restriction of that same induced Weil
  pullback, not an independently supplied exact functor.
- Assertion 2: for every `K : sfCommonStageWeilComplex D l hl X₀ Qbar`,
  `SfComplexIsMixedOfWeightsAtMost ... X₀ iota.toRingHom K w` implies the same
  predicate on W₀ for the induced fixed-pair pullback. Its definition says
  exactly `∀ b : ℤ, SfIsMixedOfWeightsAtMost ... (H^b K) (w + (b : ℝ))`.
- Repeated filtration terms: the existing mixed predicate requires `Mono`, not
  proper inclusions, and allows m=0. No strictness is introduced in this theorem.

Dependency declarations used and read:

- `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageHeartProperty`, the two
  standard degree-zero classes and their full heart.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilComplex`,
  `sfCommonStageWeilSheaf`, `sfCommonStageWeilFrobeniusPullback`,
  `sfWeilPrimeInvertible`. These are the recorded fixed-pair categories;
  invertibility of l on the geometric fibre is derived, not an added hypothesis.
- `Sheaf.Paper.AdicPunctualWeights`: `SfPunctualEigenvalue`,
  `SfIsPunctuallyPureOfWeight`, `SfIsMixedOfWeightsAtMost`. The local operators
  are the recorded finite-stage ones, scalar-extended to the algebraic closure.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`:
  `AlgebraicGeometry.IsImmersion` and `IsImmersion.isImmersion_iff_exists`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `commonStageDerivedPullback`,
  specified uniquely by its actual finite-stage object and morphism formulas.
- `Sheaf.Paper.WeilMixedUpperBounds`: `sfWeilCohomology`,
  `SfComplexIsMixedOfWeightsAtMost`; cohomology uses the normalized Frobenius
  truncation and shift comparisons.
- `Sheaf.Paper.WeilIndSheafCategory`: `zlFiberMap`, `zlPull`,
  `zlPullComp`, `zlFrobeniusSquare`, `zlWeilPull`. No ind-category occurs
  in the theorem: this module owns the required existing heart pullback too.

The two last modules belong respectively to the already-landed nodes
`sk-d-dl-general-weights` and `def-zl-weil-ind-sheaf-category`; these ids are
added to stmt_deps under the explicit permission to cite landed nodes.
The original stmt_deps are retained. `def-weil-complex-weights` has no lean
record; its closed upstream audit names only the upper half in the different
upstream Weil category. I read that signature and its warning that the lower
half is not supplied. For the exact upper notion needed here, the project
already has `SfComplexIsMixedOfWeightsAtMost` under the landed general-weights
node, so I use it directly and do not duplicate the definition or misattach a
full upper/lower/purity node to an upper-only declaration. The present theorem
has no lower-weight or duality assertion.

All stated proof dependencies are plain imports:
`Sheaf.Paper.ZlImmersionWeilLocalBehavior` (`zlImmersionWeilLocalBehavior`,
its normalized `ZlImmersionPullback` and `ZlWeilExactOperation` clauses),
`Sheaf.Paper.LocalFrobeniusTrace` (the finite and common-stage local operators),
`Sheaf.Paper.IntegralPullbackComposition` (`integralPullbackComposition`), and
`Sheaf.SixFunctors.FrobeniusPointTransportNatural`
(`frobeniusPointTransport_natural`). Punctual and complex weight definitions
are public imports because the statement uses them too.

Edge cases checked against the statement and these definitions: identity, open,
closed and general locally closed immersions; empty W₀ or X₀; zero sheaf and
zero complex; a sheaf supported outside W₀; zero stalks; a filtration quotient
annihilated by restriction; coincident consecutive terms; m=0; negative and
nonintegral w; every integer cohomological degree including zero and negative
degrees. No connectedness, nonemptiness, smoothness, lisse, stable lattice or
extra coefficient-size equality is assumed.

Searches actually run:

- msearch leanfinder: `Pullback along a locally closed immersion preserves mixed
  upper weights of constructible Weil sheaves and complexes` → 8 hits,
  including scheme module pullback/restriction and sheaf-of-modules composition;
  none states Weil weight preservation.
- msearch loogle: `"IsMixedOfWeightsAtMost", "upperStar"` → 0 hits.
- msearch grep: `SfIsMixedOfWeightsAtMost|IsMixedOfWeightsAtMost.*upperStar`
  → 0 Mathlib hits.
- msearch leansearch: `Restriction of a constructible Weil sheaf along a locally
  closed immersion preserves mixed upper weights` → 8 hits about scheme
  restriction and structure-module sections, none an exact match.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for mixed-weight predicates,
  immersion/weight combinations and the proposed declaration name; the node-id
  search in upstream had no hit. `dag/lean_names_upstream.json` was searched too.
  Upstream `WeilSheaf.IsMixedOfWeightsAtMost.upperStar` and
  `WeilComplex.IsMixedOfWeightsAtMost.upperStar` were found and their signatures
  and docstrings read in `DeligneLaumon/Reduction/FormalSteps.lean`. They use
  the distinct upstream coefficient/derived-of-pairs model, not the node's
  actual common-stage fixed-pair model, so no exact existing attachment.
  Existing project definitions were reused as listed above.

No mathematical statement correction and no STATEMENT-DISPUTED flag.
The unavailable server source query for the unused
`Sheaf.SixFunctors.CoefVerdierWeilEquivariance` did not affect the statement:
only the already-existing upper bound is needed, not Verdier duality.

Validation: prescribed scompile.py compiled the module both as a sandbox file
and at its library module path with exit 0, no errors or unexpected warnings.
The prescribed deliver2.py --no-push dry run passed the server preflight and
per-file compiles: OK, temporary commit 9c539215a2e. Final delivery follows.

## Second reading by NQ

Worker self-check, not a claim of independent review: reopened the node and
module, matched each binder and both conjuncts as above, and checked the
filtration definition only requires Mono and permits zero length. The canonical
sheaf and complex pullbacks use the same normalized Frobenius square. All
universes and variables are explicitly bound with autoImplicit false. The
original mathematical statement is unchanged. The dispatcher brief assigns the
independent reading to the maintainer's delivery review and prohibits starting
another agent.
