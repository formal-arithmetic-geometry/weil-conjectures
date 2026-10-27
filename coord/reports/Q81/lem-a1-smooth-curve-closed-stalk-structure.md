## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.SmoothCurveClosedStalkStructure` states
`AlgebraicGeometry.smooth_curve_closed_stalk_structure`, with exactly one postponed
proof (`sorry`). No definitions, new nodes, dependency repairs or statement corrections
are needed. The item node is changed only in `lean`.

Source read: Stacks Project, `curves.tex`, Tag 0C1E, label
`lemma-uniformizer-works`, including its proof. The first sentence gives the DVR
property and the last sentence uses rank-one differentials. Separability is used only
in the intervening assertion that the differential of a uniformizer is nonzero, which
is outside this item's statement. Also read the current blueprint's
`sec-deligne-laumon-a1/sk-lem-wft-finite-map/lem-a1-finite-map-curve.md`.

Hypothesis and conclusion correspondence:

- A field k: `(k : Type u) [Field k]`.
- A k-scheme X and its structure map: `(X : Scheme.{u}) (f : X ⟶ Spec (.of k))`.
- Separated, integral, finite type, dimension one: `[IsIntegralCurve f]`, whose
  `IsVariety` parent extends `IsSeparated f`, `LocallyOfFiniteType f` and
  `QuasiCompact f` and supplies `IsIntegral X`; its dimension field is
  `topologicalKrullDim X = 1`. The recorded dimension comparison identifies this
  with the local-ring-supremum convention.
- Smooth over k: `[Smooth f]`.
- A closed point x: `(x : X) (hx : IsClosed ({x} : Set X))`.
- A is the actual stalk: every occurrence of A is `X.presheaf.stalk x`.
- Dimension of A is one: `ringKrullDim (X.presheaf.stalk x) = 1`.
- Every open neighbourhood has dimension one:
  `∀ N : X.Opens, x ∈ N → topologicalKrullDim N = 1`.
- Dimension at x is one: `topologicalKrullDimAt x = 1`.
- Regular local: `IsRegularLocalRing (X.presheaf.stalk x)`.
- Noetherian: `IsNoetherianRing (X.presheaf.stalk x)`.
- Discrete valuation ring: `IsDiscreteValuationRing (X.presheaf.stalk x)`;
  integrality supplies its implicit domain instance.
- Free rank-one differentials, with an A-linear isomorphism A to Ω:
  `Nonempty ((X.presheaf.stalk x) ≃ₗ[X.presheaf.stalk x] @KaehlerDifferential ...)`.
  `Nonempty` expresses existence of the specified linear isomorphism. The explicitly
  supplied algebra is `(((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
  X.presheaf.germ ⊤ x trivial).hom.toAlgebra)`: the canonical identification of k
  with global sections of Spec k, pullback along f, then the germ at x.
  Thus this is Ω for the structure-map algebra, with no arbitrary algebra binder.
- No separability assumption: no residue-field, perfection, or separability binder
  is present. Neither conclusion specifies the differential of a uniformizer.

Recorded dependency declarations read and used:

- `def-pc-curve`: `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`,
  `AlgebraicGeometry.IsVariety` and `AlgebraicGeometry.IsIntegralCurve`; read their
  full signatures, parent classes, dimension field and docstrings.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`; also read `SmoothOfRelativeDimension` for the rank
  interpretation. Only `Smooth` is an assumption of this theorem.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim : WithBot ℕ∞`.
- `def-kun-dimension`: `WeilConjectures.Mathlib.Topology.KrullDimension`,
  `topologicalKrullDimAt` (infimum over open neighbourhoods) and the existing
  `topologicalKrullDim`.
- `def-weil-regular-scheme`: import its recorded
  `Sheaf.AlgebraicGeometry.IsRegularScheme`. Its `AlgebraicGeometry.IsRegularScheme`
  is the locally Noetherian plus stalkwise regular scheme notion; the present node
  uses this dependency's ring clause, Mathlib's `IsRegularLocalRing`, whose full
  declaration in `Mathlib.RingTheory.RegularLocalRing.Defs` extends both
  `IsLocalRing` and `IsNoetherianRing`. No scheme regularity assumption is introduced.
- `def-sc-discrete-valuation-ring`: its Mathlib match,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic.IsDiscreteValuationRing` (global
  declaration name `IsDiscreteValuationRing`), the local PID domain with nonzero
  maximal ideal. No dependency Lean record is needed for this Mathlib leaf.
- `def-weil-pbc-kahler-differentials`: `Mathlib.RingTheory.Kaehler.Basic`,
  `KaehlerDifferential`, `KaehlerDifferential.D`, and
  `KaehlerDifferential.linearMapEquivDerivation`; the full construction and universal
  property were read. The statement uses the existing differential module.

Proof-dependency imports are included without `public`: the dimension comparison
module, Mathlib scheme properties, affine smoothness ring-hom interface and affine
stalk localization modules, `Sheaf.RingTheory.SmoothOverFieldRegularLocal`,
`WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`,
`Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension`, and
`Mathlib.RingTheory.Etale.Kaehler`. The other proof dependencies are supplied by
statement imports or those Mathlib modules. The declaration docstring reproduces
all four DAG proof steps and their named inputs, including the explicit localization
isomorphism and its inverse in the final step.

Edge cases checked before writing:

- The empty scheme and zero stalk cannot satisfy the integral-curve/point hypotheses;
  no extraneous nonemptiness assumption is added.
- The generic point is not closed on a dimension-one integral scheme. Without the
  closed-point hypothesis its stalk would be the function field of dimension zero;
  the closed-point binder is therefore essential.
- An empty open is excluded only by `x ∈ N`; the whole space is allowed. Opens are
  arbitrary open neighbourhoods, not just affine ones.
- No projectivity, properness, geometric integrality, algebraic closedness or perfect
  base field is assumed. The affine line and nonproper curves remain included.
- In characteristic p over k = F_p(s), the closed point `(T^p - s)` of the smooth
  affine line has inseparable residue field. Its localized differential module is
  still free on dT, while d(T^p - s) = 0. The conclusion correctly asserts existence
  of a basis, rather than asserting that every uniformizer differentiates to one.
- Dimension values are `WithBot ℕ∞`, retaining both standard dimension conventions.
  All type variables and the universe u are explicit; `autoImplicit` is disabled.

Searches actually run (all through `msearch.py` except the direct source searches):

- LeanFinder: "At a closed point of a smooth integral curve the local ring is regular
  dimension one a discrete valuation ring and its Kahler differential module is free
  of rank one". Eight hits: DVR cotangent-space criteria and standard-smooth
  differential results; none states all the scheme-level clauses here.
- Loogle: `AlgebraicGeometry.IsIntegralCurve, IsDiscreteValuationRing`. Reported the
  project-specific `IsIntegralCurve` identifier unknown; this is not evidence of a
  Mathlib exact match. Repeated with Mathlib names
  `AlgebraicGeometry.Smooth, IsDiscreteValuationRing`: zero hits.
- Grep: `(stalk|localRing).*(isDiscreteValuationRing|kaehler|Kaehler)|IsIntegralCurve.*Smooth`.
  Two Mathlib hits, in Smooth/Local and DiscreteValuationRing/TFAE; neither is this
  statement.
- LeanSearch: "A smooth integral curve at a closed point has a dimension one regular
  DVR local ring and free rank one Kahler differentials". Eight hits, including
  manifold integral curves and separate standard-smooth differential/DVR criteria;
  no combined algebraic-geometric statement.
- `rg` over the project's `WeilConjectures/AlgebraicGeometry` and
  `Sheaf/AlgebraicGeometry` for `IsIntegralCurve`, closed stalks, and stalk algebras;
  read `Curve/UniformizerDifferentialBasis.lean` and
  `Curve/NormalSeparablePointSmooth.lean`. The former assumes finite separable residue
  field and concludes a fact about the differential of a uniformizer; the latter
  assumes normality and finite separability. Neither is the item.
- Direct `grep -rn` for the item id in `lean/WeilConjectures` found no match.
- Direct `rg` for `smooth_curve_closed_stalk_structure`, smooth-curve-stalk phrases
  and curve-stalk-structure phrases in Mathlib, both project roots and
  `dag/lean_names_upstream.json` found no existing declaration with this name or
  exact statement. Search transcripts are in the sandbox's `searches.jsonl`.

Validation: `scompile.py Q81 lem-a1-smooth-curve-closed-stalk-structure` accepted the
single delivered module against the server library with exit code zero and no errors
or warnings. The node's `lean.statement` is extracted verbatim from the theorem
signature before `:=`; JSON uses indent one, Unicode, and a final newline.

No node fault or statement dispute was found. The maintainer supplies the independent
review; no independent second reading is claimed here.

## Second reading by Q81

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
