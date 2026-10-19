## Worker report

The module `Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual` states
`AlgebraicGeometry.WeilSheaf.punctualWeights_lowerStar_of_isFinite`, with `sorry` as
its sole proof. It states both punctual preservation assertions in one conjunction;
neither implication assumes the antecedent of the other. No definition is introduced.
The node statement, dependencies, proof and source are unchanged.

Hypothesis and clause correspondence:

- A finite field is `{k₀ : Type u} [Field k₀] [Finite k₀]`. The coefficient prime
  is `{l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]`, as in the recorded
  weight declarations. This is the finite-field convention of
  `def-weil-finite-field-fiber`, with the existing canonical algebraic closures
  used by the upstream sheaf implementation; no particular finite field or
  extension degree is selected. Every finite field has prime-power cardinality.
- The schemes are `{X₀ Y₀ : Scheme.{u}}`, each equipped with `Over (Spec k₀)`.
  For EACH structure morphism the statement explicitly retains
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`: finite type and
  separatedness, exactly as the node requires.
- The finite morphism over the finite field is `(f₀ : X₀ ⟶ Y₀)` with
  `[f₀.IsOver (Spec k₀)] [IsFinite f₀]`. Finite uses the recorded Mathlib
  `AlgebraicGeometry.IsFinite`, not a custom property or finite étale variant.
- The constructible algebraically closed coefficient Weil sheaf is
  `(G : WeilSheaf k₀ l X₀)`. This is the existing upstream full category of
  constructible pro-etale coefficient sheaves on the geometric fibre with
  Frobenius isomorphism. Constructibility and the Weil structure are part of
  the object, not additional free predicates. The theorem uses only sheaves;
  it does not use the upstream derived category of Weil sheaves that the
  recorded `SfWeilSheafComplex` repair excludes. The sibling
  `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` uses this same sheaf interface
  and imports both recorded side-library modules.
- The chosen coefficient-field isomorphism is `(ι : PadicAlgCl l ≃+* ℂ)`;
  `ι.toRingHom` is passed to the recorded weight predicates. The real weight
  is `(w : ℝ)`, without integrality or sign restriction.
- The canonical direct image is `((lowerStar f₀).obj G)`, the already constructed
  upstream functor: it pushes forward on the geometric fibre and transports
  Frobenius canonically. There is no arbitrary output sheaf or map parameter.
- The first conjunct is `G.HasWeightsAtMost ι.toRingHom w →
  ((lowerStar f₀).obj G).HasWeightsAtMost ι.toRingHom w`. Reading the full
  definition in `WeilSheaf/Stalk.lean`, this quantifies over all finite/closed
  points and imposes the local Frobenius eigenvalue inequality, rather than
  requiring a mixed filtration. For finite-type schemes over a finite field,
  finite points are precisely the closed points.
- The second conjunct is `G.IsPunctuallyPureOfWeight ι.toRingHom w →
  ((lowerStar f₀).obj G).IsPunctuallyPureOfWeight ι.toRingHom w`, using exactly
  the recorded equality predicate with the same weight. It has no extra
  upper-bound premise.

Dependency declarations and source inspection:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, including
  its real fields and `geometricFiber`; reached through `SfWeilSheafComplex`.
  The theorem uses the same convention in unbundled upstream sheaf parameters.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`,
  an affine morphism with finite maps on affine open sections. The dependency
  also records `IsIntegralHom`, which is not needed by this statement.
- `def-weil-scheme-morphism-properties` is explicitly a convention record,
  fixing no additional declaration. Its finite-type/separated conventions are
  the standard `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` classes.
- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalHeart`, `sfCommonStageHeart`,
  and their degree-zero full-subcategory properties. Its full current module
  and standard-class definitions were read; imported via `SfWeilSheafComplex`.
- `WeilConjectures.DeligneLaumon.Reduction.Weights`: the recorded
  `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost` and
  `IsPunctuallyPureOfWeight`; the latter and `HasWeightsAtMost` are defined in
  the publicly imported `WeilConjectures.WeilSheaf.Stalk`. The mixed predicate
  is deliberately not substituted for the node's eigenvalue bound.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`, `sfWeilSheaf`,
  `sfCommonStageWeilComplex`, `sfCommonStageWeilSheaf`, and their full
  signatures/docstrings were read. The current fixed-pair complex convention
  is imported; no assertion about the alternative upstream Weil complexes is
  made. The already existing upstream Weil SHEAF realization is used directly,
  as in `FiniteMapPurity`, without defining a second category.
- `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage`,
  `sfCompletedModuleDirectImage`, `sfCompletedDerivedDirectImage`, and the
  canonically normalized tower/comparison constructions. The full source was
  inspected. This recorded definition is imported, while the requested ordinary
  sheaf-level direct image uses `WeilConjectures.WeilSheaf.LowerStar.lowerStar`.
  No arbitrary derived-direct-image presentation is assumed.
- The proof dependencies `lem-zl-finite-adic-direct-image` and
  `lem-a1-finite-weil-sections-decomposition` have no Lean records on the read
  base and supply no imported modules. Their full statements and the node's
  four proof steps were read. They are named explicitly in the proof docstring.
  They are proof prerequisites, not unstated notions needed in this signature.

Edge cases: empty schemes, empty fibres, and zero sheaves/stalks are admitted;
weight conditions quantify over eigenvalues, hence are vacuous when none occur.
Finite radicial and nonreduced morphisms are included. A positive residue degree
is used only in the natural-language proof, never imposed as an extra parameter.
All real weights, including negative weights and zero, are admitted. No lissity,
connectedness, smoothness, diagonalizability, or surjectivity is assumed.
The common universe `u` for the schemes and base field follows the existing
upstream `WeilSheaf` interface and does not restrict geometric cases: the entire
finite diagram can be placed in any containing universe. The coefficient algebraic
closure is the existing `PadicAlgCl`, with the requested isomorphism explicit.

Searches made before writing:

- `msearch.py`, LeanFinder: "finite pushforward preserves punctual purity and
  local Frobenius upper weight bounds for constructible Weil sheaves". Eight
  generic results on module pushforward, constructible images, Witt vectors,
  and ring-theoretic Frobenius; none states the requested theorem.
- `msearch.py`, Loogle: `WeilSheaf.lowerStar, WeilSheaf.HasWeightsAtMost,
  WeilSheaf.IsPunctuallyPureOfWeight`. Zero hits; the service reports unknown
  identifier `WeilSheaf.lowerStar` (the project-specific declaration was then
  found and read directly in the upstream source).
- `msearch.py`, grep of Mathlib: `finite.*pushforward|[Pp]unctually[Pp]ure|HasWeightsAtMost`.
  Two unrelated hits, locally finitely supported pushforward and Dedekind ideals.
- `msearch.py`, LeanSearch: "finite pushforward of a Weil sheaf preserves upper
  bounds on local Frobenius weights and punctual purity". Eight generic sheaf
  pushforward and finite-limit results; no Weil weight theorem.
- Direct `rg` of `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the node id, finite pushforward, punctual purity, `HasWeightsAtMost`, and
  `lowerStar_of_isFinite` found the definitions above, the quasi-finite
  compact-support upper-bound theorem, and
  `IsPunctuallyPureOfWeight.lowerStar_of_isFinite` in the published upstream
  `DeligneLaumon/Reduction/FiniteDirectImage.lean`. The last supplies only the
  purity clause, not the conjunction requested by this node. Its signature and
  docstring were read; it is not an exact existing attachment for the whole item.
- The side-library sibling `FiniteMapPurity.lean` states only purity for finite
  ETALE morphisms, so it is not this statement. The new full declaration name
  was searched in Mathlib, upstream `WeilConjectures`, and `lean/Sheaf`: no hit.

No statement correction, disputed statement, new node, or dependency replacement
is needed. The only newly postponed theorem is the item's own declaration.

Validation: `scompile.py` passed the delivered module in both sandbox and library
positions, with no errors or warnings (2026-10-17 UTC). The delivery dry run and
preflight use `deliver2.py --no-push`; the final delivery repeats its checks. The
maintainer supplies the independent review after delivery, as required by the
dispatch brief.

## Second reading by Q71

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
