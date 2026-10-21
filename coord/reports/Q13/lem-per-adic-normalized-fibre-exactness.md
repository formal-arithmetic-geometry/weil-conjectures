## Worker report

The module `Sheaf.Paper.AdicNormalizedFibreExactness` states
`AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre.adic_normalized_fibre_exactness`
with its entire mathematical proof postponed by `sorry`. All helper definitions contain real
constructions or explicitly specified data. There is no statement correction, new node or
dependency repair. Namespace below: `AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre`.

Hypotheses and background:

- The section binders `(l : ℕ) [Fact l.Prime]` and `(E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` give the prime and arbitrary finite coefficient
  extension. The given algebraic closure and intermediate L are background for scalar functors
  and the pair category; the node asserts no scalar-extension or Qbar comparison of its fibres.
  Quantifying every finite E states the finite-stage assertion without restricting to a model
  of that algebraic closure.
- The theorem binds `k`, its field structure, `X.scheme.Over (Spec (.of k))`,
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on its structure morphism and
  `IsUnit (l : k)`. These are precisely a separated scheme of finite type over the given field
  with l invertible. `X : ContinuousRational.Base l` packages the noetherianity, dimension bound
  and stalk invertibility already required to name the raw category. For these finite-type
  schemes they are consequences, so this encoding excludes no allowed X, including empty X.
- The parameter `R : ContinuousRational.Family l` is the compatible normalized realization of
  the dependency. Its existence is `continuous_rational_derived_realization`; the theorem
  works for the supplied compatible realization rather than selecting a new independent J.
- `Heart l E X` is literally `(localizedT l E X).heart.FullSubcategory`; `localizedT` is the
  recorded bounded localized standard t-structure on `PbcRationalCategory`, the raw scalar
  localization. `realize` is inclusion into that category, followed by `J` and H⁰. This is
  the sheaf realization of the heart specified by the dependency's `heart` and `t_bounds`.
- The completed coefficient and localized continuous sheaves are the existing
  `integralCoefficientSheaf` and `rationalCoefficientSheaf`, identified with completion and
  localization by `At.integralIso` and `At.localizationIso`. Their definitions have not changed.
  No pointwise-discrete E sheaf or Karoubi envelope is introduced.

Conclusions and their Lean rendering:

- `Assertions.point` quantifies every `(κ : Type u) [Field κ] [IsAlgClosed κ]` and scheme map
  `x : Spec (.of κ) ⟶ X.scheme`. `Point.functor` is additive and E-linear. Its codomain is
  `ModuleCat.{u+1} E`, with `Point.finite` asserting finite dimensionality on every object;
  this is the customary full-category encoding of Vect_fd(E), retaining its actual maps.
- `Point.intrinsic` is a natural isomorphism with `omega`. Its construction is `realize`, then
  `modulePull` along the geometric point using `coefficient`, then final-object evaluation,
  then restriction along `pointConstants`. The coefficient map is the existing adjoint of
  precomposition of continuous functions. Thus the construction is independent of all charts.
- `Chart` uses the recorded `FiniteLocallyClosedStratification`, one stratum, and an affine
  etale scheme over it. `Chart.Adapted` means the realized sheaf is finite locally free on
  every stratum. `Assertions.local_chart` supplies such a chart, the geometric lift, a local
  integral lattice, and the rational realization isomorphism. It requires no global lisse
  integral model of F.
- `Lattice` retains the actual continuous integral sheaf and its finite local freeness; its
  `system` is `AdicIntegralDiagramOfUniverses`. Its `lisse` condition is the dependency's
  normalized lisse-system predicate; `finiteFree` states exactly finite free geometric stalks
  over A/(ϖ^(n+1)). `reduction`, `complete`, `quotient` and `scalar` specify the actual quotient
  maps, inverse-limit universal property, scalar cokernels and integral action. This prevents
  an unrelated tower from serving as the normalized reduction of the lattice.
- `Lattice.fiber` is exactly `adicIntegralFiberOfUniverses`, the inverse limit of etale module
  stalks, and `Lattice.rationalFiber` is balanced extension of scalars along A ↪ E. The source
  writes M tensor_A E; ModuleCat uses E tensor_A M, canonically equivalent by tensor symmetry.
  `Assertions.integral_finite_free` states both Module.Finite and Module.Free of that limit.
  `Assertions.normalization` supplies the displayed E-linear fibre isomorphism on every
  adapted chart and every lattice presentation.
- `Represents` compares every reduction square of the actual integral map with the specified
  system map. `rationalLimitMap` applies `limMap` to the stalk natural transformation and
  then balanced localization. `Assertions.fractions` states the exact conjugacy square:
  if the chart restriction of f is u/ϖ^b, its fibre is ϖ^(-b) times that inverse-limit map.
  It quantifies all representatives and b, so equal fractions cannot produce different maps.
- Naturality in F is the functor and natural intrinsic isomorphism; the fractions equation
  supplies naturality of the local identifications on integral maps and their fractions.
  Every normalization compares to the same point functor. Comparisons between two choices
  are the inverse of one normalization followed by the other (transport along the chart's
  point equality when needed). These have the cocycle by cancellation. Thus choice changes
  of stratification, chart and lattice give the asserted comparison isomorphisms without
  selecting globally compatible lattices. The source proof's chart refinements and local
  fraction presentations explain how those comparisons calculate on local maps.
- `Point.exact` sends every `ShortComplex` that is short exact after `realize` to a short
  exact fibre sequence. Exactness is therefore the inherited ambient continuous-module
  exact structure, not a separately postulated exact structure on the raw category.
- `Assertions.detects_zero`, `detects_iso`, and `detects_zero_map` give exactly the joint
  detection assertions for objects and maps. `detects_exact` is middle exactness of every
  short complex iff all its fibres are exact. `detects_short_exact` includes the endpoint
  kernel/cokernel conditions and is the final in-particular equivalence in the node.

Dependency declarations used (read with their signatures and source docstrings):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: reexports
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer` and the positive
  coefficient quotient construction; adds `finite_coefficientExtensionRing`.
- `Sheaf.Paper.AdicCoefficientDatum`: actual completed coefficient and module categories,
  reexported through the realization; `completedReductionTower` is not redefined.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.mk`.
- `Sheaf.Paper.IntegralUniformCoefficient` / `BoundedConstructibleComplete`:
  `PbcBoundedConstructibleComplete` inside the raw category, retaining all three membership
  conditions and compatible origin witnesses. The convenience unlifted u+1 specialization
  is not needed when E is in u: the realization already uses `pbcIntegralDatum` with ULift A.
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`, `pbcRationalization`.
- `Sheaf.Paper.LocalizedTStructure`: `pbc_localized_tstructure`, via `localizedT`.
- `Sheaf.Paper.PbcScalarExtension`: the canonical E-linear structure of the raw category.
  The `pbcCoherentScalarExtension` and `intrinsicPbcQbarCategory` background of the node adds
  no assertion or parameter to this purely finite-stage fibre theorem.
- `Sheaf.Paper.ContinuousRationalDerivedRealization`: `Base`, `At`, `Family`, `localizedT`,
  `scalarSections`, `modulePull`, `At.J`, and `continuous_rational_derived_realization`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification` (no extra constructibility hypothesis).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points follow the
  recorded inline convention of `Scheme.SpecToEquivOfField`.
- `Sheaf.Paper.LisseIntegralSmallCoefficients`: `AdicIntegralDiagramOfUniverses`,
  `IsLisseIntegralDiagramOfUniverses`, `adicIntegralFiberOfUniverses`.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientPullback`: actual normalized continuous
  coefficient maps and `integralRationalCoefficientMap`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `supportSiteComparisonCoefficientPullback` for the etale-origin reductions.
- The published proof-dependency modules are imported without `public`; their constructions
  are the plan recorded in the theorem docstring, not hypotheses of the statement.

Edge cases checked: X empty permits empty stratification and no geometric points, so its zero
module category satisfies the detection assertions; no Nonempty X is imposed. Rank zero is
allowed in `finiteFree` and in the finite free integral limit. Index n=0 is exponent one,
never the zero quotient A/(1); all positive levels are included. Denominator b=0 gives an
ordinary integral map. Zero integral maps, equal fractional representatives, identity chart
maps and arbitrary finite coefficient fields are included. No constant-rank assumption across
strata, connectedness, smoothness or global lattice hypothesis is imposed. Sites retain object
universe u+1 and morphism universe u; modules and vectors are in u+1, fields and schemes in u.
The geometric-point universe follows the recorded `SpecToEquivOfField` / lisse-system convention.

Searches:

- `msearch.py ... leanfinder "Normalized local lattice fibres are exact and jointly detect zero
  objects isomorphisms zero morphisms and short exact sequences of constructible continuous
  adic module sheaves"`: eight hits, for condensed AB properties and module localization
  exactness; none is the constructible rational-heart normalized fibre assertion.
- `msearch.py ... loogle "Functor.Linear, ShortComplex.ShortExact, ModuleCat"`: no hit; the
  endpoint did not resolve unqualified Functor.Linear. Source searches located the actual
  existing `Functor.Linear`, `ShortComplex.ShortExact` and ModuleCat APIs; they are reused.
- `msearch.py ... grep "ShortExact|FiniteDimensional|sheafFiber" CategoryTheory/Abelian`:
  25 hits, including the generic exact functor/short exact API. These do not construct an
  adic heart fibre or establish the normalization or joint detection.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`, together
  with the requested item-id search in WeilConjectures, found no existing declaration for
  this item. The upstream Adic/LisseRankCriterion fibre is an integral adic sheaf fibre,
  not the raw-rational heart with locally defined continuous lattices and ambient exactness.
  The nearby PointFibreDerivedTensor statement is in a finite-field six-functor context.
- Read the recorded source declarations rather than copying their notions. The former
  CompactObject example is now explicitly withdrawn in the shared clone; the active modules
  above give the same header, module-system and source/blueprint docstring conventions.

Validation: the complete delivery module compiled via the prescribed `scompile.py` against the
live server in sandbox and library modes (14.9s and 12.8s), with no errors or warnings.
Every variable and universe is explicitly bound; there is one postponed theorem and its
seven-step natural-language proof is in its docstring. Dry-run and delivery results follow.

## Second reading by Q13

Performed an in-thread second reading of the node statement and entire file; no independent
worker was spawned, as the dispatch brief forbids other agents and assigns independent review
to the maintainer. Checked that the heart is the raw localization's full heart, the module
fibre uses the actual coefficient map and sheaf tensor, exactness is tested in all continuous
module sheaves, and the local chart does not silently assert a global lisse lattice. Checked
all five detection/exactness fields and the zero-rank and empty-scheme cases. During elaboration,
added the named structural additivity instance for `realize` so ShortComplex.map uses its
actual zero-preserving functor, and parenthesized the fractional scalar maps so they parse as
scalar multiplication before composition. Neither changed the mathematical statement. The
local normalization is universal in the chosen chart and presentation, with its full
fractional naturality square; comparisons are composites through the same intrinsic fibre.
