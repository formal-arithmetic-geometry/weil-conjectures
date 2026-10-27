# Q107: Kollar smooth-divisor injectivity

## Worker report

The module `Sheaf.AlgebraicGeometry.KollarSmoothDivisorInjectivity` states
`AlgebraicGeometry.kollar_smooth_divisor_injectivity` with `sorry`, without proving
anything or introducing a definition. The prior BLOCKED ending concerned a stage-1
duplicate split. The live item is split with `lean: null`; the stage-2 handoff in
brief-stage2 section 0 explicitly authorizes this statement delivery.

I opened Popa's author PDF, *Kodaira dimension of algebraic varieties*, section 1.6,
Theorem 1.6.6 and its proof (printed pp.26--27), and the section opening on p.22:
https://people.math.harvard.edu/~mpopa/271/Kodaira-posted.pdf . The named local PDF
remains WANTED. The injectivity statement agrees with that source; the existing
DAG additionally spells out the algebraic-field setting, m >= 2 and empty-divisor
case. No statement correction or disputed assertion is needed.

Hypothesis and conclusion correspondence:

- `F : Type u`, `[Field F]`, `[IsAlgClosed F]`, `[CharZero F]` render the given
  algebraically closed field of characteristic zero, with arbitrary universe u.
- `Y : Scheme.{u}` and `f : Y ⟶ Spec (.of F)` specify the F-scheme and its actual
  structure morphism. There is no embedding into the complex numbers.
- `[SmoothOfRelativeDimension n f]`, for `n : ℕ`, renders smoothness and pure
  dimension n together. Over a field this is the constant relative-dimension
  form of the smoothness/dimension hypothesis, including n = 0.
- `[IsProjective f]` is exactly the project's H-projective plus quasi-compact
  convention. `[GeometricallyIntegral f]` states geometric integrality, hence
  integrality over F; no independent weaker replacement is used.
- `Scheme.Modules.exteriorSheaf f.relativeDifferentials n` is precisely omega:
  relative differentials restrict to the associated algebraic differential
  module on affine opens, and the recorded exterior sheaf is the sheafification
  of sectionwise exterior powers. Its degree-zero identification is the existing
  `exteriorSheaf_zero_iso`, including omega = O in dimension zero.
- `L : Y.Modules` with `[L.IsInvertible]` is the invertible O_Y-module. The existing
  `L.tensorPow` has zeroth power the unit and successive powers L tensor the
  previous power; associativity identifies this with the written tensor powers.
- `m : ℕ` and `hm : 2 ≤ m` include exactly the nonnegative integers m >= 2.
- `s : 𝟙_ Y.Modules ⟶ L.tensorPow m` represents a global section by its associated
  O-linear morphism from O_Y; `hs : s ≠ 0` is nonvanishing of that section.
  The zero-scheme declaration's docstring expressly uses this representation.
- `hD : Smooth (s.zeroLocus.subschemeι ≫ f)` says the actual closed zero scheme is
  smooth over the same F. No nonemptiness or connectedness is imposed on it.
- `j : ℕ` ranges over all and only the requested nonnegative cohomological degrees.
- `RingedSpace.moduleCohomology Y.toRingedSpace j` is R^j Gamma on O_Y-modules,
  not an unrelated cohomology theory. Its `.map` applies that functor to the
  specified multiplication morphism, and `Function.Injective` is injectivity
  of the underlying homomorphism.
- The morphism starts at `omega ⊗ L`: `(ρ_ _).inv` inserts the tensor unit on the
  right; `(omega ⊗ L) ◁ s` tensors the identity with the section; `(α_ _ _ _).hom`
  reassociates to `omega ⊗ (L ⊗ L.tensorPow m)`. The latter is definitionally
  `omega ⊗ L.tensorPow (m+1)`. Locally it sends w tensor l to w tensor l tensor s,
  so it is multiplication by the function representing s in a trivialization.
  In particular no arbitrary map or extra identification is assumed.
- There is no ampleness hypothesis.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the algebraically closed
  clause of def-weil-algebraic-closure, rather than assuming a chosen closure).
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`,
  `Smooth`; their full signatures and affine-chart docstrings were read.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsProjective` and
  its parent `IsHProjective`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`, through
  `Mathlib.AlgebraicGeometry.Geometrically.Integral.GeometricallyIntegral`;
  the latter module supplies `AlgebraicGeometry.GeometricallyIntegral`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `KaehlerDifferential.D`
  and `KaehlerDifferential.linearMapEquivDerivation`, through the existing
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials` construction
  `Scheme.Hom.relativeDifferentials` and its affine comparison.
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`:
  `Scheme.Modules.exteriorSheaf`, with its presheaf construction and zeroth power
  isomorphism read. The already landed nodes def-sc-relative-differential-sheaf
  and def-sc-sheaf-exterior-power are added to stmt_deps; neither is redefined.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, its monoidal structure and `tensorPow`.
- `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`:
  `Scheme.Modules.Hom.zeroLocus`, `.subscheme`, `.subschemeι`. Its ideal is
  locally generated by the section's coefficient and agrees with the image
  ideal in def-pc-zero-scheme.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `sheafCohomologyAndHigherDirectImages`, using the existing
  `AlgebraicGeometry.RingedSpace.moduleCohomology` from
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`. The latter's complete
  definition as a right derived global-sections functor was read.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  `SheafOfModules.cochainModulesMonoidal` interface for def-pur-sheaf-tensor-product
  is imported. The actual scheme tensor is the existing scheme monoidal
  structure; there is no second tensor construction in this file.

The proof-dependency nodes for the cyclic root cover, first Hodge differential
and functorial Serre duality have no Lean records and remain separate stage-1
work. No declarations were invented for them. The theorem docstring carries
all five steps of the accepted proof, including the empty divisor, the m-fold
residue normalization, the exact sequence and the complementary-degree duality.

Edge cases checked before writing: on Spec F, n = 0, a nonzero section has empty
zero scheme and the map is a scalar isomorphism; an empty divisor in any dimension
makes multiplication an isomorphism; m = 2 is admitted; j = 0, j = n and j > n are
all admitted; on P^1 with L = O(d), existence of a nonzero section forces d >= 0,
and the usual cohomology calculations agree. Geometric integrality properly
excludes an empty Y. The zero divisor is allowed to be empty. No cardinality
bound on F, positivity condition, or extra trivialization was added.

Searches (using the prescribed msearch wrapper; results logged by that wrapper):

- LeanFinder query: `Kollar injectivity cohomology canonical bundle tensor line
  bundle smooth divisor in tensor power characteristic zero`: 8 unrelated hits,
  mostly injectivity statements about algebraic cotangent modules; no match.
- LeanSearch query: `Cohomology injectivity multiplication section smooth divisor
  canonical bundle line bundle`: 8 differential-geometric section hits; no match.
- Loogle query `KaehlerDifferential, exteriorPower, moduleCohomology` reported
  unknown identifier exteriorPower, so this was not treated as an absence result.
  A corrected query `KaehlerDifferential` returned 12 differential-module and
  derivation declarations, giving the existing algebraic definition but no
  injectivity theorem.
- Mathlib grep query `Kollar|kollar|Kodaira|kodaira|canonicalSheaf|exteriorPower`
  in AlgebraicGeometry returned no hits. Direct rg of the project Sheaf and
  WeilConjectures trees for the item id, Kollar/Kodaira injectivity and smooth
  divisors found no statement matching this item. The Kollar ring-theory files
  concern the local-ring dichotomy. Searches for relative differentials,
  exterior powers, tensorPow and moduleCohomology located the reused interfaces
  above. The DAG already has the two sheaf-definition nodes now cited.

Validation: scompile.py checked the module both as a private sandbox module and
under its real module path, with no error or unexpected warning. Every variable
and universe is explicitly bound and autoImplicit is disabled. The single
postponed theorem is the exact item, with no helper theorem or definition.

## Second reading by Q107

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
