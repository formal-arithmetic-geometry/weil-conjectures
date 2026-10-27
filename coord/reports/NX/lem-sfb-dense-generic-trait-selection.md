## Worker report

The module `Sheaf.AlgebraicGeometry.DenseGenericTraitSelection` states
`AlgebraicGeometry.exists_dense_generic_trait`, with its sole proof `sorry`.
No definition, hypothesis, conclusion, or DAG statement was changed. No new
nodes or dependency modules were needed.

Hypothesis and conclusion correspondence, reading the node beside the signature:

- The DVR R is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. Mathlib's class is a local principal ideal
  domain with nonzero maximal ideal, so fields are excluded exactly as intended.
- Its fraction field K is `(K : Type u) [Field K] [Algebra R K]
  [IsFractionRing R K]`. The scheme S is `Spec (CommRingCat.of R)`.
  Its generic point is `genericPoint (Spec (CommRingCat.of R))` and its
  closed point is `IsLocalRing.closedPoint R`.
- The integral scheme Y is `(Y : Scheme.{u}) [IsIntegral Y]`.
  Its structural map is `f : Y ⟶ Spec (CommRingCat.of R)`.
  Finite type is `[LocallyOfFiniteType f] [QuasiCompact f]`, retaining both
  parts of the dependency node's recorded definition.
- Dominance, defined in the node as dense image, is `hf : DenseRange f`.
- The special fibre is `f.fiber (IsLocalRing.closedPoint R)` and the
  hypothesis `hYs : Nonempty ...` asserts its nonemptiness.
- The arbitrary open U is an `Opens` of `f.fiber (genericPoint ...)`;
  `hU : (U : Set ...).Nonempty` is exactly its nonemptiness. Its open
  subscheme and inclusion are Mathlib's `U.toScheme` and `U.ι`.
- The existential `R₀ : Type u` has its own commutative ring, domain,
  DVR, and `Algebra R R₀` structures. The requested homomorphism is
  `algebraMap R R₀`; `Function.Injective` and `IsLocalHom` record its
  injectivity and locality separately.
- K0 is the actual canonical field `FractionRing R₀`, rather than a new
  field supplied without a fraction-field condition. Its standard field
  and `IsFractionRing R₀ (FractionRing R₀)` instances are Mathlib's.
  The existential `Algebra K (FractionRing R₀)` supplies the extension
  K0/K, and `FiniteDimensional K (FractionRing R₀)` supplies finiteness.
  The equality of the two ring-map composites R -> K0 explicitly makes
  this extension compatible with the chosen local injection R -> R0.
- The morphism is `c : Spec (CommRingCat.of R₀) ⟶ Y` and
  `c ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R₀))` says exactly
  that it is an S-morphism for the chosen R-algebra structure.
- `f (c (IsLocalRing.closedPoint R₀)) = IsLocalRing.closedPoint R`
  says its closed point lies in Y_s (membership in the fibre is equivalent
  to this equality under the recorded fibre homeomorphism).
- The last existential supplies `cη : Spec (CommRingCat.of (FractionRing R₀))
  ⟶ U.toScheme` and states that composing with `U.ι` and `f.fiberι ...`
  equals the canonical generic inclusion followed by c. This is the
  requested factorization of the generic restriction through U. There is
  no arbitrary substitute for the generic inclusion: it is the spectrum
  of `algebraMap R₀ (FractionRing R₀)`.
- No completeness, excellence, separability, or module-finiteness condition
  is imposed. The statement retains every finite extension, including
  inseparable ones. All variables and the universe are explicit, and
  `set_option autoImplicit false` enforces this.

Dependency declarations used, with their actual source signatures and docstrings read:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, lines 56–60; also its
  equivalence between irreducibles and generators of the maximal ideal.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`, lines 470–480.
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties`, lines 238–245.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, lines 38–46, and
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  lines 38–46 (available publicly through FiniteType).
- `def-pc-scheme-fibre`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, `Mathlib.AlgebraicGeometry.Fiber`, lines 37–48.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`, lines 35–39; the canonical open
  subscheme `U.toScheme` and its inclusion `U.ι` use this existing notion.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`,
  lines 91–100. The extension's source and target are fields, so its
  algebra map is injective automatically.

Public imports expose the notions in the signature. Plain imports include the
recorded proof dependencies that have declarations: the Mathlib finite-type
criterion, maximal-ideal existence, scheme sobriety, closed immersions,
Noetherian finite-type schemes, function-field fractions, and the
finite-dimensional-domain field criterion; and the recorded modules
`Sheaf.AlgebraicGeometry.QuasiFiniteLocusOpen`,
`WeilConjectures.AlgebraicGeometry.HasUniversallyBoundedFibersOfIsLocallyQuasiFinite`,
`WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE`, and
`WeilConjectures.AlgebraicGeometry.AffineFibreSectionsTensor`.
The proof dependencies `lem-sfb-quasi-section-nearby-open` and
`lem-sfb-nongeneric-point-same-field-dvr` currently have no Lean records or
Mathlib matches, so there are no modules to import for those proof-only inputs.
Their statements were read, and all six assembly steps are in the theorem's
docstring for stage 3. Neither input is needed to type the statement.

Sources opened: Stacks `more-morphisms.tex`,
`lemma-quasi-finite-quasi-section-meeting-nearby-open-X` (05GU), including
its reduced closure construction; and `algebra.tex`, `lemma-exists-dvr`
(00PH), including its fraction-field-preserving domination conclusion.
These support the node's statement without any correction.

Edge cases checked before writing: Y empty is excluded precisely by integrality;
an empty special fibre and empty U are excluded precisely by the two nonempty
hypotheses. U may be the whole generic fibre and Y may be S itself (choose
R0=R, K0 canonically isomorphic to K, and c the identity). R being a field is
excluded by the existing DVR class, not by an added hypothesis. Positive
characteristic and inseparable finite extensions are allowed. Nonexcellent,
noncomplete DVRs and non-module-finite DVR extensions remain allowed. The
universe u is arbitrary: R, its fraction field, finite-type Y, its open
subschemes, the selected local rings and fraction fields can all be represented
at this same scheme universe; no larger test-object quantification is restricted.
Using the canonical fraction field entails only the unique field isomorphism
of fraction fields, not an additional mathematical restriction.

Searches actually run with msearch.py for this item:

- LeanFinder: “An integral finite type scheme over a discrete valuation ring
  admits a trait meeting any nonempty generic open with finite fraction field
  extension”. Eight hits, including `IsIntegral`, its generic-point order
  instance, valuative-square fraction-ring data, and function-field fraction
  instances; none states the requested existence/selection theorem.
- Loogle: `IsDiscreteValuationRing, AlgebraicGeometry.Scheme.Hom.fiber`.
  Zero hits.
- Mathlib grep in AlgebraicGeometry: `trait|quasi.?section|dense.*generic`.
  Zero hits.
- LeanSearch: “A finite type integral dominant scheme over a DVR with nonempty
  special fibre has a trait meeting a prescribed nonempty generic open with
  finite fraction field extension”. Eight hits, concerning integral schemes,
  integral morphisms, and finite integral morphisms; no selection theorem.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf`:
  `trait|quasi.?section|dense.*generic|lem-sfb-dense-generic-trait-selection`.
  Existing trait-lifting, smooth-trait, purity, and generic-density results
  have different hypotheses/conclusions; none is this finite-extension
  trait-selection assertion. A narrower search for `exists.*(dvr|DVR)` and
  `dense_generic_trait|nongeneric_point_same_field` likewise found no match.
- Direct rg of `exists_dense_generic_trait` in both Lean roots and
  `dag/lean_names_upstream.json` found no declaration with the chosen name.

Validation: the delivered module compiled separately with scompile.py against
the server's live published build, in both sandbox and library modes, with
no errors or unexpected warnings. The node's `lean.statement` is extracted
verbatim from `theorem` up to, but excluding, `:=`; all other node fields
are preserved. No STATEMENT-DISPUTED issue was found.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
