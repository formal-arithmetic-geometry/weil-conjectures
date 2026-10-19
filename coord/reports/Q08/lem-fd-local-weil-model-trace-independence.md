## Worker report

The module `Sheaf.Paper.LocalWeilModelTraceIndependence` states
`WeilConjectures.localWeilModelTraceIndependence`, with its sole theorem proof `sorry`.
It constructs five named pieces of the very comparison in this node, with real data:
`localWeilModelScalar`, `localWeilModelPointScalar`, `localWeilModelPointIso`,
`localWeilModelCohomologyIso`, and `localWeilModelDegreeTrace`. They are listed in
`lean.declarations`; no independent new mathematical notion or new DAG node is needed.
The source is the displayed local cohomological trace formula in
`literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-trace/def-fd-trace-function.md`.
I opened this source and the complete item, including its nine-step proof.
The statement and all dependencies of the DAG node are unchanged.

Hypotheses and clauses, matched individually:

- The finite-field tuple is `D : FiniteFieldDatum.{u}`. Its fields record the prime,
  positive exponent, cardinality, finite base field, closure and structural inclusion.
- The distinct coefficient prime and fixed algebraic closure are
  `c : D.CoefficientDatum`, with `c.l`, `c.prime`, `c.different`, `c.Qbar`,
  `c.algebra` and `c.isAlgClosure`. In particular no abstract field unrelated to this
  fixed closure is substituted for the coefficient fields.
- The separated finite-type model is `X₀ : Over (Spec (.of D.k₀))`, with
  `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]`.
  Its geometric fibre is exactly `(D.geometricFiber X₀).left` in every construction.
  Properness is not assumed; the proper-morphism node also records separatedness.
- The three finite subextensions are `E E' L : Padic.FiniteCoefficientFields c.l c.Qbar`.
  Their finite-dimensionality and literal inclusions in the chosen closure are provided
  by this recorded type; `hEL : E ≤ L` and `hE'L : E' ≤ L` give the two inclusions.
- The two Weil pairs are `V : sfWeilComplex ... E.val` and `V' : sfWeilComplex ... E'.val`.
  These are the dependency's actual `IsoAlgebra` fixed pairs in raw rationalized
  constructible categories, without Karoubi completion or integral Weil structures.
- `localWeilModelScalar ... V` constructs the extended pair: its carrier is precisely
  `sfRationalScalarExtension ... .obj V.carrier`, and its structure is the inverse
  `rationalPullbackScalarComparison` followed by scalar extension of `V.str`.
  The auxiliary characteristic parameter is zero, consistently with the published
  rational scalar comparisons; the actual geometric characteristic remains `D.p`.
- `u : localWeilModelScalar ... V ≅ localWeilModelScalar ... V'` is an isomorphism
  of Weil pairs. Applying `sfWeilForget` gives its underlying isomorphism, whose
  arrows obey the `IsoAlgebra` intertwining equation. It is not an arbitrary carrier
  isomorphism with equivariance omitted.
- Positive extension degree and rational point are `(n : ℕ) (hn : 1 ≤ n)` and
  `x : D.extensionPoints X₀ n hn`. The geometric point used throughout is the
  dependency's `localExtensionPoint D X₀ n hn x`.
- `C_{E,x}` is exactly `localPointComplex ... V (localExtensionPoint ...)` in the
  bounded finite-dimensional point category. `localExtensionFrobenius ... V n hn x`
  is the dependency's local operator, including its iterated theta, point transport,
  specified composition comparisons and the semilinear return equation. These
  constructions are used directly, not replaced with arbitrary point endomorphisms.
- `b_M` is `localWeilModelPointScalar`. Its first factor is the inverse component of
  `pointRationalFibreScalarIso`, normalized by the rationalized sections comparison
  of the dependency `lem-weil-point-sections-scalar-extension` and its fixed size
  transport. Its second factor is `pointRationalFibre.mapIso` of
  `rationalPullbackScalarComparison.app V.carrier` for the geometric point.
  Its endpoints are explicitly typed in the definition.
- The exact displayed tilde-u is `localWeilModelPointIso`: compose `b_M`, then
  `pointRationalFibre.mapIso (rationalDerivedPullback.mapIso (sfWeilForget.mapIso u))`,
  then the inverse of `b_M'`. Lean's `≪≫` and `≫` compose from left to right.
- The first conjunct is tilde-u followed by the extended primed operator equals the
  extended unprimed operator followed by tilde-u. This is precisely the node's
  displayed intertwining equation, written in Lean's composition order.
- The `∀ j : ℤ` clause includes every negative and positive cohomological degree.
  Its first conjunct states conjugacy of the scalar-extended cohomology operators.
  `localWeilModelCohomologyIso` is the inverse `fieldDerivedHomologyIso` at the first
  point complex, then `H^j(tilde-u)`, then `fieldDerivedHomologyIso` at the second.
  The compared arrows are literally `ModuleCat.extendScalars.map` of the recorded
  `localExtensionFrobeniusCohomology` arrows.
- `localWeilModelDegreeTrace` is `LinearMap.trace` of that recorded cohomology
  endomorphism, not an alternating or categorical trace. The next conjunct gives
  equality in `L.val` using `IntermediateField.inclusion hEL` and `... hE'L`.
  The final conjunct is equality in `c.Qbar` using the fixed `E.val.subtype` and
  `E'.val.subtype`. These are the two equivalent trace formulations requested.
- The domain is the full constructible pair category. There is no finite-Tor,
  perfect-reduction, integral-lattice, integral-equivariance, or chosen-basis binder.
  Boundedness and finite-dimensionality are supplied by `localPointComplex` itself.

Dependency declarations read and used (their source signatures and docstrings were
opened, including normalization definitions rather than just their names):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `FiniteFieldDatum.CoefficientDatum`, `geometricFiber`, `extensionPoints`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalScalarExtension`, and its uniquely prescribed integral object/Hom formula.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`, `sfWeilForget`,
  `sfWeilFrobeniusPullback`, `sfWeilPrimeInvertible`.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localDerivedStalk`, `localPointComplex`,
  `localPullbackComposition`, `localExtensionPoint`, `localExtensionPoint_return`,
  `localExtensionFrobenius`, `localExtensionFrobeniusCohomology`; the full file was read.
- `Sheaf.SixFunctors.FrobeniusPointTransportNatural`:
  `frobeniusPointTransport_natural`, including its rational naturality and final
  scalar-compatibility clauses; proof dependency imported without `public`.
- `Sheaf.Paper.PointSectionsScalarExtension`: `pointSectionsScalarExtension` and
  `pointRationalSectionsScalarExtensionIso`. The small comparison actually used is
  `pointRationalFibreScalarIso` in `Sheaf.Paper.FiniteCoefficientPoint`, whose unique
  normalization explicitly uses this very sections comparison and tensor/lift map.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`: `scalarPullbackCompleted`
  and the normalized strict tower/ordinary comparisons underlying
  `rationalPullbackScalarComparison` in `Sheaf.Paper.DerivedPullbackTensorHom`.
- `Sheaf.Paper.IntegralPullbackComparisonRealization`:
  `integralPullbackComparisonRealization`, `IntegralComparisonSystem`,
  `integralComparisonComposition`, `integralComparisonScalar`,
  `IntegralComparisonRealizationCoherence`, especially scalar/composition coherence
  before and after rationalization; proof dependency imported without `public`.
- `Sheaf.Paper.FieldCohomologyScalarExtension`:
  `DerivedCategory.fieldDerivedHomologyIso` and its representative normalization;
  this is explicitly used in the cohomology comparison helper.
- `Mathlib.LinearAlgebra.Trace`: `LinearMap.trace`; source definition and ordinary
  conjugacy/base-change signatures were read.
- `Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws`:
  `DerivedCategory.perfectCategoricalTrace_conjugacy`,
  `perfectCategoricalTrace_scalar_extension`, `perfectCategoricalTrace_cohomology`.
  Imported as the node's proof dependency; the degreewise conclusion is expressed
  directly using ordinary linear trace, so no perfectness predicate is introduced.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsSeparated`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
  These use exactly the node's scheme-morphism properties.

Edge cases checked before and after drafting: `n = 1` uses positive-power index zero
in the existing definition, hence exponent one, not an identity local operator.
`n = 0` is excluded exactly by the stated positivity. Empty schemes and models with
no extension-valued points give an empty point quantifier, without a nonempty-scheme
hypothesis. Zero complexes, zero cohomology, shifted complexes and negative `j` are
included. Equal fields `E = E' = L` and either inclusion being identity are allowed;
the actual scalar comparisons remain in place rather than being silently erased.
Different fields inside a larger common finite extension are allowed. Nonsemisimple
and nontrivial-rank Weil operators are not restricted. The construction does not
replace the semilinear return by an incorrect fixed-point equation on scheme maps.
Universe `u` is explicit and all variables are bound; there are no auto-implicits or
file-local notations/instances. No statement correction or disputed statement.

Searches for existing notions/statements (2026-10-18):

- `msearch.py ... leanfinder "Isomorphic finite coefficient Weil models have conjugate
  local Frobenius operators after scalar extension and equal degreewise traces"`:
  eight results, including `isConj_arithFrobAt`, Witt-vector isocrystal equivalence
  and finite-field Frobenius declarations; no constructible Weil-pair comparison.
- `msearch.py ... loogle "LinearMap.trace_conj, LinearMap.trace_baseChange"`:
  zero hits. The declarations were nevertheless located by grep and read directly.
- `msearch.py ... leansearch "The traces of cohomological local Frobenius operators
  on isomorphic finite field models of Weil complexes agree after coefficient scalar
  extension"`: eight results, including `LinearMap.trace_map`, Frobenius and Witt
  isocrystal declarations; none states the geometric comparison.
- `msearch.py ... grep 'localFrobenius|trace_conj|trace_baseChange' LinearAlgebra`:
  eleven hits, ordinary trace conjugacy/base-change and matrix facts only.
- `rg -n 'localFrobenius|localWeilModel|trace_baseChange|trace_conj'` in the upstream
  `WeilConjectures` and side `lean/Sheaf`: upstream has ordinary trace usage only;
  side has the actual local-operator definition and point-embedding conjugacy theorem.
  The latter was opened and compares different residue embeddings at one field,
  not different coefficient models, so is not a duplicate of this item.
- `rg -n 'lem-fd-local-weil-model-trace-independence'` in upstream `WeilConjectures`:
  no match. Exact proposed declaration-name search in upstream, side Lean and
  `dag/lean_names_upstream.json`: no match.

Validation: the prescribed `scompile.py Q08 lem-fd-local-weil-model-trace-independence`
compiled the delivered file as sandbox and library module, with no errors or warnings.
The only postponed proof in this module is the named main theorem. All five helper
constructions are compositions of the dependency maps/isomorphisms with actual data.

## Second reading by Q08

This is the author's separate second pass, not a claim of an independent worker review;
the dispatcher brief requires direct delivery and forbids starting another agent.
I reopened the full node and the completed module and checked each correspondence above.
In particular the point-isomorphism definition reads b, then the point image of the
underlying pair isomorphism, then inverse b'; it is not a bare existential conjugacy.
I checked the comparison directions against both `pointRationalFibreScalarIso` and
`rationalPullbackScalarComparison`, and the cohomology isomorphism against
`fieldDerivedHomologyIso`, whose direction is H(C tensor L) to H(C) tensor L.
The theorem retains separatedness and both parts of finite type, and uses all finite
subfields inside the given closure. Its two intertwining equations have the correct
Lean composition order. The trace is ordinary in every degree, with both L and Qbar
inclusions explicit. There is no extra Tor or lattice condition, no weakened carrier,
and no restriction to nonzero cohomology or positive cohomological degrees.
No mismatch was found and no statement was changed during this second pass.
The maintainer's independent review remains the independent mathematical review.
