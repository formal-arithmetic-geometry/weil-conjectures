## Worker report

The promoted module `Sheaf.Paper.LocalWeilModelTraceIndependence` states
`WeilConjectures.localWeilModelTraceIndependence`; its proof is `sorry`, as required
for stage 2. It defines the five comparison constructions used by the statement with
actual data: `localWeilModelScalar`, `localWeilModelPointScalar`,
`localWeilModelPointIso`, `localWeilModelCohomologyIso`, and
`localWeilModelDegreeTrace`. The theorem retains the finite-field datum, distinct
coefficient prime, separated finite-type scheme, three finite coefficient fields and
both inclusions, two finite-stage Weil pairs, an isomorphism of their scalar extensions,
`n >= 1`, and the specified rational point. Its three conclusion clauses are exactly
point-operator conjugacy, degreewise cohomology conjugacy for every integer degree,
and equality of ordinary traces in the common field and in the fixed algebraic closure.

The Lean binders render the hypotheses as follows: `D : FiniteFieldDatum`,
`c : D.CoefficientDatum`; `X₀ : Over (Spec (.of D.k₀))` with
`[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]`;
`E E' L : Padic.FiniteCoefficientFields c.l c.Qbar` with `hEL` and `hE'L`;
`V`, `V'` are `sfWeilComplex` objects and `u` is an isomorphism of the two
`localWeilModelScalar` pairs; finally `(n : ℕ)`, `hn : 1 ≤ n`, and
`x : D.extensionPoints X₀ n hn`. `localWeilModelPointIso` is precisely the
specified b-map, point pullback of `u`, and inverse b'-map. The first conjunction
uses the two `DerivedCategory.pointFdScalarExtension` maps and
`localExtensionFrobenius`; the universal integer-degree clause uses
`localWeilModelCohomologyIso`, `ModuleCat.extendScalars`, and
`localExtensionFrobeniusCohomology`; the final two clauses use
`LinearMap.trace`, `IntermediateField.inclusion`, and the fixed subtypes into `Qbar`.

Dependencies used: `Sheaf.Paper.FiniteFieldFiber` (`FiniteFieldDatum` and its
coefficient datum, geometric fibre, extension points),
`Sheaf.Paper.SfRationalizationKaroubi` (`sfWeilComplex` scalar extension),
`Sheaf.Paper.SfWeilSheafComplex` (`sfWeilComplex` and forgetful map),
`Sheaf.Paper.LocalFrobeniusTrace` (point complexes and local Frobenius operators),
`Sheaf.SixFunctors.FrobeniusPointTransportNatural`,
`Sheaf.Paper.PointSectionsScalarExtension`,
`Sheaf.Paper.IntegralOperationsScalarComparisons`,
`Sheaf.Paper.IntegralPullbackComparisonRealization`,
`Sheaf.Paper.FieldCohomologyScalarExtension`,
`Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws`, and Mathlib's
`AlgebraicGeometry.IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, and
`LinearMap.trace`. The recorded declarations and their docstrings were read.

Edge cases checked: `n = 1`; empty schemes and empty point sets; zero and shifted
complexes; negative cohomological degrees; equal fields `E = E' = L`; identity
inclusions; nonsemisimple Weil operators; and no finite-Tor or integral-lattice
hypothesis. All universes and variables are explicit.

Searches made on 2026-10-18: `msearch.py` LeanFinder, LeanSearch and Loogle queries
for isomorphic Weil-model local trace invariance; `msearch.py grep` and `rg` over
Mathlib, `WeilConjectures`, and `lean/Sheaf` for local Frobenius, scalar extension,
and trace-conjugacy names. They found only ordinary linear trace and unrelated
Frobenius declarations; no exact existing statement. The promoted module is the
canonical project declaration. No statement correction or `STATEMENT-DISPUTED` flag
is needed.

## Second reading by N1

I reopened the node, the source blueprint clause, and the complete module. The
hypothesis-by-hypothesis correspondence above is exact: separatedness and both parts
of finite type are present, the common extension and both inclusions are explicit, and
`u` is an isomorphism of Weil pairs rather than an arbitrary carrier map. The three
conclusion clauses have the correct composition order and include every `j : ℤ`.
The b-comparison directions and scalar/cohomology maps match the recorded dependency
signatures. The only postponed proof is the named theorem. The declaration is already
promoted in the shared tree; this N1 copy changes only the node's `lean.by` attribution.


Independent maintainer reading (2026-10-18, immutable delivery
7f0d18cacb4cc36cb36ae9e85dd35f4493be8bcc): the theorem signature and all five
helper constructions agree with the node. I checked the inverse direction of phi,
the rational pullback/scalar comparison, the forgetful image of the Weil-pair
isomorphism, and the inverse/forward cohomology comparisons at E/E'. Lean's first
equality reads tilde-u followed by F' equals F followed by tilde-u, which is the
node's equation in diagrammatic composition order. Both trace equalities are
inside the universal integer-degree binder. No nonzero-cohomology, integral-lattice,
finite-Tor, properness, smoothness, or semisimplicity assumption occurs. The
single universe is the existing FiniteFieldDatum/CoefficientDatum framework
convention; no additional equality of site-object and site-morphism universes is
introduced by this file. The point-section interface retains its u+1 coefficient
lift and specified descent.

I found a documentation/API mismatch in proof-plan step 9 (H8):
TraceFormalLaws.perfectCategoricalTrace_conjugacy and
perfectCategoricalTrace_scalar_extension have finite quotient-ring source
coefficients, so there are no recorded field instances of those two declarations.
The replacement module corrects this step to use the existing ordinary field
identities LinearMap.trace_conj' and LinearMap.trace_baseChange, with the canonical
tensor-coordinate identification. This changes no definition, theorem signature,
node statement, hypothesis, conclusion, or DAG dependency. The trace-formal-laws
import remains relevant mathematical proof infrastructure; it is not claimed to
supply nonexistent field specializations. No dependency module or new node is
needed because the exact ordinary trace lemmas already exist in Mathlib.

I checked n=1 (positive-power index zero), absence of n=0 by the stated hn,
empty schemes/point sets, zero and shifted complexes including negative degrees,
identity coefficient inclusions, coincident fields, and arbitrary invertible Weil
operators including Jordan blocks. The source blueprint defines the trace on the
Qbar category, making independence of finite representatives an implicit
well-definedness obligation; its final sentence does not explicitly state this
lemma. The canonical point comparisons use the actual small pro-etale framework,
not a substitute category. The realization comparison source uses ordinary strict
towers, K-flat representatives and right-derived limit. No dropped route-pivot
node is directly cited, and no infinity/dg/model-category machinery is introduced.

Compilation reproduced through the prescribed wrapper:
python3 /home/ubuntu/weil-launcher-nt/scompile.py N1
lem-fd-local-weil-model-trace-independence
snapshot/lean/Sheaf/Paper/LocalWeilModelTraceIndependence.lean
returned exit 0 with no diagnostics: isolated sandbox 30.9 s and library-name
confirmation 19.0 s. The installed wrapper reports server-side overlay compilation;
it is not a local-only run. No lake build, global build or direct live write was
performed. The replacement module changes documentation alone. Its complete replacement was
rechecked with the same wrapper, passing fixes/LocalWeilModelTraceIndependence.lean:
exit 0, no diagnostics, sandbox 33.7 s and wrapper library confirmation
Sheaf/Stage2/Check.lean 17.8 s. The fallback confirmation name comes from the
basename-only fixes layout; the original library-name check above also passed.
