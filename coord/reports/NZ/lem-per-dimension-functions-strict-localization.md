## Worker report

The delivery states `AlgebraicGeometry.Scheme.isGeometricDimensionFunction_iff_strictLocalization`
in `Sheaf.AlgebraicGeometry.DimensionFunctionsStrictLocalization`. Its only theorem has
`by sorry` as its entire proof. No definition or theorem proof is added. The source is
Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XIV, Definitions 2.1.1--2.1.2 and
2.1.8, the following paragraph (printed pp. 209--212), and the opening strict-local
reduction of Proposition 2.5.4 (printed p. 217). I read those passages in the supplied PDF.
The statement and source agree; no statement correction or dispute is needed.

The former worker left only dispatcher marker files, no Lean module, node copy or report.
The current base has the NS stage-1 split and maintainer review but no `lean` record for
this item. This packet therefore supplies a genuine stage-2 statement, rather than
resubmitting the already-reviewed stage-1 split. It retains that split and review verbatim.
Only `lean` and the permitted addition of an already-landed definition to `stmt_deps`
change in the node copy.

Clause-by-clause correspondence:

- The scheme T is `(T : Scheme.{u})`; the hypothesis that it is Noetherian is
  `[IsNoetherian T]`, including quasi-compactness exactly as the node requests.
- Excellence is `(hT : ∀ U : T.affineOpens, IsExcellent Γ(T, U))`. This uses the
  recorded excellent-ring definition and tests every affine coordinate ring, the same
  scheme-level encoding used by the landed regular-dimension-function-pullback consumer.
- An arbitrary integer-valued function is `(d : T → ℤ)`. There is no boundedness,
  continuity or normalization hypothesis on d.
- The dimension-function predicate is the existing
  `AlgebraicGeometry.Scheme.IsGeometricDimensionFunction`. Its full definition quantifies
  over an algebraically closed field Ωx and a geometric point barX, then over another
  algebraically closed field Ωy and a geometric point a of the recorded strict
  localization. Its premise is `topologicalKrullDim (closure {a(...)}) = 1`; reduction
  leaves this topological space unchanged, so this is precisely the dimension of the
  reduced closure in the node. Its equation is value(general) = value(special) + 1,
  equivalent over ℤ to the node's value(special) = value(general) - 1.
- The equivalence itself is `IsGeometricDimensionFunction T d ↔ ...`.
- Every geometric point is quantified by `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (barT : Spec (.of Ω) ⟶ T)`. The underlying point t is determined by barT; no independent
  point, residue-field identification or redundant equality is assumed.
- The strict localization is `strictHenselizationScheme barT`, exactly the recorded
  spectrum of the affine pointed-etale coordinate-ring colimit.
- Its canonical map is `strictHenselizationStructuralMap barT`. The pulled-back function
  is `(fun x ↦ d (strictHenselizationStructuralMap barT x))`. No arbitrary replacement
  morphism or chosen isomorphism is used in the statement.
- The right side requires this function to be a dimension function for every barT.
  The final 'in particular' is precisely the forward implication specialized to a
  geometric point, and introduces no extra conclusion or hypothesis.

Dependency declarations read and used:

- `Sheaf.RingTheory.ExcellentRing`, `IsExcellent`: its full expansion through
  `IsQuasiExcellent` and `IsUniversallyCatenary` was read.
- `Mathlib.AlgebraicGeometry.ResidueField`, `Scheme.SpecToEquivOfField`, and
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed`: geometric points are inline
  algebraically closed fields and maps from their spectra, as the recorded match says.
- `Sheaf.AlgebraicGeometry.StrictHenselization`, `Scheme.strictHenselizationRing` and
  `Scheme.strictHenselizationScheme`; these are the current canonical abbreviations for
  the upstream construction. I also read the original colimit and spectrum declarations
  in the supplied `lean/WeilConjectures` framework.
- `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim`: its signature and definition
  are the supremum of prime-chain lengths. For the reduced closure in the immediate
  geometric specialization, the landed dimension-function definition uses the equivalent
  topological dimension of the closure, so no affine chart or new ring is chosen here.
- `Sheaf.AlgebraicGeometry.GeometricDimensionFunction`,
  `Scheme.IsGeometricDimensionFunction`, owned by the already-landed node
  `def-per-geometric-dimension-function`. That node is added to `stmt_deps`; no copy of
  this predicate or new definition node is made. I read its node and full source, including
  the current server source via `scompile.py --source`.
- The canonical map is imported transitively from
  `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`; its full source
  and construction were read using `scompile.py --source`.

The three already-stated proof dependency modules are imported without `public`, as required:
`Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance`
(`Scheme.indEtale_strictLocal_invariance`),
`Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale`
(`Scheme.strictHenselization_indEtale_of_affine_chart`), and
`Sheaf.Paper.StrictHenselizationFunctoriality`
(`AlgebraicGeometry.strictHenselizationFunctoriality` and the clause-(1) declaration
`AlgebraicGeometry.strictHenselizationResidue`). I read their declarations and docstrings.
The theorem docstring carries all three steps of the reviewed node's proof, including
using the canonical isomorphism phi over T and transporting v by its inverse in step 3.

Edge cases checked mathematically: the empty scheme and the spectrum of a field impose
no dimension-one specialization conditions; the trait equation has the general value
one larger than the special value; nilpotents do not affect the closure's topological
Krull dimension; reducible and non-equidimensional schemes retain each geometric branch;
zero-dimensional closures do not trigger the predicate. Arbitrarily large algebraically
closed residue-field overextensions within the universe are quantified, not just a fixed
algebraic closure. The scheme, its geometric fields and the strict-local construction
use the same universe u, matching the landed definition; there is no independent smaller
universe for test points. All variables and universes are explicitly bound, and
`set_option autoImplicit false` is present. No local notation or private instance appears.

Searches actually made:

- msearch LeanFinder, 'An integer valued dimension function on a scheme is a dimension
  function if and only if its pullbacks to all strict localizations are dimension functions':
  eight results about ring-hom locality, stalkwise criteria and Krull-dimension bounds;
  none states this equivalence.
- msearch Loogle, '"DimensionFunction"': zero hits.
- msearch grep, 'DimensionFunction|dimensionFunction|dimension.function': zero Mathlib hits.
- msearch LeanSearch, 'A dimension function on a scheme is detected by pullback to all
  strict localizations': eight hits about localization dimensions, inducing maps and
  morphism properties; none states this equivalence.
- rg over the supplied upstream `WeilConjectures` source for dimensionFunction,
  DimensionFunction, dimension_function and dimension-function vocabulary: no exact theorem.
  The blueprint-id search likewise gives no upstream binding for this item.
- rg over `lean/Sheaf` and the DAG found the landed
  `def-per-geometric-dimension-function` and `RegularDimensionFunctionPullback`; the latter
  uses this equivalence in its proof plan but states a different regular-pullback theorem.
  The full declarations were opened. No exact existing statement was found.

No new nodes or dependency repairs are included. No statement was corrected. The sole
citer, `lem-per-regular-dimension-function-pullback`, keeps its existing statement and
canonical dimension-function predicate; its strict-local reduction can use this theorem.

Compilation status: the prescribed single-file `scompile.py` invocation reached the
server and returned exit 75, explicitly classified as
`INFRASTRUCTURE RETRY (stale live olean)`: the published live build lacks
`Sheaf.AlgebraicGeometry.GeometricDimensionFunction.olean`. The server source query
confirms that this already-landed module exists. This is a missing published artifact,
not a missing mathematical definition. I have not copied or redefined it, changed any
launcher/server tool, edited the live library, or run a global build. Further compiler
and dry-run results are recorded below.

The required `deliver2.py NZ lem-per-dimension-functions-strict-localization --no-push`
was also run. It failed at compilation with the identical infrastructure diagnostic:
`COMPILE FAILED on the server, nothing pushed` and
`INFRASTRUCTURE RETRY (stale live olean)`, naming the missing published
`Sheaf.AlgebraicGeometry.GeometricDimensionFunction.olean`. Thus the wrapper could not
reach preflight and did not create or push a delivery. No push invocation was made.
Static checks confirm the recorded signature is verbatim, all Lean lines are at most
100 characters, and the node differs only in `lean` and addition of the landed
`def-per-geometric-dimension-function` to `stmt_deps`.

## Saved-packet retry 2026-10-18 20:49 UTC

Retained the earlier packet and ran the required dry run first. `deliver2.py NZ lem-per-dimension-functions-strict-localization --no-push` again failed before preflight with `INFRASTRUCTURE RETRY (stale live olean)`, naming the absent published `Sheaf/AlgebraicGeometry/GeometricDimensionFunction.olean`. A direct prescribed `scompile.py` invocation independently returned exit 75 with the same diagnostic. `scompile.py --source Sheaf.AlgebraicGeometry.GeometricDimensionFunction` succeeded and confirmed the current canonical definition and signature used by this packet. No mathematical interface repair is indicated: the published compiled artifact is missing. No Lean or node file was changed, no tool was modified, and no delivery was pushed.

## Saved-packet retry 2026-10-18 21:00 UTC

Inspected the saved report and ran the required dry run before further investigation.
`deliver2.py NZ lem-per-dimension-functions-strict-localization --no-push` failed
with `COMPILE FAILED on the server, nothing pushed` and
`INFRASTRUCTURE RETRY (stale live olean)`, again naming the missing published
`Sheaf/AlgebraicGeometry/GeometricDimensionFunction.olean`. A direct prescribed
`scompile.py` invocation independently returned exit 75 with the same diagnostic.
`scompile.py --source Sheaf.AlgebraicGeometry.GeometricDimensionFunction` succeeded;
its complete source confirms the canonical predicate and strict-localization map
used in the saved module. The wrapper explicitly diagnoses a published live build
that predates or lacks this live module, rather than an absent source declaration.
The packet is retained unchanged apart from this report entry. No launcher tool or
live library was modified, no global build was run, and no delivery was pushed.

## Saved-packet retry 2026-10-18 21:10 UTC

Inspected the preserved report and module, then ran the required
`deliver2.py NZ lem-per-dimension-functions-strict-localization --no-push`
before investigating further. It again returned `COMPILE FAILED on the server,
nothing pushed` and `INFRASTRUCTURE RETRY (stale live olean)`: the published
`Sheaf.AlgebraicGeometry.GeometricDimensionFunction.olean` is absent.
The prescribed direct `scompile.py` invocation reproduced the same failure.
`scompile.py --source Sheaf.AlgebraicGeometry.GeometricDimensionFunction`
succeeded and agrees with the canonical definition in the read-only shared source.
There is no alternate upstream definition to import and no mathematical dependency
interface defect to repair. The worker contract explicitly forbids rewriting an
already-landed declaration merely because its published build artifact is missing.
The source signature remains verbatim in the node record and every Lean line is
at most 100 characters. No Lean or node file was changed, no launcher tool or live
library was modified, and no delivery was pushed. The packet is retained.

## Saved-packet retry 2026-10-18 21:13 UTC

Inspected the preserved report and ran the required `deliver2.py NZ
lem-per-dimension-functions-strict-localization --no-push` first. It returned
`COMPILE FAILED on the server, nothing pushed` and `INFRASTRUCTURE RETRY
(stale live olean)`, identifying the missing published
`Sheaf.AlgebraicGeometry.GeometricDimensionFunction.olean`. The direct prescribed
`scompile.py` invocation independently returned exit 75 with the same missing
artifact diagnostic. `scompile.py --source
Sheaf.AlgebraicGeometry.GeometricDimensionFunction` succeeded; its full definition
agrees with the saved module's canonical predicate and map. This is a published
artifact failure, not an absent or unusable mathematical interface to repair.
The Lean module and node copy remain unchanged. No tool or live library was
modified, no global build was run, and no delivery was pushed.

## Saved-packet retry 2026-10-18 21:18 UTC

Retained the saved module and node record and ran the required dry run first.
The initial dry run reproduced the stale-live-olean diagnostic. The prescribed
direct `scompile.py` invocation then passed both sandbox and library compilation
without warnings or errors. A second `deliver2.py NZ
lem-per-dimension-functions-strict-localization --no-push` passed preflight and
compilation, printing `OK (dry run)` for commit `432777b4fb`. The earlier missing
artifact diagnostic therefore no longer blocks this packet.

Self-check: read the saved theorem and current dependency node records, and fetched
the current `Sheaf.AlgebraicGeometry.GeometricDimensionFunction` source using
`scompile.py --source`. Its canonical predicate and structural map agree with the
saved statement. The node differs from the current base only in `lean` and the
permitted addition of `def-per-geometric-dimension-function` to `stmt_deps`.
The recorded theorem signature is verbatim, every Lean line is within 100 columns,
all universes and variables are explicit, and the sole proof remains `by sorry`.
No Lean or node changes were needed. This entry supersedes the historical blocked
compilation status above.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
