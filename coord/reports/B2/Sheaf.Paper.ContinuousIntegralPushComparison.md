## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.integralScalarPushHom_isIso`
with its original signature and public import unchanged. The proof treats the actual
continuous coefficient inclusion, ordinary uncompleted derived pushforward, and the
specified adjunction mate. Constructibility supplies bounded-below membership; no
finite-dimensionality of E, properness, or upper cohomological bound is added.

Eleven new support modules construct the scalar sequence and unit cocone, normalize
the regular coefficient telescope, tensor it with modules, pass degreewise to
complexes, identify the specified derived unit, build a strict bounded-below model,
and transport the two required homology colimits. The final proof checks the actual
mate on the zeroth leg, determines all later legs by cancellation, and reflects the
result through restriction of scalars.

The current second reading removed the two unlanded duplicate modules
`ContinuousIntegralModuleInvertible` and `ContinuousIntegralScalarInvertible`, with
their two unlanded nodes. The existing `module_nsmul_isIso` and
`derived_nsmul_isIso` in `ContinuousConstructibleIntegralImage` already prove both
statements without finite-dimensionality. That module is unclaimed. Its only changes
are making these two existing theorems public and adding their docstrings; their
types and complete proofs are byte-identical. They must be public because exposed
cocone definitions cannot refer to private helpers. No existing definition changes.

Removed the local private `Mod.extendUnit_tensor` proof from
`ContinuousIntegralModuleTelescope`. It now uses the existing
`Mod.extendComapTensorIso` and `Mod.extendUnit_tensor` from
`ContinuousConstructibleIntegralDenominators` through a proof-only `import all`.
This also removes its direct Compatibility import. The original unit formula and
the existing one have definitionally equal tensor identifications; a scratch
compile verified direct reuse. The regular telescope continues to reuse the
existing private presheaf localization API of `ContinuousIntegralScalarExact`.

All thirteen delivered modules compile in import order with `lcompile.py --all`,
without errors or warnings. A fresh scratch audit of 23 public theorem, definition
and structure names shows only `propext`, `Classical.choice`, and `Quot.sound`,
including for the final comparison and pushforward homology colimit. No `sorryAx`
occurs in this current audit. Earlier report rounds described upstream holes that
are no longer present in the current compiled dependencies. Logs are
`scratchpad/current-compile.log` and `scratchpad/current-axioms.log`.

Change records:

- `coord/changes/module_nsmul_isIso-public.md`
- `coord/changes/derived_nsmul_isIso-public.md`

## Proved and sorry left

Closed exactly one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.integralScalarPushHom_isIso`.
Holes added: none. Split-off obligations: none. No delivered source contains
`sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or a kernel-check
bypass. This delivery is a proof, not a decomposition.

The following new auxiliary theorems are fully proved, all in
`AlgebraicGeometry.ProEtale.CondensedRing`:

- `integralLocalization_coconeLegs`
- `integralLocalization_cocone_map_isIso`
- `transportRegularTelescope`
- `integralRegularTelescope`
- `mappedScalar_isIso`
- `integralModuleLocalization_isColimit`
- `integralComplexLocalization_colimit`
- `integralScalar_derivedUnit_complex`
- `exists_integralLocalization_complex_model`
- `localizationCocone_isColimit_of_model`
- `integralLocalization_push_homology_isColimit`
- `integralLocalization_homology_isColimit`

The two exposed upstream scalar theorems were already proved and close no additional
hole. Cocones use explicit powers of the inverse scalar. The strict representative
is obtained from a proved representative theorem; colimit and inverse choices are
determined up to their stated universal-property equalities. No data is selected
from an unproved arbitrary existence statement.

## No longer needed

Removed the original proof-only imports
`Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`,
`Sheaf.Paper.CondensedQcqsPushforwardContinuity`, and
`Sheaf.Paper.ContinuousIntegralCoefficients` from the item. Coefficients and scalar
exactness remain available through its unchanged public scalar-exactness import.
Qcqs continuity remains used through the telescope-continuity theorem and is not
pruned. Of the original four proof-plan nodes, only
`def-weil-pbc-condensed-e-module-category` is no longer needed by this proof; its
statement-dependency entry is unchanged. The other three original nodes remain
needed transitively.

Removed the two proposed invertibility modules and their nodes
`lem-weil-pbc-continuous-module-ell-invertible` and
`lem-weil-pbc-continuous-scalar-ell-invertible` before landing, because the existing
integral-image module supplies their results. Removed the duplicate local tensor
unit proof and its direct Compatibility import from the module telescope. The
existing denominator module supplies the tensor API instead. Both existing modules
were already in the targets' import closure.

The item uses the specific bounded-below `RightDerivedFunctor.PlusCompatibility`
API. Proof-only imports use plain `import` or `import all`; public imports supply
types and exposed definitions. In particular the public integral-image import of
`ContinuousIntegralLocalization` supplies the public scalar theorem used in its
exposed cocone construction. No private helper enters an exposed definition.

A fresh source import-closure comparison from `TargetsCheck` finds zero newly
reached existing modules and zero existing modules pruned. All eleven new support
modules are reached. No existing Lean module is withdrawn. The unit record
`dag/units/sk-thm-properbasechange.json` and its `realized` fields are unchanged.

## Where the brief, the DAG or earlier work was wrong

The return at ac838e96a identified a duplicate private point-invertibility proof.
The first repair reused the point theorem but missed the stronger existing module
and derived invertibility theorems immediately below it. The current second
reading found and removed both duplicate new modules. It also found the already
proved tensor-unit formula in `ContinuousConstructibleIntegralDenominators` and
removed the remaining local copy. No mathematical statement is disputed.

The original DAG's two-step localization/continuity plan is valid, but the new
proved interfaces make its unit compatibility, strict representative, and leg
transport explicit. Node proof metadata now records the actual existing scalar
and tensor APIs. No target, existing statement, definition, or unit route changes.
The earlier second-reading reports are retained only as local history in
`scratchpad/historical-report.md`; this report describes the final delivery.

## New nodes

`def-weil-pbc-integral-localization-telescope`: explicit scalar sequences,
identity-component additive-functor comparisons, localization-unit cocones, and
universe-lifted reindexing. Its scalar inverse uses the existing public derived
theorem of the integral-image module.

`lem-weil-pbc-integral-localization-legs`: induction on the index and cancellation
at the target identify all legs from the zeroth leg.

`lem-weil-pbc-integral-localization-mate`: the resulting morphism between two
mapped colimit cocones has an invertible vertex map.

`lem-weil-pbc-integral-regular-telescope`: the normalized scalar sequence of the
regular module is colimiting, with zeroth leg the coefficient inclusion; the
existing presheaf telescope is reused.

`lem-weil-pbc-integral-module-telescope`: tensor the regular telescope and use the
existing extension-tensor unit formula to identify the canonical module cocone.

`lem-weil-pbc-integral-complex-telescope`: evaluation in each degree gives the
complex telescope and its specified unit leg.

`lem-weil-pbc-integral-derived-unit`: exact derived adjunction factorization and
uniqueness of left adjoints identify the termwise unit with the specified unit.

`lem-weil-pbc-integral-localization-complex-model`: a proved strict representative,
good truncation, and all leg equations give the localization model.

`lem-weil-pbc-integral-localization-colimit-transport`: representative and vertex
isomorphisms transport colimits using the model's leg equations.

`lem-weil-pbc-integral-localization-push-continuity`: apply the existing uniformly
bounded-below qcqs continuity theorem to the strict model.

`lem-weil-pbc-integral-localization-homology-colimit`: exact filtered colimits of
module sheaves and the cohomology factorization give the other required colimit.

## Second reading by B2

1. **Unchanged interfaces: pass after the declared visibility repair.** I read all
   delivered modules and diffed both existing files against the repository. The
   item's theorem signature and public import are byte-identical. The supplying
   integral-image module differs only by the two `private` removals and their new
   docstrings; a text comparison verifies every proof and mathematical signature
   unchanged. The module is unclaimed. Both change records enumerate all nine
   downstream modules and the direct users added here. Repository-wide search
   finds no pre-existing external uses of the helper names. No downstream
   statement changes meaning, and no existing definition or target is altered.

2. **Proofs and axioms: pass.** I compiled the final thirteen-file set with
   `lcompile.py --all`, without errors or warnings, and checked all 23 public
   theorem, definition and structure names explicitly with `#print axioms` in a
   scratch copy. Every one uses only the three permitted axioms; no `sorryAx`
   remains even in the final comparison. The cache contains precisely the thirteen
   current delivery modules, with no copies of the two removed modules or unrelated
   dependencies. I checked the cocone construction, degreewise colimit reflection,
   exact derived-unit factorization, strict representative, and colimit transport.
   The data are actual constructions or choices from proved universal properties;
   none depends on an unproved arbitrary witness.

3. **Auxiliary statements and search: pass after removing duplicates.** No statement
   is split off with `sorry`, and none restates the final pushforward comparison.
   I found the existing `module_nsmul_isIso`, `derived_nsmul_isIso`,
   `extendComapTensorIso` and `extendUnit_tensor` by source searches with different
   names from the first worker, and reused them. Fresh LeanFinder search for an
   adjunction identifying localization with a repeated-multiplication colimit
   returned ordinary ModuleCat scalar-extension adjunctions, not the required
   continuous module-sheaf unit telescope. Fresh Loogle search found the already
   used `IsColimit.hom_isIso`. The existing coefficient telescope has no normalized
   transition statement, so the normalized regular telescope interface is needed.
   I checked the zeroth and successor leg equations, zero modules and complexes,
   and empty schemes. The generic cancellation arguments also cover scalars 0
   and 1 under their stated invertibility hypotheses. Finite dimensionality and
   upper bounds are absent from the reused scalar helpers and are not introduced.

4. **Route and pruning: pass.** I read Hemo--Richarz--Scholbach Lemma 5.3(1),
   Bhatt--Scholze Lemma 6.8.2(2), and the unit's source and realized steps. The
   proof uses localization followed by uniformly bounded-below continuity. In
   `mate_unit_comap` the actual adjunction mate supplies the zeroth unit identity;
   the leg lemma then supplies every later leg. Bounded-below preservation of
   Rf_* gives the bound for the target telescope. Derived homology detects the
   resulting isomorphism, and exact faithful restriction reflects it. I checked
   direct imports against their uses and the full source import closure. Only the
   unused universe bridge is removed from the original proof dependencies;
   coefficients, exactness, and continuity remain used. No unit step is bypassed,
   and no existing module is claimed as pruned.

5. **DAG agreement: pass after repair.** All twelve delivered node records have
   their Lean signature verbatim in the matching file, and each proof-dependency
   set is exactly the union of its steps' `uses`. Every dependency ID resolves.
   The existing item's node changes only `proof`, `proof_deps`, and
   `proof_origin`. New nodes retain their complete source, searches, creation,
   blueprint, chapter, unit and Lean fields. I removed the two unlanded duplicate
   nodes and replaced their uses with the existing integral-image node, naming
   the actual helpers explicitly. The module-telescope node also records the
   denominator module's existing tensor-unit API. The unit's `realized` fields
   are untouched.

Changed in this reading: removed both duplicate invertibility modules and nodes;
exposed and documented their two existing upstream scalar theorems without changing
the types or proofs; removed the local tensor-unit proof and reused the existing
denominator API; updated imports, proof metadata, change records, and this report.
The original comparison proof is retained except for the reused scalar theorem
names. Exactly one original hole is closed and zero holes are added.
