## What changed

Proved `AlgebraicGeometry.Etale.properSmoothCurves_finiteModule_higherDirectImage_constructible`
with the original signature, docstring and public imports unchanged. The proof splits the base
into its zero- and one-dimensional fibre loci. It uses finite direct-image vanishing and the
connected-fibre degree-zero theorem on the first, and the existing prime-coefficient theorem
and proved source coefficient devissage on the second. Exact open restriction and open-cover
constructibility glue the result. Private proved helpers compare fibre dimensions and the
bounded-below and total derived models.

The shorter coefficient route restricts scalars along `ULift (ZMod (ringChar R)) →+* R`.
The source devissage theorem has no invertibility hypothesis. It handles zero coefficients,
the characteristic-one ring, empty loci, and negative degrees. Every retained proof import
supplies a declaration explicitly used by the proof. Updated the existing DAG node's proof,
proof dependencies and proof origin to describe this route. No public interface, definition,
consumer, or unit-level route changes; no change record is needed.

## Proved and sorry left

Closed the original one hole in
`AlgebraicGeometry.Etale.properSmoothCurves_finiteModule_higherDirectImage_constructible`.
The delivered module has zero holes; zero holes added, zero split off. All private helpers
are proved. The required initial dry run passed compilation and preflight (AUTO); final
validation includes the route metadata and this report. No claim is made that all imported
theorems have themselves been proved in this delivery. A separate full-file compile
with `#print axioms` succeeded in 36.1 seconds: it reports `propext`, `Classical.choice`,
`Quot.sound`, and inherited `sorryAx`. There is no local `sorry`; the imported proof
closure still contains project holes, as allowed by this stage.

## No longer needed

Removed these direct proof imports (the original public imports remain):

- `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`
- `Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf`
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.LinearAlgebra.Basis.VectorSpace`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible`
- `WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor`
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`

Removed these direct DAG proof dependencies, whose arguments are replaced by the existing
source coefficient, finite-image, restriction and constructibility APIs:

- `lemma-constructible-hom-constant-locally`
- `def-weil-pbc-constructible-abelian-sheaf`
- `def-weil-pbc-etale-constructible-sheaf`
- `lem-weil-pbc-exchange-forget-coefficients`
- `lem-weil-pbc-constant-sheaf-geometric-stalk`
- `lem-weil-pbc-etale-restriction-injectives`
- `lem-weil-pbc-site-pullback-abelian-exact`
- `lem-weil-pbc-etale-quasifinite-shriek-constructible`
- `def-weil-pbc-extension-by-zero`
- `def-sbc-smooth-morphisms`
- `def-weil-pbc-scheme-conventions`
- `def-weil-proper-morphism`
- `def-sbc-locally-finite-presentation`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `lem-weil-pbc-vector-space-free`
- `lem-weil-pbc-sheafification-exact`
- `lem-weil-pbc-right-derived-universal-delta-functor`
- `thm-constructible-serre`
- `lem-weil-pbc-module-direct-image-left-exact`
- `lem-weil-pbc-module-sheaves-enough-injectives`

The coefficient conversion no longer passes through our separate abelian constructibility,
forget-coefficients, free-vector-space or universal-delta-functor constructions. The
zero-dimensional branch no longer uses a quasi-finite shriek compactification or its qcqs
permanence lemmas. Some source implementations still use related general results
transitively; these are direct route removals, not an assertion of global unreachability.
The dimension-loci and prime-coefficient nodes remain required, and the existing
connected-fibre degree-zero and module-constructibility comparison nodes are used.

## Where the brief, the DAG or earlier work was wrong

The retained candidate was complete but earlier attempts could not load the published
CoefficientDevissage and RingScalarExtension objects. The initial dry run in this session
now compiles it and passes preflight; that publication problem is resolved. Reused the
retained LeanFinder, Loogle, LeanSearch and source-search records. Source inspection verifies
that the general ZMod devissage theorem requires no invertibility, unlike its final wrapper.
The planned finite-free prime-field reduction is therefore unnecessary. The source
cardinality induction is a shorter implementation of the same finite-coefficient argument.

The target module is not itself a unit statement or unit proof step in
`dag/units/sk-thm-properbasechange.json`; that unit's realized route is unchanged.
All newly used API declarations already exist and are proved in the source library;
there are no new statements, new modules, or new DAG nodes in this delivery.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
