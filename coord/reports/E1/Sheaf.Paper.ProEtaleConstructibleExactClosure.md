## What changed

Proved `AlgebraicGeometry.Scheme.constructibleProEtale_exactClosure` with its exact
existing signature. The finite ring is lifted to the site coefficient universe;
the module category and the actual sheaf objects then agree definitionally.
The existing `proEtaleModuleRestriction_constructible_iff` and the proved
`CoefficientSerre.coefficient_constructible_iff` helper identify the two
constructibility predicates. The proof applies the public
`constructibleCoefficient_exactClosure` theorem and translates its hypotheses and
conclusions through this equivalence of propositions.

The two private proof imports are
`Sheaf.Paper.ProEtaleConstantModuleConstructibility` and
`all Sheaf.Paper.ConstructibleCoefficientSerre`. The latter exposes the existing
proved comparison helper only to this proof. No existing declaration, public
import, definition, instance, signature or visibility was changed. No consumer
needs adaptation. The item node's proof, proof dependencies and proof origin now
record this route. Its unit `sk-def-sf-operations` has no realized statement or
proof steps that this replacement could bypass.

The sandbox file compiled successfully through `lcompile.py` (6.1 seconds).
The source read was Stacks `proetale.tex`, `lemma-constructible-serre` (09B5),
with `sites-modules.tex`, `lemma-kernel-finite-locally-constant` (093U), and
`etale-cohomology.tex`, `lemma-constructible-abelian` (03RZ). The existing proof of
the reused theorem follows 09B5 through constructible etale origins and exact
comparison. The coefficient comparison lemmas explicitly include the empty
scheme, zero coefficient ring and the positive-stratum convention.

## Proved and sorry left

Closed one of the item's one original holes:
`AlgebraicGeometry.Scheme.constructibleProEtale_exactClosure`
(node `lem-weil-proetale-constructible-exact-closure`).
There are zero holes left in the item and zero holes added. No statements were
split off. This is a proof from existing proved comparison and exact-closure
declarations, not a decomposition.

## No longer needed

Removed these unused direct proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre`
- `Sheaf.RingTheory.WeaklyEtaleField`
- `WeilConjectures.ConstructibleSheaf.Refinement`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk`
- `Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition`
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`
- `Sheaf.AlgebraicGeometry.ProEtalePullbackLocallyConstant`
- `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`

The former seven-step local Serre/refinement plan is unnecessary in this module:
the already proved coefficient-universe theorem supplies the whole closure
argument. The former proof dependencies below are removed from this node's
direct proof dependency list. This is direct-dependency pruning only: no claim is
made that these modules disappear from the targets' transitive import closure,
and no declaration or module is withdrawn.

- `prop-weil-pbc-proetale-constant-ring-map`
- `def-weil-pbc-proetale-operations`
- `lem-sfb-proetale-object-inverse-image-restriction`
- `lem-pur-proetale-inverse-image-stalk`
- `def-weil-proetale-inverse-image`
- `def-weil-pbc-proetale-site`
- `lem-weil-pbc-weakly-etale-composition-base-change`
- `lem-weil-pbc-weak-etale-field`
- `lem-weil-pbc-weakly-etale-source-locality`
- `def-weil-proetale-locally-constant-sheaf`
- `def-weil-geometric-point`
- `lem-weil-proetale-constant-sheaf-stalk`
- `lem-weil-pbc-site-constant-restriction`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-exc-proetale-pullback-locally-constant`
- `def-weil-proetale-constructible-sheaf`
- `lem-weil-pbc-constructible-stratification-intersection`
- `lem-pur-proetale-module-pullback-composition`
- `lem-weil-pbc-locally-constant-derived-serre`

The replacement proof uses only
`lem-weil-pbc-proetale-constant-module-constructibility` and
`lem-weil-constructible-coefficient-serre` directly. The latter is used as a proved
tool from another unit; no unit-level route is changed. No new maintainer tool
approval was written.

## Where the brief, the DAG or earlier work was wrong

The original plan predates the proved coefficient-universe exact-closure module
and the constant-scalar constructibility comparisons. These now give a much
shorter route. The item statement is correct and was not changed. In particular,
the comparison does not replace the prescribed global finite partition by an
affine-local predicate or impose a nonempty-scheme or nonzero-ring condition.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
