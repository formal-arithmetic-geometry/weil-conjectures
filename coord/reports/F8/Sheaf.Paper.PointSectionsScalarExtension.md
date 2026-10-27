## What changed

In `Sheaf.Paper.PointSectionsScalarExtension`, proved thirteen of the fourteen
original holed theorems. Public declarations, signatures, definitions and public
imports are unchanged. All added declarations are proved private helpers.

The ordinary sections comparison uses the profinite integer-tower isomorphism,
finite constant sections and sheafification evaluated at the final point. It
transports the ordinary module tensor across the coefficient-section ring
isomorphisms and has exactly the prescribed pure-tensor formula. No global
integral basis is needed for this comparison. The ordinary sheaf associator uses
the uniqueness of left adjoints to composed restriction of scalars; its unit
formula determines the normalized map, and linearity proves its formula on all
iterated tensors. This argument is first proved for arbitrary ring sheaves to
avoid repeatedly unfolding the completed coefficient limit.

Exactness, the counit-normalized exact-derived comparison, ordinary multiplication,
module multiplication and associativity, rationalization, constructibility and
invertibility of completion use the existing proved interfaces. Proof imports
expose private proved API lemmas where the original modules did not publish them.
The node records these auxiliary arguments and retains the original plan for the
main theorem. No other module is adapted; no definition or statement is repaired.

## Proved and sorry left

Closed thirteen original holes, all in namespace `WeilConjectures`:

- `pointCompletedSections_exact`
- `pointCoefficientTensors_exact`
- `pointSectionsTensor_existsUnique`
- `pointCompletedOrdinary_exact`
- `pointOrdinaryDerivedComparison_existsUnique`
- `pointOrdinaryTensorUnit_existsUnique`
- `pointOrdinaryTensorAssoc_existsUnique`
- `pointIntegralModuleUnit_existsUnique`
- `pointIntegralModuleAssoc_existsUnique`
- `pointCoefficientFieldTensor_exact`
- `pointTensorRationalization_existsUnique`
- `pointIntegralConstructible_iff`
- `pointConstructibleCompletionComparison_isIso`

One original hole remains: `WeilConjectures.pointSectionsScalarExtension`, node
`lem-weil-point-sections-scalar-extension`. Its proof remains exactly `by sorry`;
its existing complete proof docstring and six-clause statement are unchanged.
No holes were added or split off. This is a partial delivery of a multi-hole module,
not a completed proof of the main coherence theorem.

The remaining work is the ordinary unit/tower sections squares, descent of these
squares across the exact-derived identifications, cancellation of the completion
comparisons, and rational assembly. Attempted generator-square proofs are not
included as private holes. The ordinary child theorem for tower coherence already
states this mathematics, but uses its own normalized comparison bundle; identifying
that bundle with the present module's choices still needs an argument.

Edge cases checked in the constructions include identity coefficient maps,
zero sections/modules and arbitrary tensor generators. The associator argument
uses no injectivity or nonzero assumption on a section or module element.

## No longer needed

Removed the following direct proof imports:

- `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`

The used definitions remain available through the unchanged statement imports
and necessary proof imports. Direct continuous-coefficient and basis proofs are
replaced by final-object evaluation and the proved profinite tower. Direct K-flat
resolution arguments are replaced by the proved counit-normalized exact-derived
comparison. Module rationalization reuses `CoefficientComplexRationalization`.

No module is withdrawn and no source-library declaration is removed. No node is
claimed globally prunable: the unfinished main theorem and the tower-coherence
child still retain their planned dependencies. In particular the ordinary
comparison proved here does not authorize withdrawing
`PointFiniteFreeSectionsTensor` or `PointDerivedTensorTowerCoherence`.

## Where the brief, the DAG or earlier work was wrong

The declared finite-free and tower-coherence child results are specialized to a
finite-field datum and finite subfields of a fixed closure. Several auxiliary
statements in this module quantify over an arbitrary algebraically closed base
and arbitrary finite coefficient fields and homomorphisms. They cannot be closed
by direct application of those specialized statements. The general ordinary
comparison and associator above supply the needed auxiliary results without
changing their signatures.

The latest blueprint moved the point-fiber text to
`sec-six-functors-basics/sk-def-sf-admissible/def-weil-finite-coefficient-point.md`.
Its current paragraph is not the verbatim historical sentence in the retained
node's source record. No target or node statement is changed on that account.

Compiler performance required keeping selected limit and coefficient constructions
locally irreducible and isolating the general adjunction calculation. These local
attributes do not alter imported declarations or public data. No timeout limit is
raised and no proof is split into another file to meet the limit.

Validation: the full single-file compile passed in 52.3 seconds. The final large
unchanged theorem has a declaration-scoped `linter.all false`: its diagnostic
traversal alone took roughly fourteen seconds; kernel checking is unchanged.
All other declarations retain the usual lint checks.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
