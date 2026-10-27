## What changed

The existing presentation records are relocated verbatim to
`AlgebraDiagramPullbackData` and publicly re-exported by the item. The auxiliary
modules construct exactness, normalized scalar presentations, ordinary restriction
and coefficient comparisons, their derived descent, and the unit and coefficient
naturality equations. The original theorem signature is unchanged. The main theorem is reduced to the
named ambient balancing constituent; its remaining hole is reported below.

## Proved and sorry left

The item originally had one hole, in
`CategoryTheory.AlgebraDiagramPullback.algebraDiagramPullbackExtensionCoherence`.
Its body now assembles the comparison and naturality data without `sorry`.
The packet currently adds one hole:
`CategoryTheory.AlgebraDiagramPullback.ambient_balancing`
(node `lem-pur-algebra-diagram-ambient-balancing`). This is the balancing identity
from parent proof steps 3–4, a strictly separate constituent; the
hole accounting is a decomposition (one closed, one added), not a net proof.
No definition contains a hole. All other new theorem bodies are written and have
compiled. The ordinary balancing identity was proved and compiled in the scratch verification
module. The cochain lift and one-coefficient ambient representative calculation
remain constituents of the named balancing split; temporary scratch modules are
excluded from the delivery. Scratch files are
excluded from the delivery.
Continuation audit: scalar-evaluation factorization was verified in diagnostic work.
The full balancing draft still has unclosed cochain single-factor and ambient
normalization calculations; it is preserved only in scratchpad and is not delivered.
The retained balancing statement is the sole new hole, not a proved result.

The balancing statement includes zero rings and zero modules; both routes are
then the unique zero maps. For identity pullback it reduces to naturality of the
fixed scalar tensor presentations. It assumes neither coefficient flatness nor
that a scalar-extension unit is invertible.
`AlgebraDiagramPullbackData`, `AlgebraDiagramExactness` and
`AlgebraDiagramAmbientSpecialization` have finished clean compilation.
`AlgebraDiagramScalarPresentation`, `AlgebraDiagramOrdinaryComparisons`,
`AlgebraDiagramOrdinaryUnitNaturality`, and `AlgebraDiagramScalarUnitNaturality`
have also compiled cleanly, including checks after import pruning.
`AlgebraDiagramThetaNaturality` compiled cleanly, including a separate check.
Derived descent compiled cleanly after removing unused tactics and its unused
scalar-normalization import. The extension-unit theorem and the main assembly have compiled successfully in
37.8 and 8.4 seconds respectively. Making category and universe arguments explicit
avoids expensive elaboration of the adjunction mate. The final cleanup check compiled without warnings: extension-unit (54.9 seconds),
main assembly (8.5 seconds), the unchanged direct consumer TowerChernPullback
(45.2 seconds), and its unchanged consumer TowerP1KernelScalarNormalization
(55.3 seconds). Both consumer sources are temporary validation copies, excluded
from the delivery.
The combined DAG closure has 560 nodes and no cycles or missing dependencies;
the non-Mathlib Lean import closure has 1,024 modules and no cycles or missing
source modules. The item signature and relocated declaration block were compared
verbatim against the shared originals.

## No longer needed

The constant-left-module inverse-image proof is unnecessary because the theorem
already assumes both structural coefficient maps are isomorphisms. The proof does
not use `lem-pe-constant-left-module-inverse-image` or its module
`Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`; its old tool approval is
removed from the parent route.

The original main module's eight proof imports were removed from the data module:
`ExactPullbackSignedComparison`, `GeometricInverseImageExact`,
`ConstantLeftModuleInverseImage`, `SheafRingDerivedCoefficientAdjunction`,
`KFlatResolutionIndependentCoefficients`,
`KFlatTensorPreservesQuasiIsoIndependentCoefficients`,
`SiteDerivedTensorDescentIndependentCoefficients`, and
`Mathlib.CategoryTheory.Localization.Predicate`.
The exact pullback, resolution and tensor descent tools are still used through the
proved constituents; their modules are not claimed globally unnecessary. The
normalized scalar adjunction is obtained from the existing normalization theorem.
No source-library declaration is withdrawn or weakened.

Redundant proof imports removed from the new scalar-presentation module are
`GeometricInverseImageExact`, `ScalarExtensionRingIso`, and
`SheafRingCoefficientOrdinaryAdjunction`. The same three, together with
`ExtensionTensorComparisonIndependent`, were removed from scalar-unit naturality.
Its scalar-normalization import is retained: removing it leaves unresolved
universe constraints in the representative comparison.
Ordinary comparisons no longer import `GeometricInverseImageExact`,
`ModuleTensorGenerators`, or `SheafRingCoefficientOrdinaryAdjunction`.
Ordinary-unit naturality uses only ordinary comparisons, coefficient arrows and
module tensor generators; its redundant imports of geometric exactness,
`RingedTopoiCanonicalTensorPullbackUnitExistence`,
`FlatRestrictionOrdinaryComparisons`, `ScalarExtensionRingIso`, and
`SheafRingCoefficientOrdinaryAdjunction` were removed. Derived comparisons no
longer import `KFlatScalarComparisonNormalization`.
These removals simplify proof imports and do not claim that those modules are globally unused.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned cochain coherence declarations provide
two-variable monoidality, but do not state the one-coefficient specialization
needed in steps 3–4. The new balancing node isolates this genuine normalization
calculation; the other constituents are proved from existing declarations.
The unit's `realized` statement and
step lists are empty; no realized unit route is bypassed. During this session a
draft edit was accidentally applied to the shared item file; it was immediately
restored and compared against the saved original. All intended work is in the
sandbox. Several compiler clients were interrupted by provider termination; their
returned results were checked before resubmission.

## New nodes

`def-pur-algebra-diagram-pullback-data`: Fix small ringed sites, a ringed geometric pullback with an algebraic inverse-image presentation, and a compatible square of algebra coefficients. Use module sheaves, unbounded derived categories and the published tensor comparison. Define coefficient modules, scalar tensor presentations, exactness records, normalized units and two-resolving-factor tensor formulas, normalized scalar association, and the Coherence and Result records with their actual coefficient-map naturality equations. These are exactly the existing declarations of the parent node, relocated without changes of signatures or bodies.

`lem-pur-algebra-diagram-ambient-balancing`: For a ringed geometric pullback with invertible structural coefficients and a compatible algebra square, fix normalized scalar derived presentations, an ordinary restriction comparison with its generator equation, a scalar-association derived isomorphism normalized by kappa, a coefficient isomorphism with its generator equation and an ambient tensor isomorphism normalized on two resolving factors. Then the localized restriction comparison followed by underlying scalar association equals the ambient coefficient specialization at every derived object.

`lem-pur-algebra-diagram-ambient-specialization`: Given an ambient tensor comparison for an exact ringed pullback, normalized source and target scalar presentations and a degree-zero coefficient isomorphism, explicitly specialize the ambient comparison at that coefficient and conjugate by the scalar tensor presentations. This gives a natural isomorphism with the displayed component composite.

`lem-pur-algebra-diagram-derived-comparisons`: For exact pullback and scalar restriction on a compatible coefficient square, localize the ordinary restriction square with the specified factorization formula. Exact pullback preserves flat-term K-flat resolving objects and has an ambient tensor isomorphism normalized on two resolving factors. For any normalized scalar presentations on source and target, balanced scalar association descends to an extension isomorphism with exactly the stipulated cochain kappa normalization.

`lem-pur-algebra-diagram-exactness`: For any morphism of commutative ring sheaves, restriction of module scalars preserves finite limits and colimits. A geometric module pullback with invertible structural coefficient map also preserves finite limits and colimits.

`lem-pur-algebra-diagram-extension-unit`: Given normalized source and target scalar presentations, ordinary restriction with its generator normalization, and a derived scalar-association isomorphism normalized by kappa, the composite of derived restriction and underlying scalar association carries the source scalar unit to the target scalar unit, for every unbounded derived object.

`lem-pur-algebra-diagram-ordinary-comparisons`: For a compatible algebra coefficient square over a ringed geometric pullback whose two structural coefficient maps are isomorphisms, there are natural ordinary restriction and coefficient-module isomorphisms with precisely the parent generator equations.

`lem-pur-algebra-diagram-ordinary-unit-naturality`: For the ordinary normalized restriction and coefficient comparisons of a coefficient square, scalar association commutes with the scalar extension units. Comparisons of the underlying coefficient modules commute with compatible maps of ring sheaves represented by their actual sectionwise module maps.

`lem-pur-algebra-diagram-scalar-presentation`: On a small ringed site, for any algebra extension with exact restriction and existing unbounded derived categories, there is a ScalarDerivedPresentation: the ordinary extension functor with its specified object equality, a normalized derived adjunction unit, and the normalized underlying tensor isomorphism on two flat-term K-flat resolving factors.

`lem-pur-algebra-diagram-scalar-unit-naturality`: For two algebra extensions of the same ring sheaf and normalized scalar derived presentations, any coefficient module map given sectionwise by an algebra map carries the first scalar unit to the second under scalarUnderlyingMap, on every unbounded derived object.

`lem-pur-algebra-diagram-theta-naturality`: For any two Coherence presentations over the same exact base pullback, if their degree-zero coefficient isomorphisms commute with given coefficient module maps, their ambient scalar specializations commute with the induced scalarUnderlyingMap on source and target, for every derived object.

Change record: `coord/changes/M4-algebra-diagram-pullback-data.md`.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
