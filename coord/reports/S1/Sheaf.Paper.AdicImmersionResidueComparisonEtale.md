## What changed

Proved `AlgebraicGeometry.Scheme.sfbImmersion_residueComparison_etale` in
`Sheaf.Paper.AdicImmersionResidueComparisonEtale`, with its statement unchanged.
No other existing Lean module is changed.

The private helpers construct the canonical constant-ring direct-image map and
identify its module direct image with fixed-scalar direct image, using the
identity on sections. The existing scalar-normalization theorem then supplies
the compatibility needed by the proved ringed-pullback adjunction. Two
uniqueness-of-left-adjoint comparisons identify the actual algebraic pullback
with comparison inverse image through the specified scalar and AsSmall
equivalences. Whiskering the existing geometric pullback square gives the
ordinary comparison for the displayed residue functors. Exactness makes the
universal derived comparison invertible, and the final isomorphism is the
composite with `mapDerivedCategoryFactors` and the termwise comparison.

Added proof-only imports of
`WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar`,
`Sheaf.CategoryTheory.RingedPullbackPresentationOnSites` (using its proved
private supplied-adjunction and continuous-ringed-topos helpers through
`import all`), `Sheaf.CategoryTheory.ConstantInverseImageScalarNormalization`,
and `Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived`.
Removed unused private fixed-site instance helpers; kept the public imports.
The item's node now records the actual three proof steps and their dependencies.

The generic ringed-pullback presentation and constant inverse-image scalar
normalization are tools from other units: they supply the adjunction for the
specified algebraic lift and its ring-level normalization, respectively. They
do not replace any step of `sk-lem-integral-models`. Their existing statements
and proved helper APIs avoid duplicating this theory. Any new cross-unit tool
approval is left to the maintainer; no `tool_uses` field was changed.

Validation: the entire module compiled without errors or warnings in 24.1 s
through `lcompile.py`. No definition, target statement, public signature or
public import was changed. The argument imposes no nonzero-ring or nonempty-site
assumption; the stated immersion and noetherian hypotheses are retained.

## Proved and sorry left

Closed the sole item hole:
`AlgebraicGeometry.Scheme.sfbImmersion_residueComparison_etale`
(node `lem-sfb-adic-immersion-residue-comparison-etale`).
One of one item holes closed, zero holes added, zero split-off statements.
There are no `sorry` declarations left in this module or added by this delivery.
The proof uses existing declared dependencies, including
`CategoryTheory.ConstantCompletion.constantInverseImageScalarNormalization`;
it does not claim to close their existing holes.

## No longer needed

No original public import was removed, and no module is withdrawn.
The planned direct dependency
`lem-weil-pbc-site-module-sheaf-constant-ring-equivalence`
(`Sheaf.CategoryTheory.SiteModuleSheafConstantRingEquivalence`) is not needed by
this proof. The specified residue functors use the explicit
`ConstantScalarRestriction.restriction.asEquivalence`; its normalized action,
its existing equivalence instance, and the sectionwise direct-image comparison
suffice. The node instead cites `lem-sfb-constant-scalar-restriction-tensor`.
This is a local dependency reduction; no claim is made that other users of the
old node can be pruned.

The stronger support-site coherence API is not imported: the already proved
`ProEtale.comparisonUpperStarUpperStarIso` gives the required ordinary square.
The comparison-pullback node itself remains a dependency. No completion-tower,
K-flat-resolution comparison or additional derived comparison lemma is needed;
exactness and the existing universal left-derived-functor API suffice.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The previous single-step proof plan omitted
the distinction between an arbitrary algebraic inverse-image presentation and
the supplied one used in `adicResidueComparison`. The existing ring-only scalar
normalization theorem and proved supplied-adjunction helper bridge that gap;
uniqueness of left adjoints then gives the specified ordinary functor comparison.
No further split of the residue-comparison obligation is necessary.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
