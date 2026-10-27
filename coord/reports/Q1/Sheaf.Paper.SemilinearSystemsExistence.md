## What changed

`Sheaf.Paper.SemilinearSystemsExistence` retains its public import, structures and theorem
statement. The proof now establishes Grothendieck abelianness, componentwise exactness,
triangulated evaluation and joint detection of derived isomorphisms. It then assembles
three smaller construction packages and proves the specified Hom transition equation.

The transition argument is complete Lean: scalar adjunctions turn naturality of the
constructed derived transition into naturality of reduction; tensor-reduction compatibility
and the evaluation normalization identify the untransposed Hom reduction. Cancelling tensor
with the cartesian reduction and applying the tensor-Hom adjunction gives the displayed
transpose, including its inverse cartesian comparison. Equality is never inferred merely
from agreement after evaluations.

The three new modules each state one remaining construction theorem. The scalar package
has no closed structure or Hom data; the tensor package has no cartesian Hom comparison;
the Hom comparison assumes these packages and asserts no transition law. Thus none
repackages the original existence obligation. All new data are structure fields;
no definition selects an arbitrary witness of an unproved existence statement.

## Proved and sorry left

Closed the sole original textual hole:
`WeilConjectures.SemilinearSections.semilinearSystemData`
(`lem-coef-semilinear-system-existence`). This is a decomposition, not a net proof gain:
one original hole is closed and three strictly smaller holes are added (net -2).

The new holes, and the only direct holes in this delivery, are:

- `WeilConjectures.SemilinearSections.systemScalarCoherence_nonempty`
  (`lem-coef-semilinear-scalar-coherence`): scalar adjunctions, left-adjoint composition
  comparisons and the system reduction cocycle.
- `WeilConjectures.SemilinearSections.systemTensorCoherence_nonempty`
  (`lem-coef-semilinear-tensor-coherence`): closed tensor models and their normalized
  evaluation, scalar and reduction compatibilities.
- `WeilConjectures.SemilinearSections.systemCartesianHomEvaluation_nonempty`
  (`lem-coef-semilinear-cartesian-hom-evaluation`): the evaluation-normalized comparison
  of internal Hom for a cartesian first input.

The item module contains zero direct holes. Its private helpers are proved, including
`systemsGrothendieck`, `evaluationTriangulated`, `systemsIsZero`, `systemsComponentwise`,
`evaluationDetects`, `derivedEvaluationDetects`, `reductionNaturality`,
`tensorHomTranspose` and `homReductionFormula`.

Validation: remote `lcompile.py --all` compiled the three new modules in 8.9 s,
9.2 s and 7.3 s. After correcting the top proof, remote single-file compilation
of the item passed without errors or warnings in 20.2 s. Every delivered module
is below the 60-second limit. The delivery command runs the required preflight.

## No longer needed

Removed these proof imports from the item module:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`

The remaining private imports provide the three new construction packages,
independent-universe Grothendieck abelianness, the derived homology isomorphism criterion,
and the exact-functor/homology comparison. The public import is unchanged.

The original dependency nodes for site construction, module adjunctions, K-flat resolutions,
derived change of rings, tensor descent, derived adjunctions, internal Hom, global sections
and Yoneda remain needed inside the new construction obligations. They are redistributed,
not globally pruned. The item itself now needs only the new packages and the direct
abelian/derived evaluation infrastructure, as its updated node records. No module or
blueprint-unit step is withdrawn. Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

Zheng's Lemma 4.10 concerns commutation of evaluation with direct image. The cartesian
internal-Hom comparison used here is Proposition 4.17(a), printed pp. 25-26. Construction
4.1, printed p. 21, gives the sequence topos and the evaluation adjoints. The new modules
cite Proposition 4.17, and the updated proof origin records it. The existing public
statements and their docstrings are preserved.

The original proof's componentwise exactness and joint detection are formalized directly
from the existing exact evaluation; no extra existence theorem is introduced for them.
The new tensor obligation explicitly includes compatibility with reduction maps, which
is necessary to prove the Hom transition law from actual maps.

`blueprint_refs.py ancestor lem-coef-semilinear-system-existence` reports no ancestor
because this node's `created.item` names a Lean module. The inherited parent chain through
`lem-coef-semilinear-derived-sections` identifies
`prop-coef-integral-exceptional-adjoint`; the new nodes record that mathematical ancestor
and the intermediate nodes. No maintainer-owned ancestry fields are changed.

Edge cases checked in the statements and arguments: empty sites, zero ring sheaves,
zero complexes and identity indices require no excluded cases. Scalar extensions are
resolved before tensoring, so no flatness of coefficient homomorphisms is assumed.
The unit record has empty `realized.statement` and `realized.steps`; its route is preserved.

## New nodes

`lem-coef-semilinear-scalar-coherence`:
`lean/Sheaf/Paper/SemilinearScalarCoherence.lean` isolates the scalar portion of original
steps 4-6, including normalization and the reduction cocycle.

`lem-coef-semilinear-tensor-coherence`:
`lean/Sheaf/Paper/SemilinearTensorCoherence.lean` isolates the tensor and closedness
construction of original steps 3, 6 and 7, including the tensor-reduction square proved
on pure tensors before descending.

`lem-coef-semilinear-cartesian-hom-evaluation`:
`lean/Sheaf/Paper/SemilinearCartesianHomEvaluation.lean` isolates the projection-isomorphism
and Yoneda part of original steps 8-9. The Hom transition conclusion is proved in the item.

All three nodes have source proofs, actual logged LeanSearch/LeanFinder/Mathlib grep
searches and unchanged site/coefficient universes. No change record is needed: no
existing declaration signature, definition or exported import is changed.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
