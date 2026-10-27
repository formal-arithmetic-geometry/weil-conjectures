## What changed

Proved `SheafOfModules.LocalizedStrictTensor.localized_strict_tensor_descent`.
The proof constructs universal reduction models, conjugates ordinary comparisons
by their computation counits on resolving complexes, and descends using fully
faithful restriction to these representatives. It proves uniqueness and
coefficient naturality by the same faithfulness. For each coefficient level it
constructs both scalar evaluation models and the linear projection comparison,
then proves the evaluated square by pasting the four counit equations and
cancelling the invertible scalar counit. Every private helper is proved.

The only imported unfinished mathematical result newly used directly is the
existing generator-coherence theorem, whose ordinary comparison, linear lifts,
unit equations, and coefficient square are exactly its published interface.
This universal generator normalization determines the ordinary maps, including
their scalar-unit values; the choice does not supply unconstrained data.
Universal scalar-extension models are taken from the existing proved existence
theorem. Choices are of universal derived pairs determined up to their unique
counit-compatible isomorphism; there is no arbitrary data witness.

Made the coefficient family explicitly use the existing reduction as its object,
retaining its original maps and functor laws. Refactored the existing Data and
LinearEvaluation modules to share the exact
normalization equations, the exact-derived-square construction, and the evaluated
square equation. This preserves
the old formulas by unfolding, and prevents large repeated elaboration of the
localized extension functor. No target signature or source-library declaration
was changed. Changes are recorded in
`coord/changes/U1-localized-strict-normalization.md` and
`coord/changes/U1-localized-strict-linear-normalization.md`.
The Data node records the five shared concrete definitions. The item node now
follows the implemented counit descent and pasting proof; unit route retained.

## Proved and sorry left

Closed the one original hole:
`SheafOfModules.LocalizedStrictTensor.localized_strict_tensor_descent`
(node `lem-sf-cbc-localized-strict-tensor-descent`).

Holes closed: 1. Holes added: 0. Holes left in the item: 0. No split-off theorems.
The adapted definition modules have zero holes. The imported existing
`SheafOfModules.SliceTensorGenerator.coherence_exists`
(node `lem-sf-cbc-slice-tensor-generator-coherence`) remains an upstream proof
item; it is not copied or changed in this delivery.

## No longer needed

The implemented route does not use these declared proof dependencies:

- `lem-sf-cbc-diagonal-resolving-complexes`
  (`Sheaf.Algebra.Homology.DiagonalResolvingComplexes`): the actual strict reduction
  inverts quasi-isomorphisms between resolving complexes directly, via the
  already proved `StrictReduction.reductionInverts`.
- `lem-sf-cbc-strict-tensor-model-evaluation`
  (`Sheaf.Algebra.Homology.StrictTensorModelEvaluation`): derive the ordinary
  reduction itself and use its universal computation counit; evaluation is
  constructed from the ordinary scalar lift and the scalar counit.
- `lem-sf-cbc-coefficient-linear-projection-descent`
  (`Sheaf.Algebra.Homology.CoefficientLinearProjectionDescent`): the generic
  exact-comparison argument constructs the linear comparison directly; the
  generic pasting calculation proves its required compatibility.

These are no longer needed by this proof, not assertions that their declarations
or other consumers can be removed. No module is withdrawn. The broader
site-derived descent and localization tools remain used through the existing
proved `cochainDerivedExists`, `cochainRepresentativeWhiskering`, and resolving
class API in `Sheaf.Paper.ReductionPullbackDerivedTower`.

Removed direct proof imports:

- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionExistence`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionUniqueness`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`
- `Sheaf.Paper.RestrictionDerivedProducts`
- `Mathlib.CategoryTheory.Adjunction.Limits`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`

Their required general infrastructure is available through the retained proof
modules; the removed direct imports supply no additional step. All original
public imports are retained verbatim.

Removed obsolete item `tool_uses` entries for ringed-open-total-tensor-kflat,
ringed-slice-extension-tensor, diagram-site-realization,
cochain-pullback-tensor-coherence, site-one-sided-tensor-normalization,
sheafification-bilinear-extension existence and uniqueness,
ringed-topoi-derived-pullback, and restriction-derived-products. Their old direct
roles are replaced by the actual universal reduction and generator coherence;
underlying facts still used inside those imported results retain their own nodes.

## Where the brief, the DAG or earlier work was wrong

The original plan required diagonal tensor models and a separate coefficient
projection descent. Those are unnecessary for this statement: its
`ReductionModel` asks for a universal left-derived ordinary reduction, which is
already constructible from the resolving-class localization API. Descending
counit conjugations also proves evaluation, without constructing a diagram-site
tensor model. The normalization and every conclusion clause remain the same.

The old expanded normalization and exact-square definitions were mathematically
correct, but repeatedly unfolded equivalent ring-sheaf and functor presentations
during elaboration. The shared concrete definitions give the same equations a
usable interface. No disputed or weakened statement is introduced.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
