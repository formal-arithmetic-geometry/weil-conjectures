## What changed

Filled `SheafOfModules.coefficientSystemUnboundedComparison` without changing its
statement or any existing public import. All new imports and helpers are private
to this proof. The construction uses normalized localization, common free adapted
resolutions, and the mates correspondence. Updated the node to this route.
The localization, square, transition and resolution arguments use abstract private
helpers, so Lean does not repeatedly unfold the concrete coefficient-site data.

## Proved and sorry left

Closed the one original hole in
`SheafOfModules.coefficientSystemUnboundedComparison`. Added zero holes. No `sorry`
remains in the delivered module, and no new statement is split off.

The complete item module compiled through `lcompile.py` with exit code 0,
no warnings, in 52.5 seconds. The theorem statement and the original public import
were compared verbatim against the shared source and are unchanged. The node's
only changed fields are `proof`, `proof_deps` and `proof_origin`.

## No longer needed

The original module had no proof imports to remove. During implementation the
unused proof imports `Sheaf.CategoryTheory.DerivedCategory.NormalizedAdjunctionComposition`
and `Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived` were removed.
The proof also no longer imports
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`: the tensor
sheafification comparison from the adapted-resolution module needs no chosen
internal Hom.

The following declared proof dependencies are not needed by this proof:

- `def-pc-sheaf-restrict-scalars`
- `lem-galois-yoneda-fully-faithful`
- `lem-pc-kflat-resolution`
- `lem-pc-derived-adjoint-functors`
- `lem-pc-pre-derived-adjoint-functors-general`
- `lem-pur-coefficient-evaluation-derived-left-adjoint`
- `lem-pur-derived-change-of-rings`
- `lem-weil-pbc-exact-functor-derived-factorization`
- `lem-weil-pbc-exact-functor-derived-functor`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-weil-pbc-ringed-pullback-preserves-kflat`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-ringed-topoi-module-adjunction`
- `lem-weil-pbc-termwise-adjunction-homotopy`
- `prop-pur-kinjective-resolutions-exist`

Mathlib supplies exact derived functors, derived adjunctions and their normalized
unit formula directly. Ordinary tensor and extension comparisons follow from
mates and uniqueness of adjoints. Common free adapted resolutions suffice instead
of a theorem asserting preservation of every K-flat complex. Restricted direct
image and transition compatibility follow by taking mates, so the separate
pushforward-composition, tensor-pullback and Yoneda wrappers are unnecessary here.
The corresponding modules omitted from the proof imports are
`Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`,
`Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`,
`Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`,
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`,
`Sheaf.Paper.KFlatRingedToposPullback`,
`Sheaf.CategoryTheory.KInjectiveTotalDerived`,
`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`,
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsMixedUniverses`, and
`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`. The restriction, Yoneda and
exact-factorization nodes are Mathlib leaves or have no separate attached module.

`Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint` remains required through the
unchanged public import of `CoefficientSystemImageData`: its package is a statement
dependency. Its existence theorem is not used in this proof because PY and PX are
already inputs. Likewise ordinary scalar restriction remains part of the prescribed
interface, although its separate node supplies no additional proof here.

No existing library declaration or module is deleted, and no pruning claim is
made for other consumers of these dependencies. The unit has no realized nodes.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The DAG route is longer than necessary: the
ordinary normalized right adjoints and exact squares already determine the tensor
comparisons by mates, and a common adapted resolution avoids a general K-flat
preservation theorem. Evaluation is never assumed to preserve K-injectives.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
