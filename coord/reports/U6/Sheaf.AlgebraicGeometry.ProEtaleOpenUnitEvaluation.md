## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleOpenUnitEvaluation` in
`Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation`, with its statement unchanged.
The public composition and section-projection definitions are unchanged.

The constant-ring comparison is the sheafification/restriction compatibility isomorphism.
Its unit identity normalizes constants. The coefficient direct-image map equals the
specified constant-section map by the inverse law of the ring-sheaf adjunction's Hom
equivalence. Sheafification uniqueness and naturality on constants prove the two ring
identities required by `SheafOfModules.pushforwardPushforwardAdj`. Its right adjoint is
literally the specified module direct image. `Adjunction.leftAdjointUniq` compares its
restriction left adjoint with the actual published small-model/tensor pullback. Evaluation
gives the additive equivalences, linearity, and both naturalities. Finally
`Adjunction.unit_leftAdjointUniq_hom_app` gives the specified unit formula with the actual
first projection. Thus no arbitrary replacement of the pullback or unit occurs.

Added three proved private helpers: `openRingComparison`,
`openRingComparison_constant`, and `ringDirectImage_constant`. No public API was added.
Updated the existing DAG node's proof, proof dependencies and proof origin to this route.
The unit record has no realized statement or proof-step nodes here, so no unit route is
bypassed. The theorem still assumes a finite coefficient ring as originally stated.

Validation: the item with reduced imports compiled cleanly (10.1 seconds). A subsequent three-file
run compiled the item and both unchanged direct consumers in import order (6.3, 3.3 and
26.7 seconds). Those consumer copies were removed from the delivery. All compilation
used `lcompile.py`; no library build was run. The final version with the original public import API restored compiled cleanly in 6.7
seconds. A resumed check against the current library compiled cleanly in 6.1 seconds.
The delivery probe checks axioms.

No public import or declaration interface changes. An attempted reduction of four public
reexports compiled with both direct consumers, but broader source analysis found that
54 transitive consumers obtain part of their visible API through these reexports.
The final version retains the original public imports for compatibility. The five unused
proof-only imports are removed; the three new imports are proof-only.
No consumer adaptation or change record is needed.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.proEtaleOpenUnitEvaluation`
(node `lem-pur-proetale-open-unit-evaluation`). Added 0 holes. There are no remaining
`sorry`s in the item and no new modules or split-off obligations. This is a proof, not a
decomposition. The existing dependencies of the published operations remain as before;
this delivery does not claim their remaining obligations are closed.

## No longer needed

Removed imports:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` (its interface remains available through
  the retained public imports and is still used; only the redundant direct import is removed)

The existing public reexports of ModuleDerivedCategory, ProEtaleWeaklyEtaleLocalization,
SfIntrinsicRealizationTransport and ProEtaleConstantExact are retained for consumers.
Their theorems are not needed in this proof. In particular the weakly-etale localization
node remains a proof dependency for the continuity and cocontinuity facts specialized
directly from the upstream Proetale module, but its large packaged equivalence theorem
is unnecessary here. The existing
Mathlib leaf `lem-pur-ring-presheaf-sheafification-localization` supplies the general
sheafification compatibility used by the coefficient calculation.

Removed direct proof dependencies:
`def-pc-fibre-product`, `def-pur-sheaf-tensor-product`,
`def-weil-pbc-proetale-modules`, `def-weil-size-convention`,
`lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`,
`prop-weil-pbc-proetale-constant-exact`, and
`prop-weil-pbc-proetale-constant-ring-map`.
The actual inverse image, tensor construction, coefficient identification, and adjunction
are retained through the operations interface. Their correctness is not bypassed:
uniqueness compares the actual adjunction, including its unit, with restriction.
No separate comma-category, colimit, small-model, or pure-tensor calculation is needed.
No library module is withdrawn; these dependencies can have other users.

## Where the brief, the DAG or earlier work was wrong

The planned seven-step pointwise Kan/tensor computation is longer than necessary once the
published module adjunction exists. Mathlib already constructs the restriction adjunction
from the site adjunction and the two ring compatibility identities; uniqueness of left
adjoints includes the needed unit normalization. This shorter route preserves every
hypothesis and conclusion. The initial compile-service retries returned no-answer messages;
subsequent compiles succeeded, so this is not a remaining blocker.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
