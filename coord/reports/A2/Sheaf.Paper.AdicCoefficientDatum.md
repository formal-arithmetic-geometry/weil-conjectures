## What changed

Completed the five remaining proofs of `Sheaf.Paper.AdicCoefficientDatum` without changing
any existing declaration signature or public import. Retained and checked the earlier
sandbox's tensor-generation helpers, transition construction, balancing naturality and
cocycle, and comparison by localization on K-flat representatives. Used the existing K-flat
scalar-extension theorem on resolutions with flat terms.
Naturality and the preservation of quasi-isomorphisms carry the normalization formula
from those resolutions to every K-flat complex.
Derived evaluation compares the tower and scalar counits on the same ordinary complex.
The ordinary complex and balancing declarations are moved earlier, with unchanged bodies,
so the transition proof can use them. Private helpers are proved in this module.
Explicit alias normalization, the proved scalar-extension witness equality, and a
tensor-presentation naturality API avoid repeated unfolding of the chosen functor.
The component comparison and exact-counit naturality APIs keep the evaluation proof
from repeatedly unfolding natural-transformation records.
The K-flat transfer uses the inverse of the tensor-presentation isomorphism and the
existing total-tensor functor.
Public imports are unchanged. The extra private proof context is recorded in
`coord/changes/A2-adic-coefficient-private-proof-context.md`. Final compilation and
delivery validation are pending.

## Proved and sorry left

Closed the five holes present in the current shared source:

- `AlgebraicGeometry.Scheme.completedReductionTransition_exists`.
- `AlgebraicGeometry.Scheme.reductionBalance_naturality`.
- `AlgebraicGeometry.Scheme.reductionBalance_cocycle`.
- `AlgebraicGeometry.Scheme.completedReductionDerivedNormalization_exists`.
- `AlgebraicGeometry.Scheme.completedReductionEvaluation_exists`.

No holes added or split off; zero `sorry` left in the delivered module. The existing stated
dependencies `completedAdicBalance_exists` and
`derivedChangeOfRingsIndependentCoefficients` retain their holes. This delivery proves
the assigned module from the existing declarations.

## No longer needed

Removed six redundant direct proof imports. Each module is already available through
an unchanged public import:

- `Mathlib.CategoryTheory.Sites.PreservesSheafification`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Mathlib.Algebra.Homology.DerivedCategory.Fractions`.
- `Mathlib.CategoryTheory.Localization.CalculusOfFractions`.
- `Mathlib.CategoryTheory.Localization.Construction`.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`.

The first two were present in the shared source; the last four were exploratory additions.
Their declarations remain used through the existing imports. No dependency node or
module is withdrawn from the targets' closure. The proof follows the node's tensor
balancing, K-flat computation and localization route. Exploratory direct imports of
tensor cancellation and total-complex functoriality are also unnecessary: the existing
K-flat scalar-extension theorem encapsulates those arguments.

## Where the brief, the DAG or earlier work was wrong

The retained K-flat transport used the tensor-presentation isomorphism in the wrong
direction; the proof now maps its inverse through the total-tensor functor. A private
naturality lemma also replaces the large equality transport in the chain-isomorphism
construction. The existing `changeOfRings_isKFlat_of_flat_terms` declaration assumes flat terms,
while normalization
is characterized on every K-flat representative. Resolving such a representative once
more with flat terms and using naturality bridges these interfaces without strengthening
the existing scalar-extension theorem.
The node proof now records the flat-term resolution refinement.
The existing node `lem-pur-kflat-change-of-rings` is used as a tool: the source
normalization paragraph explicitly calls for scalar-extension K-flatness, and the
existing library theorem supplies it on the flat-term resolutions provided by
`lem-pc-kflat-resolution`. No unit statement or required unit step is bypassed.
No mathematical statement or target is changed. The current blueprint moved this
coefficient node to the pro-etale coefficient chapter; the existing DAG id and its
completed-coefficient convention are preserved.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
