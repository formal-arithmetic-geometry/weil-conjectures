## What changed

Proved `WeilConjectures.sfRationalBoundedConeTorsion` in
`Sheaf.Paper.SfRationalBoundedConeTorsion`, preserving its entire statement.
The proof realizes the planned ambient successive-truncation induction. Four proved
private helpers transport scalar-map vanishing through cohomological monomorphisms
and epimorphisms, detect zero maps on single objects, and identify the truncation
inclusion on cohomology. The final tensor-balancing calculation uses the actual
raw localization ring, without choosing a coefficient-field identification.

Updated `lem-sf-rational-bounded-cone-torsion` to describe the Lean argument and its
actual proof dependencies. No new public declaration, statement change, definition
change, or consumer adaptation is required. The existing truncation-triangle tool
approval is retained. The unit's bounded-perfect-complex route is unchanged.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.sfRationalBoundedConeTorsion`
(node `lem-sf-rational-bounded-cone-torsion`).
Added zero holes, split off zero statements, and left zero holes in the delivered
Lean module. All four private helpers are proved. The proof uses the already
recorded ambient scalar-linearity interface and the declared truncation triangle;
existing holes in imported dependencies are not altered by this delivery.

Edge cases were checked in the argument: N=0 gives r=1 and the zero-identity
criterion; a=b gives one nonzero truncation layer followed by the permitted extra
factor; negative a and b are handled by integer indexing and nonnegativity of
b-a+1; the zero object and empty scheme require no additional hypothesis.

## No longer needed

Removed these explicit imports:

- `Mathlib.Algebra.Homology.DerivedCategory.Linear`
- `Mathlib.Algebra.Homology.Embedding.CochainComplex`
- `Sheaf.CategoryTheory.ScalarLocalization`
- `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`
- `Mathlib.LinearAlgebra.TensorProduct.Basic`
- `Mathlib.RingTheory.Localization.Away.Basic`
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`

The existing public imports are preserved, including the protected unit-route
module `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`. The removed proof-only
imports are redundant through the remaining public dependencies. This does not
claim these transitive modules are globally unnecessary. No dependent module is
withdrawn.

Removed direct proof dependencies `def-weil-completed-integral-coefficients` and
`lem-weil-linear-abelian-derived-category`: the proof obtains the specified ambient
linear structure from `lem-weil-integral-constructible-linear` and uses only its
bilinearity. It needs no separate comparison with a termwise derived scalar action,
no scalar linearity of shifts, and no isomorphism of the coefficient localization
with E. The completed-coefficient definition remains a statement dependency.
The single-object step instead uses Mathlib's fully faithful single functor
(recorded by `lem-weil-pbc-derived-single-fully-faithful`) and its natural homology
isomorphism. All other original proof dependencies remain.

## Where the brief, the DAG or earlier work was wrong

No false statement or incorrect bound was found. The DAG's step 3 implicitly
identifies the chosen ambient constant-section action with the action induced from
a linear category of complexes. That identification is unnecessary: bilinearity
makes scalar identities natural, their cohomology maps cancel through the
truncation inclusion and the epimorphism onto the single layer, and full faithfulness
of single objects detects the zero map. This proves the step for precisely the
scalar action appearing in the unchanged hypothesis.

The initial compiler calls sometimes returned no answer from the remote server;
subsequent calls returned ordinary Lean diagnostics. Compilation and delivery
validation are performed by the required launcher tools.

The first dry run rejected public-import pruning; all original public imports
were restored, including the protected unit-route import. Only redundant
proof-only imports are removed in the final delivery.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
