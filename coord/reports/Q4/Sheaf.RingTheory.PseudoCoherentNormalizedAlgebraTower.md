## What changed

Proved `DerivedCategory.pseudoCoherent_normalizedAlgebraTower` with its signature and all
public imports exactly preserved. The proof specializes the existing inverse-ring
reconstruction theorem instead of repeating its finite-free model construction. It proves
the adic compatible-tuple limit property and square-zero kernels, normalizes the derived
restriction-composition comparison, converts the transition Hom bijections into invertible
adjuncts, and proves the all-level projection equations and derived completeness directly
from the specified Roos triangle.

Added `Sheaf.RingTheory.DerivedModuleScalarAdjunction`, with the proved theorem
`ModuleCat.derivedRestrictScalars_isRightAdjoint`. Its private helpers construct free flat
epimorphisms and apply the proved source K-flat derived adjunction. Explicit universe lifts
handle the original theorem's larger module universe. No arbitrary object is chosen from
an unproved existence statement.

Updated the item's node proof, proof dependencies and proof origin to this route, and
removed its obsolete direct tool approvals. No existing definition or statement changed;
no other existing module was adapted, and no change record is needed.

Both modules compiled together through `lcompile.py --all`. Axiom inspection of the new
scalar-adjunction theorem reports exactly `propext`, `Classical.choice`, `Quot.sound`.
The tower theorem additionally reports `sorryAx` from its existing staged dependencies;
its own proof contains no hole. The final delivery check rechecks the cleaned files.

## Proved and sorry left

Closed the sole original hole:
`DerivedCategory.pseudoCoherent_normalizedAlgebraTower`
(node `lem-weil-pbc-pseudocoherent-normalized-algebra-tower`).

Also fully proved `ModuleCat.derivedRestrictScalars_isRightAdjoint`
(node `lem-weil-pbc-derived-module-scalar-adjunction`).

Original item: 1 hole before, 0 after. New holes: 0. Split off: 0.
No `sorry` remains in either delivered module, including private helpers. The proof uses
the existing declarations
`DerivedCategory.isPseudoCoherent_inverse_ring_reconstruction` and
`DerivedCategory.isPseudoCoherent_iff_boundedAbove_finite_homology`, whose existing staged
proof obligations are not changed by this delivery.

## No longer needed

Removed these direct proof imports:

- `Sheaf.Algebra.Category.ModuleCat.RingScalarExtension`
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatTelescopeClosure`
- `Sheaf.Algebra.Homology.SurjectiveModuleComplexTowerLimit`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitMorphism`
- `Sheaf.RingTheory.NilpotentMarkedFreeComplexLift`
- `Sheaf.RingTheory.PseudoCoherentNilpotentInvariance`

The finite-free lifting, nilpotent invariance and strict-complex limit work belongs to the
existing inverse-ring reconstruction theorem. It is still needed there, rather than being
duplicated here. Our proof constructs the scalar adjunction for ordinary module categories
from the proved source library, so it needs neither the singleton-site detour nor the
pre-derived ind/pro-system comparison. Projection compatibility and transport of the Roos
triangle are proved directly, without the generic derived-limit-morphism theorem.

Removed direct proof dependencies:
`def-pc-ring-pseudo-coherent-complex`, `def-pod-ring-scalar-extension`,
`lem-pc-kflat-closure`, `lem-pc-pre-derived-adjoint-functors-general`,
`lem-pur-derived-change-of-rings`, `lem-weil-derived-limit-levelwise-iso`,
`lem-weil-derived-limit-morphism`, `lem-weil-pbc-exact-functor-derived-functor`,
`lem-weil-pbc-nilpotent-marked-free-complex-lift`,
`lem-weil-pbc-pseudo-coherent-nilpotent-invariance`, and
`lem-weil-pbc-surjective-module-complex-tower-limit`.
These entries may remain reachable through other statements or reconstruction itself;
no globally pruned module is claimed. The six former top-level `tool_uses` entries were
withdrawn because this proof no longer directly invokes them.

## Where the brief, the DAG or earlier work was wrong

The detailed reconstruction plan is mathematically valid but duplicates the existing
`isPseudoCoherent_inverse_ring_reconstruction` declaration. Stacks' own adic statement
also follows from the general reconstruction statement. This is a shorter route below
the unit level and preserves the proper-base-change unit's prescribed local-effectivity
step. The original normalization formulation supplies bijections, rather than chosen
adjunctions; the new fully proved module bridges that interface without adding a
hypothesis or using an unproved arbitrary witness.

The limiting-ideal edge cases cause no exception: the compatible-tuple and nilpotence
proofs work for J = 0 and for the zero ring; adic completeness supplies separatedness
where uniqueness is required. The scalar-adjunction proof assumes neither a nonzero ring
nor flatness of the ring map. The Roos transport proves the last clause for every supplied
product instance, rather than assuming all products exist.

## New nodes

`lem-weil-pbc-derived-module-scalar-adjunction` is a fully proved ordinary-module scalar
adjunction theorem, not a remaining split obligation. Its single public declaration is
in `lean/Sheaf/RingTheory/DerivedModuleScalarAdjunction.lean`. The node includes the full
argument, explicit universe transport, the source, and three actual Mathlib searches.
The only pending mathematical dependencies newly used by the item are already stated
in the existing inverse-ring reconstruction and Noetherian cohomology-criterion modules.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
