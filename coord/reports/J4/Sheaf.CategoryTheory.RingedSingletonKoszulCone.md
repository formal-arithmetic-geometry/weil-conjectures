## What changed

Proved `CategoryTheory.ringedSingletonKoszulCone` without changing its statement
or `ringedSingletonKoszulPower`. Added proof-only imports of the new, fully proved
`Sheaf.CategoryTheory.RingedSingletonCoefficientCone` and the existing
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`.

The coefficient theorem constructs normalized isomorphisms from the singleton
dual tower to scalar cones. Its proof specializes negative Koszul duality,
removes the right tensor unit, and uses the explicit two-term cone isomorphism.
The empty-subset basis fixes the unit normalization. Successor compatibility of
second projections follows from unit naturality: the unit is invertible in degree
zero, and all other coefficient projections have zero target.

The item tensors these coefficient isomorphisms by the arbitrary complex, applies
the existing signed tensor-cone comparison, and computes the second projection on
every total-tensor summand. The three required identities follow from these
formulas. No boundedness, flatness or scalar-invertibility assumption is added.

The single-file proof compiled mathematically but exceeded 60 seconds. Profiling
and local irreducibility of completed private constructions, plus normalization of
public aliases, reduced its time from 101 to 68 seconds. Only then was the fully
proved coefficient argument moved into its own module. No imported definition or
public interface was changed for performance. The original private `doubleConeHom` and `doubleConeIso` helpers were moved to
the coefficient module. The item node and the new coefficient node record the
actual argument. Both files passed the server compile with profiling enabled:
50.5 seconds for the coefficient module and 50.3 seconds for the item. The only
warnings were the profiling options, now removed. The delivery command performs
the final clean compilations and axiom/preflight checks.

## Proved and sorry left

Closed the one original hole, `CategoryTheory.ringedSingletonKoszulCone`
(node `lem-sfb-ringed-singleton-koszul-cone`). The new
`CategoryTheory.ringedSingletonCoefficientCone`
(node `lem-sfb-ringed-singleton-coefficient-cone`) is proved in full.
No holes are added or split off. Neither delivered module contains `sorry`.

## No longer needed

The explicit negative-factor transition calculation from
`def-weil-pbc-ringed-negative-koszul-transitions` is unnecessary; its direct
proof-dependency entry is removed. Its module remains a transitive import of
negative Koszul duality, so it is not withdrawn or globally pruned. Negative
duality and the negative-factor/basis definitions are used by the new coefficient
module and remain represented in that node's dependencies.

No original public import is removed. The item uses the explicit chain comparison
underlying `lem-sfb-additive-total-tensor-cone-comparison` instead of importing its
existential derived-category wrapper
`Sheaf.Algebra.Homology.AdditiveTotalTensorConeComparison`. It does not need
`Sheaf.Paper.PrincipalKoszulDualTowerComparison`, localization, quotient
comparisons, flatness, regularity, or a coefficient field. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original statement and mathematical plan are correct. The existing public
`mapBifunctorMappingCone₂Iso.ι_p₂_v` and total-tensor summand APIs suffice for the
arbitrary-complex projection formulas. Successor compatibility needs only unit
naturality and the support of O[0], rather than an explicit negative-transition
matrix calculation. The same categorical proof covers zero complexes, zero or
invertible scalars, the zero ring, and empty sites.

## New nodes

`lem-sfb-ringed-singleton-coefficient-cone` is the fully proved coefficient-only
part of the argument, with no arbitrary tensor factor. It constructs the normalized
coefficient cone isomorphisms and proves successor compatibility of their second
projections. Its module is `Sheaf.CategoryTheory.RingedSingletonCoefficientCone`.
It has no sorry, and its extraction follows the required definition improvements
and timing analysis. No change record is needed: no existing public statement or
definition is changed, and no other existing module is adapted.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
