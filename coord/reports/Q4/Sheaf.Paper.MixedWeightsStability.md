## What changed

Proved `FrobeniusModule.mixedOfWeightsAtMost_stability` in
`Sheaf.Paper.MixedWeightsStability` with its exact original signature.
A proved private helper `FrobeniusModule.mixed_eigenvalue_bound` inducts on the
finite mixed filtration: an eigenvector either lies in the preceding term or
has a nonzero eigenvector class in the next pure graded quotient. Monotonicity
of the weight bound then bounds every ambient eigenvalue. Injective maps
preserve nonzero eigenvectors; the existing universe-polymorphic range theorem
transfers eigenvalues along surjections. The existing punctual-bound criterion
converts these bounds back to mixed filtrations. Extensions use the original
stated extension theorem, and the split inclusion is injective by its left inverse.

Added private proof imports of `Sheaf.LinearAlgebra.FrobeniusPunctualBoundMixed`
and `WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Exact`; retained
`Sheaf.LinearAlgebra.FrobeniusModuleExtensionBounds`. Public imports and all
existing signatures are unchanged. Updated the node proof and dependencies to
match this route. The unit has no separately realized proof steps to bypass.

Validation: the full candidate compiled through `lcompile.py` in 4.2 seconds.
The final pruned module and delivery are checked again by the delivery tool.
The induction covers an empty filtration and zero module; quotient nonvanishing
uses exactly nonmembership in the preceding term, so repeated filtration terms
and nonsemisimple Frobenius cause no additional assumption.

## Proved and sorry left

Closed 1 of 1 original holes:
`FrobeniusModule.mixedOfWeightsAtMost_stability`
(node `lem-a1-mixed-direct-summand`).

Added holes: 0. Split off: 0. No `sorry` remains in any delivered Lean file.
The private helper `FrobeniusModule.mixed_eigenvalue_bound` is fully proved.
Existing imported theorems
`FrobeniusModule.isMixedOfWeightsAtMost_of_forall_hasEigenvalue`
(node `lem-a1-punctual-bound-module-mixed`) and
`FrobeniusModule.IsMixedOfWeightsAtMost.of_shortExact`
(node `lem-a1-extension-bounds`) remain prerequisites with their existing holes;
this delivery adds no holes to them and does not claim to close them.

## No longer needed

Removed private import `Sheaf.LinearAlgebra.FrobeniusModuleMixedSubquotient`:
node `lem-a1-subquotient-extension-bounds` and its canonical restricted-quotient
presentation are unnecessary for this theorem. The direct eigenvector argument
avoids transporting a mixed filtration through identifications with that
particular quotient module, and works with independently sized source and target
carrier universes. Its characteristic-polynomial route through
`p-linear-filtration` is also unnecessary here. These nodes may still be needed
by other parents; no global unreachability is asserted.

Removed private import `Sheaf.Paper.AdicPunctualWeights`: the new proof concerns
Frobenius modules only and uses no adic sheaf weight declaration. The sheaf
assertions already supplied by the existing public import
`WeilConjectures.DeligneLaumon.Reduction.Weights` remain available.
No public import is removed. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned subquotient declaration is phrased for a canonical quotient of a
stable submodule rather than the arbitrary equivariant maps and independent
carrier universes used here. It would require additional transport glue.
The eigenvector induction plus the existing filtered criterion gives a shorter
route. The DAG now records that actual route. The recorded extension declaration
fits the third conjunct exactly. No statement or definition was changed, and
no new node or forced consumer adaptation is needed.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
