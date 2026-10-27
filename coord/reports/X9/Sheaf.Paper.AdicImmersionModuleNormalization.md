## What changed

Filled `AlgebraicGeometry.Scheme.sfbImmersion_moduleNormalization` in
`Sheaf.Paper.AdicImmersionModuleNormalization`, preserving its statement and every existing
public definition and instance signature. Added proved private helpers for scalar equivalences,
algebraic presentations of sectionwise restriction and scalar transport, composition of
presentations, and comparison of presentations. The existing limit and colimit instances now
use a model equivalence with an explicit transport functor, avoiding conversion through a
large inverse functor. The slice comparison uses identity linear maps on sections instead of
equality of entire functor structures. Completed limits remain locally folded during
elaboration. Added private proof imports of
`ModulePullbackPushforwardAdjunction`, `SiteAlgebraicCompositionUnit`,
`Sites.GeometricInverseImageExact`, `ProEtaleAlgebraicInverseImage`, and
`NativeRingedRestrictionSlices`.

The proof builds the global comparison before restricting to the slice. It uses the existing
proved graph-transport comparison to compare the two algebraic lifts, then uses the tensor
adjunction to replace extension along the invertible completed coefficient map by restriction
along its inverse. The final equivalence is the AsSmall slice module equivalence followed by
scalar transport. Updated the item's proof and proof dependencies to this argument.

Validation: remote single-file compilation passed in 54.5 seconds, below the 60-second
limit. Removed all profiling options and diagnostic commands before delivery. Every existing
signature and public import was checked against the shared source. `deliver3.py` runs the
production compile and preflight.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.sfbImmersion_moduleNormalization`
(node `lem-sfb-adic-immersion-module-normalization`). No holes added or split off.
There are zero `sorry` occurrences in the delivered Lean module. All private helpers are proved.
Existing dependency theorems retain their existing proof status.

## No longer needed

The original proof dependency `lem-pur-site-restriction-module-adjunction-exact`
(`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`) is not used by this argument: slice
transport is sectionwise, so no extension-by-zero adjunction is needed here. Removed this
logical proof dependency from the node. That module can remain needed by other library
consumers; this delivery withdraws no module.

No original Lean import was removed; each supplies definitions or proofs still used by the
unchanged instances or the new proof. The argument needs neither a separate equality of the
two canonical completed-ring comparisons nor a finite-projection normalization theorem for
the final equivalence: the conclusion quantifies existentially over that equivalence.

## Where the brief, the DAG or earlier work was wrong

Existing library declarations supply the generic algebraic comparison machinery needed to
close the module-level obligation. A further decomposition of the normalization statement is
unnecessary. The source completed-ring map and the specified module pullback remain exactly
those in the original statement; the comparison ring isomorphism is obtained by transporting
operation graphs. No statement or definition repair, consumer adaptation, or source-library
edit was needed. The unit route is unchanged.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
