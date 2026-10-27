## What changed

Completed `WeilConjectures.PurityFiniteSetting.finite_setting_comparison_hypotheses`
without changing its signature. A proved private geometric helper gives the Noetherian,
compact and quasi-separated conclusions, Nagata existence, and the dimension bound for
every compactification. It is applied twice: to the original morphism and to every
specified Cartesian base change. A proved private coefficient helper shows that ell^n
vanishes in the actual quotient, using maximal-ideal membership and ideal powers.
The main proof combines these with the existing finiteness and stalk-unit theorems.

Updated the node proof and dependencies to the declarations actually used. All changes
are in this item and its node; no source-library definitions or statements change.
The public import changes are recorded in
`coord/changes/U8-purity-finite-comparison-imports.md`; the downstream check found no
consumer requiring adaptation.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.PurityFiniteSetting.finite_setting_comparison_hypotheses`
(node `lem-pur-finite-setting-comparison-hypotheses`).
The two private helpers `finite_type_geometry` and `coefficient_power_zero` are fully proved.
Holes added: 0. Holes left: 0. Split off: 0.

The checks include ramified coefficient extensions (only ell in (varpi) is used),
positive level one, empty schemes, compactifications with additional components,
and nonseparated structure morphisms to the field. The conclusion for base changes
uses only the specified pullback isomorphism and its second projection equation.

## No longer needed

Removed the unused public smoothness import and replaced the public refinement-category
import by `WeilConjectures.Compactification.Defs`, which supplies the compactification
type actually used in the signature. Made `CoefficientExtensionFinite` a private proof
import. There are no current direct Lean importers of this item, so these public-import
changes require no consumer adaptations.

Removed private imports `WeilConjectures.Mathlib.Topology.KrullDimension`,
`Mathlib.Topology.Algebra.Valued.LocallyCompact`, and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.

The proof does not need `def-kun-dimension` or a conversion from scheme dimension:
`AlgebraicGeometry.exists_topologicalKrullDim_le` already gives the exact bound.
It does not need `lem-weil-pbc-qcqs-morphism-permanence` to prove that the open part
of a compactification is quasi-compact: `Compactification.quasiCompact_openImmersion`
gives this directly from quasi-compactness of f.
It does not apply `lem-weil-valued-dvr-finite-quotients` separately:
`Padic.finite_coefficientExtensionRing`, recorded on
`def-weil-l-adic-coefficient-extension`, already gives finiteness of this exact quotient.
These dependency removals are local to this proof, not withdrawals of their modules;
other users and the coefficient finiteness theorem retain their own dependencies.
No module or declaration was withdrawn, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The DAG plan included unnecessary dimension
translation and re-established finite quotient facts for which the exact interfaces
already exist. The implemented proof uses those interfaces directly. Unit invertibility
is checked using the existing coefficientPrime_isUnit_stalk and the ringed-space
criterion, including the empty scheme.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
