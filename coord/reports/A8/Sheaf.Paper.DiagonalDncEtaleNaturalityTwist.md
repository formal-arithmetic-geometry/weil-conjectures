## What changed

The assigned theorem `diagonalDncEtaleNaturality_twist` keeps its complete original
signature and public import. Its proof-only import supplies the proved
`diagonalDncEtaleNaturality_localInverse`; cancellation of the source restriction
comparison recovers the original component equation.

The local-inverse theorem is proved by factorization at the actual normal-section
object and pasting two distinct squares. `DiagonalDncEtaleFactors` defines
`twistToNormal` (Tate restriction and inverse beta) and `normalToDualizing`
(inverse delta, alpha, inverse rho, coefficient-unit comparison), and proves their
composition is the existing local inverse. The second factor takes only affine
diagonal geometry, with no normalized beta input.

`DiagonalEtaleSectionComparisons` reuses the fully explicit self-product/Rees/
zero-fibre argument in `GeneralChartComparisons` under an independent namespace.
Its normal map is constructed by the zero-fibre pullback universal property;
`normalGeometry` proves the Cartesian projection and zero-section identities.
`normal` applies the already specified smooth exceptional exchange. Importing the
existing general-chart module would create a cycle through diagonal orientation,
so this module contains only the needed geometric construction and its proofs.
`DiagonalEtaleNormalTransport` composes the two actual normal comparisons through
the diagonal of the common source. It involves no beta or DNC orientation choice.

`DiagonalDncEtaleBeta` states only the Tate/integration square at that normal map;
`DiagonalDncEtaleDualizing` states only the DNC/dualizing square there. The former
has no compact-support normalization input; the latter has neither a twist
transport nor normalized beta input. The proof of the local-inverse theorem
combines them using functoriality and associativity. The unit route through the
diagonal normal bundle, DNC, and normalized vector integration is retained.

Validation: all seven Lean modules compiled without warnings through `lcompile.py`.
The local-inverse proof uses explicit functoriality of both derived pullbacks and
associativity to paste the factor squares. Temporary profiler settings are removed.
The original declaration signature was compared verbatim with the repository copy.
The first preflight of the corrected factorization packet reported only two
metadata signature mismatches: the definition attachments included their bodies.
Those attachments now stop at the declaration signatures. The additional LeanSearch
run is also recorded, alongside Loogle/LeanFinder and source grep.

## Proved and sorry left

The original hole is closed in the unchanged declaration
`WeilConjectures.PurityFiniteSetting.diagonalDncEtaleNaturality_twist`.
The intermediate theorem
`WeilConjectures.PurityFiniteSetting.diagonalDncEtaleNaturality_localInverse`
is also proved, as are `DiagonalEtaleComparison.localInverse_factors`, all normal
map/projection/ideal lemmas, and the Cartesian normal-geometry assertion.

Exactly two new holes remain:

- `WeilConjectures.PurityFiniteSetting.diagonalDncEtaleNaturality_beta`
  (`lem-pur-diagonal-etale-beta-square`): compatibility of normalized vector
  integration with the actual Cartesian normal comparison, without delta/alpha/rho.
- `WeilConjectures.PurityFiniteSetting.diagonalDncEtaleNaturality_dncDualizing`
  (`lem-pur-diagonal-etale-dnc-dualizing-square`): compatibility of inverse DNC,
  alpha, rho, and the unit comparison, without beta or vector integration.

Each is in its own module, has an exact named `by sorry` proof, a source, a complete
proof in words, and a node. Neither restates the whole local-inverse square.
The remaining beta proof may use the already proved
`Etale.ordinaryFiniteTwistTransport_unique` to replace the supplied t by the
canonical transport; this existing dependency is recorded in its node.

This is a decomposition of one original hole into two genuine geometric steps,
not a net reduction of the target-closure hole count. No definition contains sorry.

## No longer needed

No existing module or node is withdrawn. The assigned proof needs no affine-cover
existence argument, since the affine target and both charts are supplied. The
original three geometric proof dependencies are replaced directly by the proved
pasting node; the needed DNC and normalization facts remain dependencies of its
two geometric factors. There is no global pruning claim. Specifically, the affine-cover existence part of
`lem-pur-affine-target-diagonal-dnc` is unused; its canonical geometry and maps are
still the definitions used here. `thm-pur-dnc-invariance` remains needed by the
DNC factor, and the normalization data of
`lem-pur-diagonal-orientation-refinement` remain needed by the integration factor.

The independent geometric module imports only `PurityDncInvariance` publicly,
instead of the larger diagonal counit/orientation package. Its public types need
the existing DNC section objects and canonical fibre comparisons. It omits the orientation-dependent `source`,
`sourceOrdinary`, and `sourceLift` constructions of `GeneralChartComparisons`.
It does not import that module, `GeneralChartDncNaturality`, or the downstream
orientation theorem. Unused public imports of `PuritySectionEtaleRestriction`
and `ChartNormalDifferential` were removed from the new geometric module;
`ChartNormalDifferential` remains a proof-only `import all` because its proved
geometric helper is used. `ConormalAlgebraFlatBaseChange` is also proof-only.
All original public imports remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The first packet of this session merely conjugated the original assertion and
left its equivalent local-inverse square admitted. That was not a genuine
reduction. This packet supersedes it: the local-inverse square now has a complete
pasting proof from two independent factor squares at a geometrically constructed
normal comparison. No definition or existing statement is weakened.

The existing general-chart module contains the needed normal-cone construction,
but its orientation imports make it unusable here without a cycle. The independent
geometric module reuses that argument without importing the unfinished orientation.

## New nodes

`lem-pur-diagonal-dnc-etale-naturality-twist-square-local-inverse` records the now
proved pasting of the beta and DNC/dualizing squares; it has no remaining hole.

`lem-pur-diagonal-etale-local-inverse-factors` records the actual two factors and
their proved equality with the local inverse (`DiagonalDncEtaleFactors`).

`def-pur-diagonal-etale-section-comparisons` records the self-product, coefficientwise
Rees map, actual normal-cone lift, Cartesian/zero-section proofs, and the canonical
exceptional exchange (`DiagonalEtaleSectionComparisons`).

`def-pur-diagonal-etale-normal-transport` records the constructed comparison through
the common source normal cone (`DiagonalEtaleNormalTransport`).

`lem-pur-diagonal-etale-beta-square` records the integration factor and its source
argument (`DiagonalDncEtaleBeta`); this is one of the two remaining holes.

`lem-pur-diagonal-etale-dnc-dualizing-square` records the DNC/dualizing factor and its
source argument (`DiagonalDncEtaleDualizing`); this is the other remaining hole.

Only the assigned existing node and the nodes created in this session are changed;
no existing definition or statement changes, so no shared-interface adaptation or
change record is required.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
