## What changed

Proved `WeilConjectures.integralSections_perfect_reduction` in
`Sheaf.Paper.IntegralSectionsPerfectReduction`, preserving every public statement,
definition body, public import and existing attribute. Added six proved private
helpers for bounded finite PID cohomology, integral perfectness, transport of finite
point models between localization universes, and invertibility of the normalized
section adjunct, using generic adjunction and naturality lemmas.

The proof uses the existing finite direct-image and dense-refinement compact-support
bounds, then the existing point Tor-amplitude realization. It identifies the actual
specified coefficient maps using `pointReductionUnitNormalization`, adjunction units,
and naturality, and applies ordinary/integral compact-support projection comparison
theorems to the precise chosen Roos realizations. Integral perfectness follows directly
from finite PID resolutions of the bounded cohomology and perfect-cohomology assembly.
The finite models retain the exact interval `[a,b+2d]` at every positive exponent.

Private proof imports added: `PointReductionUnitNormalization`,
`PointTorAmplitudeRealization`, `FiniteCompactSupportUniformTor`,
`PerfectCohomologyAssembly`, and `ScalarPerfectCohomologyAndPidModels` under their
existing Sheaf namespaces. Updated the item's DAG proof and dependencies to match.
No new module or declaration API is introduced. The original permissive backward
unification options are tightened to respect transparency; large scalar-reduction
witness definitions are locally irreducible during proof elaboration. Explicit section
objects and direct references to geometric hypotheses avoid expensive instance search
through bundled return types.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.integralSections_perfect_reduction`
(node `lem-sf-integral-sections-perfect-reduction`). Added 0 holes; split off 0.
There are no remaining `sorry` declarations in the delivered module.
This is a complete assembly from the existing dependency declarations; some dependencies
retain their own named proof obligations.

Private proved helpers: `sfSectionsPerfectOfFiniteCohomology`,
`sfSectionsIntegralPerfect`, `sfSectionsFiniteModel`, `sfSectionsAdjointIsIso`,
`sfSectionsAdjointIsIsoNat`,
`sfSectionsReductionIsIso`.

## No longer needed

Removed private imports `Sheaf.Paper.PointSectionsDerivedReduction`,
`Sheaf.Paper.PointSectionsFiniteness`,
`Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion`, and
`Sheaf.RingTheory.PseudoCoherentMaximalFibrePerfect`.

The revised proof no longer directly uses nodes
`lem-pod-point-sections-derived-reduction`, `lem-weil-point-sections-finiteness`,
`lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion`, or
`lem-weil-pbc-pseudocoherent-maximal-fibre-perfect`; their four obsolete top-level
`tool_uses` approvals are removed in the node copy. The normalized unit theorem is
stronger than existence of an unspecified comparison, finiteness is already in the
section return types, and the PID argument avoids both general pseudo-coherence tools.
The normalized unit theorem still imports point-derived reduction, and the section
constructors still depend on finiteness: no global withdrawal or claim that those two
modules leave the entire target closure is made. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The original DAG's final pseudo-coherence route
is longer than the existing PID-model and perfect-cohomology assembly route, which
also agrees directly with the current blueprint's DVR global-dimension-one argument.
The recorded point realization returns models in a smaller localization universe than
the comparison maps. An explicit localization transport is essential; the complexes
and their coefficient rings are unchanged. Likewise, existence of a natural point
reduction isomorphism alone does not identify the specified projection-adjunct maps;
the existing unit-normalization theorem supplies precisely the required identity.

The generic tools newly used in the route are
`lem-trf-point-reduction-unit-normalization`,
`lem-coef-finite-compact-support-uniform-tor`,
`lem-weil-pbc-scalar-perfect-cohomology-and-pid-models`, and
`lem-sf-perfect-cohomology-assembly`. They implement the same point-perfectness steps;
no blueprint unit statement or step is bypassed. The item's unit record has no
nonempty realized statement/step list.

Edge cases checked in the argument: empty X, zero K and zero cohomology modules,
d=0, exponent one, and a=b. The input Tor predicate already supplies a<=b.
No torsion-freeness assumption is made on cohomology modules.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
