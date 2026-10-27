## What changed

Filled three existing holes in `Sheaf.SixFunctors.IntegralExceptionalMappingSystem`.
`reduction_domain` uses the existing residue-Tor theorem, normalization field and
finite evaluation isomorphisms. Finite constructibility and Tor amplitude are
transported along those isomorphisms, without an additional input hypothesis.

`support_and_counits` applies `purNormalizedReconstruction` to the normalized
outputs of `r.F` and `r.G`, giving invertibility of the actual system counits.
The structure morphisms map the unit prime in the base field to global sections.
The support limit is complete by reconstruction and the legacy-completeness
comparison. Its finite reductions are isomorphic to those of the recorded integral
compact-support functor, through the actual counit, support evaluation and
coefficient comparisons. Transporting constructibility and the common homology
interval proves the remaining assertion. No `IntegralSupport` assumption is added.

`supportCoefficientComparison` applies the injective finite scalar-adjunction
Hom equivalence. Its transposes agree by `SY.counit_projection`, scalar-unit
naturality and `IntegralSupport.projections`.

Only this module and its existing node are changed. Public signatures, definitions,
public imports and targets are preserved. No new declarations or modules.

## Proved and sorry left

Closed three of the original four holes:

- `WeilConjectures.IntegralExceptionalMapping.reduction_domain`.
- `WeilConjectures.IntegralExceptionalMapping.support_and_counits`.
- `WeilConjectures.IntegralExceptionalMapping.supportCoefficientComparison`.

One original hole remains, attached to
`lem-coef-integral-exceptional-mapping-system`:

- `WeilConjectures.IntegralExceptionalMapping.integralExceptionalMappingSystem`.

Added zero holes; split off zero statements. This is a partial delivery of a module
with several holes; the disputed final statement and its original proof docstring
remain intact.

## No longer needed

Removed direct proof imports:

- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`:
  normalization is already `S.reduction_normalized`.
- `Sheaf.Paper.NormalizedDVREffectivity`: reconstruction supplies completeness and
  invertibility of these actual counits directly.
- `Sheaf.Paper.SfIntegralCompactSupportConstructible`: the recorded integral
  compact-support functor already has constructible output. Finite comparison
  transports its bounds to the actual support limit.

Removed their direct node dependencies
`lem-sfb-successive-derived-quotient-normalization`,
`lem-coef-normalized-dvr-effectivity` and
`lem-sf-integral-compact-support-constructible`.
Removed the two corresponding old top-level tool approvals. These results remain
needed by their other consumers, including reconstruction and the recorded
compact-support construction; no global withdrawal or unreachable-module claim
is made.

Added private proof imports of
`Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`,
`Sheaf.Paper.SfDerivedCompleteLegacyComparison` and
`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`.
The node records their actual dependencies, using the specific
`lem-pur-normalized-actual-reconstruction-maps` attachment for
`purNormalizedReconstruction`. All public imports are preserved. Reconstruction and the legacy comparison are
generic tools from the smooth-purity unit: they package precisely the actual
normalization/effectivity and completeness conversion needed here. They do not
bypass any realized step of the assigned unit.

## Where the brief, the DAG or earlier work was wrong

The direct successive-quotient-normalization step duplicates the given calculus's
`reduction_normalized` field. The separate normalized-effectivity argument is
already packaged by the existing reconstruction theorem. The constructibility
argument does not need an extra `IntegralSupport`: actual finite evaluations suffice
to transfer the recorded integral functor's finite constructibility and bounds.

STATEMENT-DISPUTED: the final theorem's intended naturality argument is not
justified by its hypotheses. `CoefficientDerivedSystemCalculus.globalEvaluation`
is an objectwise family of isomorphisms with no naturality field. Its identification
with the natural sections comparison and `fiberHom` is instead
`CoefficientDerivedSystemResolutionCoherence.globalEvaluation_model`, which is
absent from the hypotheses. `Enriched.finiteEvaluation` constrains the comparisons
at pairs involving `r.F` and `r.G`; it does not give naturality along the outer
system counit isomorphisms at the different pairs used by `finitePsi`.
The other fields of the bare calculus do not mention `globalEvaluation`.
Consequently one cannot use their internal-Hom naturality to justify this step.
No unproved naturality assertion or weaker replacement theorem was introduced;
the original declaration is marked for review and remains a named hole.
The earlier review's assertion that omitting Coherence is harmless needs to be
reconciled with this specific missing field. A formal counterexample to the full
geometric statement has not been constructed.

The node's old blueprint source path is absent from the current `latest` snapshot;
its original citation is preserved. The current finite-exceptional proof and
normalized-DVR-effectivity proof were read for the preserved finite-adjunction
route and reconstruction argument. Zero inputs and empty schemes require no extra
case hypotheses; the proofs transport existing predicates and isomorphisms.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
