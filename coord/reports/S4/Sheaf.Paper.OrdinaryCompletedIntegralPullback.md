## What changed

In `Sheaf.Paper.OrdinaryCompletedIntegralPullback`, proved five existing obligations without
changing any public declaration signature, definition body, or public import:

- Constructed the completed direct-image coefficient map by the preserved-limit universal
  property. Proved constant-coefficient naturality directly from the sheafification
  adjunction to assemble its finite-level cone.
- Applied `module_pushforward_isRightAdjoint_of_universes` to the actual completed ring map.
  Proved sectionwise pushforward additive, then used its adjunction to prove pullback additive.
- Proved the strict cone condition by product projections and quotient-tower naturality.
- Proved existence and uniqueness of the specified completion comparison. First proved
  naturality of the actual `(quotients,0)` mapping-cocone lift using the existing Roos-square
  calculation. Packaged the universal ordinary derived counit as a natural transformation,
  then descended by the fully faithful good-complex localization. The preimage equation gives
  exactly the required normalization; faithfulness and cancellation give uniqueness.

The six new private lemmas are fully proved. One private constructed comparison packages
its actual natural transformation together with its normalization proof. Proof imports access existing private
Roos and descent helpers through `import all`; coefficient naturality is proved locally. Local transparency
attributes and explicit product index families prevent expensive unfolding of cone objects.
No heartbeat or server time limit was increased. Updated the two existing owning DAG nodes to
record the implemented supporting proofs and the current three-step geometric plan.

Change record: `coord/changes/S4-ordinary-integral-proof-elaboration.md` documents the
new module attribute commands required by preflight. There are no consumer adaptations.

Repair of the return at 628eee3dd: removed the proof import of
`Sheaf.Paper.IntegralComparisonSequenceSystems`, which the landing source check could not
find. Its only use was a private coefficient-naturality lemma. Two fully proved local
helpers now derive that equality from the sheafification adjunction and unit naturality.
The quarantined sequence-system module and its node are untouched. Rebased the two node
copies on the current shared records, preserving current review metadata, tool approvals,
and the current geometric proof route. This is a proof repair, with no added holes.

The repaired module compiled cleanly through `lcompile.py` in 22.2 seconds.
The delivery tool performs the final axiom scan and preflight.

## Proved and sorry left

Closed five of the original nine holes; added zero holes and split off zero statements.
The closed declarations are:

- `WeilConjectures.ordinaryIntegralDirectRingMap_existsUnique`
- `WeilConjectures.ordinaryIntegralModulePush_isRightAdjoint`
- `WeilConjectures.ordinaryIntegralModulePull_additive`
- `WeilConjectures.ordinaryIntegralCompletionChain_condition`
- `WeilConjectures.ordinaryIntegralCompletionComparison_existsUnique`

The four original holes retained, with their original signatures and proof docstrings, are:

- `WeilConjectures.ordinaryIntegralPull_hasLeftDerived`
- `WeilConjectures.ordinaryIntegralPullComplexCounit_isIso`
- `WeilConjectures.ordinaryIntegralQuotientAugmentation_existsUnique`
- `WeilConjectures.ordinaryCompletedIntegralPullback`

All nine obligations are attached to `lem-tw-ordinary-completed-integral-pullback`.
The construction obligations are also owned by
`def-sf-ordinary-integral-pullback-construction`. This is a partial proof delivery;
the final constructibility/isomorphism theorem is not claimed proved. The proved descent
uses the existing derived functor and augmentation declarations, including their still
unproved construction obligations, as permitted by the stage-3 dependency rule.

## No longer needed

Removed the rejected proof import `Sheaf.Paper.IntegralComparisonSequenceSystems` from
the returned packet. Its node `def-trf-integral-comparison-sequence-systems` is no longer
a dependency of the supporting proof: the sheafification argument proves exactly the
coefficient naturality needed here without sequence-site constructions. This removes a
proof dependency only; the existing module and node remain available to their other users.

Removed these unused proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`
- `Sheaf.Paper.IntegralUniformCoefficient`
- `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`
- `Sheaf.Paper.SfImmersionCompletedPullbackComparison`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `Sheaf.CategoryTheory.SiteInverseImageTensor`
- `Sheaf.Paper.RingedDerivedSliceLocalization`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Paper.KoszulReconstruction`
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`

These are unused-import removals, not withdrawals of mathematical dependencies. The final
geometric proof remains unfinished, so the current geometric route and its tool approvals
are retained in the DAG. No node or module is withdrawn, and no source-library declaration
is removed or altered.

## Where the brief, the DAG or earlier work was wrong

No false statement or mathematical error was found. The module-adjunction construction
requires the existing independent-universe theorem because the coefficient universe is
larger than the site universes. The shortest available coefficient-naturality and good-class
localization proofs were already implemented as private lemmas in other modules. The
returned coefficient helper, however, belonged to a quarantined module; depending on its
compiled artifact did not establish source availability at landing. The repair proves the
small sheafification argument locally and removes that import.

Implicit product indices in `towerTransitionEndomorphism` caused the elaborator to unfold
large homotopy-cofiber constructions. Explicit index families, generic private tower and
descent lemmas, a normalization equation packaged with the constructed comparison, preference for the
recorded `integralTowerHasDerivedCategory` instance, suppression of competing imported
instances, and local irreducibility attributes made the full proof compile under the
existing 60-second limit. The canonical limit remains transparent during its actual
universal-property construction. No definition was split into a separate file.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
