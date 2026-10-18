## What changed

Proved `AlgebraicGeometry.perfect_degreeZero_fibre_criterion` in
`Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion`, preserving its complete signature
and public imports. The proof uses the existing finite-free residue model, whose negative
terms vanish and whose degree-zero term has rank one. The existing affine chain-map
representative and rank-one residue component criterion make that component invertible
on every stalk. Exact stalk/homology comparisons prove the global cohomology assertion.
A kernel of the projection onto degree zero gives an explicit split complex; its positive
tail is a bounded finite-free retract, hence perfect and K-flat with the required tensor
vanishing. All remaining new local helpers are private and contain no holes. No existing definitions or
consumers changed. Private caches of the standard abelian and colimit instances avoid
repeated expensive sheafification-instance synthesis. Their instance scope ends before the
public signature; the main proof installs the caches only in its body.

Repair of returned head `9845b6bdc`: removed the duplicate private theorem
`AlgebraicGeometry.strictlyPerfect_single_restricted_unit`. Both chain-representative
calls now use the existing theorem in
`Sheaf.AlgebraicGeometry.ConnectiveRankOneModelStalk`, accessed by `import all` because
the existing helper is private. That module is unchanged, and the import-cycle check
passes. The retained sandbox proof was compared against the current shared source;
the item still has its original single hole there.

The node's proof, dependencies and proof origin now describe this direct route and
record the existing helper dependency. Obsolete
`tool_uses` approvals were withdrawn, without adding or reordering approvals. The unit's
statement and steps are preserved; this changes only the argument below the degree-zero
criterion, not the theorem-of-the-cube route.

Searches used the launcher's LeanFinder (perfect complex, negative residue vanishing and
invertible degree-zero structure-sheaf map: only general derived-category hits), Loogle
(`IsIso, HomologicalComplex.homologyMap`: unknown identifier/no match), and grep
(`perfect.*fibre|degreeZero.*fibre|split_connective`: no match). Repository searches found
the existing rank-one component and localized homology comparisons used here.

Validation: the complete axiom probe compiles cleanly, and `deliver3.py --no-push`
passes. The review class is CODEX because the node route changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.perfect_degreeZero_fibre_criterion`
(node `lem-sc-perfect-degree-zero-fibre-criterion`).

Item holes: 1 closed of 1; 0 remaining. New holes: 0. Split-offs: 0.
Every private helper is proved. This is a proof from existing library declarations,
not a claim that all transitive dependencies of those declarations are already axiom-free.

## No longer needed

Removed the duplicate local `strictlyPerfect_single_restricted_unit` proof; its existing
library declaration supplies both uses.

Removed these proof imports and corresponding planned dependencies:

- `Sheaf.AlgebraicGeometry.PerfectCutComplexDegreeZero`
  (`lem-sc-perfect-cut-complex-degree-zero`): split the rank-one model directly instead.
- `Sheaf.AlgebraicGeometry.PerfectSummand` (`lem-pc-perfect-summand`): exhibit perfection
  of the tail by restricting its termwise finite-free retraction.
- `Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective`
  (`lem-pc-perfect-affine-bounded-projective`): the existing minimal finite-free model
  already supplies the required finite-support data.
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeResidueIso`
  (`lem-sc-finite-locally-free-residue-isomorphism`): prove invertibility by the existing
  rank-one stalk component criterion and exact homology comparisons.

The route also does not need
`lem-weil-pbc-finitely-presented-flat-module-projective`
(`Module.Flat.projective_of_finitePresentation`): no separate finite-presentation or
flatness argument for H^0(K) is used. The top-level approvals for perfect summands,
finitely-presented flat modules, affine bounded-projective models, and Tor-amplitude
quasi-coherent testing were removed. The public import `TorAmplitudeQCohTest` is retained
for the unchanged statement interface, but its testing theorem is not used in the proof.
No global Tor-amplitude descent is required. `TorAmplitudeOpenLocal` is used only for
its already-proved open-pullback/restriction comparison, not its amplitude theorem.

An exploratory import of
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` was also removed;
the split tail is handled in the abelian category of all module sheaves.
These are removals from this item's proof route; other targets may still need the nodes.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the private structure-sheaf single-complex helper
already present in `ConnectiveRankOneModelStalk`. This repair imports and uses it.

No statement correction was needed. The earlier four-step route is longer than necessary
once the rank-one component and affine representative declarations are available. In
particular, one can split the minimal finite-free model using the given unit arrow,
without first constructing a separate finite-locally-free H^0(K) summand.

The local splitting is compatible with the zero tail and with higher terms of arbitrary
finite ranks. For an empty scheme both pointwise conclusions are vacuous and the stalk
criterion still proves the first assertion. No nonempty-open hypothesis was added.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
