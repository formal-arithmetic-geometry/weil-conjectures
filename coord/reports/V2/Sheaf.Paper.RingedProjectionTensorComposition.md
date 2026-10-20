## What changed

Proved `SheafOfModules.ProjectionCoherence.ringedProjectionTensorComposition`
from structural tensor coherence and explicit adjunction calculations. The proof
establishes the three naturality equations, identity projection, tensor
associativity, composite projection, identity/composition normalization and the
section specialization, for arbitrary unbounded objects. It never inverts a
projection map.

Moved the original definitions unchanged into
`Sheaf.Paper.RingedProjectionCoherenceData`, publicly reexported by the item.
This removes the dependency cycle between the common data and the intermediate
proofs. The change record is
`coord/changes/V2-ringed-projection-coherence-data.md`; all declaration users
are recorded there. No existing mathematical definition or theorem signature is
changed.

The proof modules are `RingedProjectionTensorStructure`,
`RingedProjectionTensorAssociativity`, `RingedProjectionCanonicalNormalization`,
`RingedProjectionSectionSpecialization`, and the two further structural modules
`RingedProjectionPullbackComparisons` and `RingedProjectionTensorCompatibility`,
all in `Sheaf.Paper`. Together with the common data and item there are eight
modules.

The additional completed subargument constructs the normalized identity,
composition and section pullback comparisons independently of tensor coherence.
It descends natural isomorphisms through the full, essentially surjective
flat-complex homotopy quotient and its localization, using the given ordinary
module comparisons and invertible flat K-flat derived comparison maps.
`ringedProjectionTensorStructure` now combines this proved construction with
compatibility of tensor constraints and normalized comparisons.

## Proved and sorry left

The original hole closed is
`SheafOfModules.ProjectionCoherence.ringedProjectionTensorComposition` (1 of 1).
One hole is added:
`SheafOfModules.ProjectionCoherence.ringedProjectionTensorCompatibility`, node
`lem-sfb-ringed-projection-tensor-compatibility`. Thus this is a decomposition,
with net zero holes closed, not a proof of all structural prerequisites.

The new hole is strictly the tensor subargument: construction of the total-tensor
constraints and tensor compatibility of already normalized comparisons. It has
no projection map, no adjunction-mate equation and no existence obligation for
identity/composition/section pullback comparisons. Its source and complete proof
in words are in its docstring and node. The original theorem is proved by real
adjunction, naturality and symmetry calculations from this structural subargument.
The ordinary symmetry involution is proved generically before specializing to
ringed modules; this avoids repeatedly elaborating the module-sheaf tensor
construction in its signed summand calculation.

All other delivered modules have zero holes. The proved public declarations in
`SheafOfModules.ProjectionCoherence` are:
`ringedProjectionPullbackComparisons`, `ringedProjectionTensorStructure`,
`tensorConstraints_involutive`, `ringedProjectionTensorAssociativity`,
`compositeProjection_eq`, `ringedProjectionCanonicalNormalization`,
`sectionProjectionComparison`, `ringedProjectionSectionSpecialization`, and
`ringedProjectionTensorComposition`.

The unchanged data bodies and the item theorem signature were checked against
the current source. The comparisons do not impose boundedness, flatness of the
structural ring map, or a choice of canonical derived lift. Identity edges, zero
objects, empty sites, zero coefficient rings and Koszul signs in odd degrees do
not require exceptional hypotheses.

Scratch experiments are retained under `scratchpad/` and are excluded from the
Lean delivery. They include successful naturality and tensor-model transport
calculations; incomplete diagnostic declarations there are not library lemmas.

## No longer needed

Removed the unused proof import
`WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat` from the item:
the proof works directly with the uncurried tensor bifunctors. The six original
public imports remain exposed through CoherenceData.

The route does not use
`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
(`lem-sfb-ringed-derived-monoidal-comparisons`), which chooses a system of derived
lifts and tensor models. Flat K-flat localization directly constructs comparisons
for the supplied presentations, so no transport of that chosen system is needed.
It also does not use
`Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`
(`lem-sf-ringed-derived-closed-symmetric-monoidal`): descending the specified total
associator and signed symmetry needs no closed tensor-Hom structure or unitors.
These dependencies and their proof imports have been removed from this route.
No existing module is claimed globally unreachable; other parents may use them.

The structural module no longer imports
`Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`,
`Sheaf.Algebra.Homology.KFlatTotalTensorModel`,
`Sheaf.Paper.KFlatRingedToposPullback`,
`Sheaf.Paper.DerivedPullbackRepresentativeComputation`,
`Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`, or the two modules just named:
the relevant uses are now in the two structural subarguments, whose dependency
records describe them. The sole direct old proof dependency retained there is
`Sheaf.Algebra.Homology.KFlatResolution`, for symmetry involutivity on resolutions.
The unit's realized records have no statement/proof-step attachments bypassed by
this change.

## Where the brief, the DAG or earlier work was wrong

The older report incorrectly said that the chosen-lift and closed-monoidal
structural dependencies were absent. They are present; their declarations were
read. Their conclusions are for chosen presentations and include extra closed
structure. The direct localization argument avoids that extra transport.

The retained draft had several genuine Lean errors in representative symmetry,
identity transposition, parenthesization of composite counits and section
naturality. Explicit typed comparison maps and focused rewriting repair them
without changing the statement. A composite natural-transformation definition
also caused expensive repeated kernel unfolding. The pullback comparison is now
constructed with an explicit component and proved naturality, retaining its
mathematical value and reducing its compile time below the file limit.

Earlier required dry runs corrected metadata: LeanFinder and Loogle are one
search kind, the common data module needs a node, and all declaration-mention
users belong in the change record. Real LeanSearch queries, the definition node
and the consumer rows address these diagnostics.

New structural records use the original module's `genSizeOf false` and
`genInjectivity false` settings, avoiding generation of large constructor lemmas.
These options do not change the declared record fields or theorem signatures.

The provider interrupted several continuations. No push was started in those
attempts. The launcher reference clock reset: the earlier dry-run final attempt reported
48 minutes, while the next continuation's `dry-run-after-gate.log` reported
0 minutes for the retained packet. This is recorded without modifying launcher
files or budget metadata. Work continued by proving all three normalized
pullback comparisons and reducing the tensor structure obligation. Earlier
transport probes eventually completed; those historical pending-probe notes
are superseded by the current compile results.

Current validation: `lcompile.py --all` compiled all eight modules without errors
or warnings (`all-eight-generation.log`), each within 60 seconds. The repaired
required dry run returned OK at `9b5872b3f0`, under CODEX review
(`dry-run-records-repaired.log`). The exact data node signature and five newly
visible consumer rows are repaired. The tool reported that three axiom probes
(CanonicalNormalization, CoherenceData and PullbackComparisons) timed out and
will be rerun by the merge; no forbidden axiom was reported. This is a limit of
that verification, not a claim that those probes completed.

## New nodes

`def-sfb-ringed-projection-coherence-data` records the common module of unchanged
explicit definitions, without adding a theorem hole. Change record:
`coord/changes/V2-ringed-projection-coherence-data.md`.

`lem-sfb-ringed-projection-pullback-comparisons` is proved: existence and exact
flat K-flat normalization of the identity, composition and section comparisons.

`lem-sfb-ringed-projection-tensor-compatibility` is the sole remaining hole:
the total tensor constraints and their compatibility with arbitrary supplied
representative presentations and already normalized comparisons.

`lem-sfb-ringed-projection-tensor-structure` is proved by combining these two
independent conclusions; it also records the proved involutivity theorem.

`lem-sfb-ringed-projection-tensor-associativity` is proved by transposing both
projection paths and applying tensor naturality and the two counit equations.

`lem-sfb-ringed-projection-canonical-normalization` is proved by conjugating the
identity and composite adjunctions, including the right-ordered section formula.

`lem-sfb-ringed-projection-section-specialization` is proved from that formula,
symmetry naturality and involutivity, giving the required left-ordered section
specialization.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
