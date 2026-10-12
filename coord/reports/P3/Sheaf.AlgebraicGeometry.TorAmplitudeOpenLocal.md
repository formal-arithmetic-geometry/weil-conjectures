## What changed

Proved `AlgebraicGeometry.torAmplitude_of_open_neighbourhoods` in
`lean/Sheaf/AlgebraicGeometry/TorAmplitudeOpenLocal.lean`, preserving its full signature,
visibility and existing docstring. Added only private, proved helpers for K-flat models,
comparison with derived tensor homology, open pullback versus exact restriction, and
restriction of homology via the proved source-library exact-functor comparison. The K-flat counit is extracted from the defining theorem of
`derivedPullback`, rather than replaced by another chosen functor. Adjoint uniqueness
identifies termwise tensor pullback with restriction, and the actual localization
comparisons carry this calculation to the chosen derived categories.

Added proof-only imports of `Sheaf.Algebra.Homology.KFlatResolution`,
`Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison`,
`Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`, and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`. The existing public import
is unchanged. Updated the item's node proof, proof dependencies and proof origin to
match the Lean argument. No other module changes. The preflight classifies the added file-local commands
as an interface edit; their scope and unchanged downstream behavior are recorded
in `coord/changes/torAmplitudeOpenLocal-proof-commands.md`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.torAmplitude_of_open_neighbourhoods`
(node `lem-pc-tor-amplitude-open-local`). All five private helpers are proved, as is
the private local tensor instance. No `sorry` remains in the item, and no holes or
new modules were added. This closes one hole with zero split-off holes; it is not a
decomposition. Existing dependencies retain their own proof obligations.

The proof handles every test module and every excluded degree separately, retaining
the original fixed interval and localization universe. It constructs the existential
K-flat witness in the reverse comparison. The chosen opens form a cover even when
X is empty, and no quasi-coherence, affine, compactness or boundedness assumption is
introduced. The interval-order hypothesis is retained although the local-to-global
argument does not need it.

## No longer needed

No original imports were removed: the single original public import is needed for
the statement. A separately added import of
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` was removed because the
needed public API already comes through `DerivedTensorOpenRestrictionUniverses`.

The direct proof dependency `pqf-lem-sheaf-zero-stalks`, module
`Sheaf.AlgebraicGeometry.SheafZeroStalks`, is no longer needed by this item.
The proved source-library theorem
`AlgebraicGeometry.Scheme.Modules.isZero_of_iSup_eq_top` supplies the open-cover
criterion directly. This is pruning of this item's route, not a claim that no
other target path uses the stalk lemma.

`lem-pc-open-restriction-kflat-model` and
`lem-pc-open-restriction-total-tensor`, modules
`Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel` and
`Sheaf.AlgebraicGeometry.OpenRestrictionTotalTensor`, are removed from this node's
direct proof dependencies. They remain necessary transitively through
`lem-pc-derived-tensor-open-restriction-universes`; they are not globally pruned.
All other planned dependency nodes remain in the direct proof dependencies.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The DAG's final stalk route can
be shortened using an already proved open-cover vanishing theorem. The detailed
chosen-derived-pullback comparison, omitted from the plan's informal adjoint
uniqueness sentence, is now a complete private Lean proof. The unit record has
no realization containing this item, and no unit statement or step was bypassed.

Searches performed: LeanFinder for local derived-tensor vanishing (eight unrelated
results); Loogle for `SheafOfModules.overFunctor` (restriction functor and
`overFunctorEquiv` found); launcher grep for local vanishing/model expressions
(no match). Repository searches found the proved source-library open-cover
criterion and the pattern for extracting the K-flat counit. Read the signatures
and proofs of the planned K-flat and restriction declarations. The local Stacks
checkout is absent; checked the official [Tag 09U9](https://stacks.math.columbia.edu/tag/09U9)
statement and proof online. No new nodes or unsupported mathematical statements
were introduced.

The complete module compiled cleanly with the launcher (no warnings). An initial
delivery compile timed out under heavy host load. Profiling identified repeated
instance inference and comparison elaboration; the final code uses the already
proved `Functor.mapDerivedCategoryHomologyFunctorIso` instead of a manually
constructed comparison. All development profiler options were removed.


Resumed-attempt verification: read the existing sandbox proof and every comparison
it uses, checked the unchanged theorem signature and the unit realization, and
recompiled successfully through lcompile.py (50.5 seconds, no warnings). Rechecked
Stacks Tag 09U9 online. The first dry run rejected the missing change record for
file-local commands; added the record above without changing the Lean proof.
No forced adaptations or new statements were needed. The second reader's section
is intentionally left for the second reader.

## Second reading by P3

1. Compared the delivered Lean module and node against the repository with `diff`.
   Independently checked the original theorem signature byte for byte with a script.
   Verdict: signature, visibility, docstring and original public import unchanged;
   no existing definition changed. The file-local elaboration commands have the
   declared change record, and all added imports are proof-only.
2. Compiled the delivered module locally with lcompile.py: clean, 15.0 seconds.
   Compiled a scratch copy with `#print axioms` for the target and all five private
   helpers: clean, 11.8 seconds. The tensor comparison helper uses only `propext`,
   `Classical.choice`, and `Quot.sound`; the other helpers and target additionally
   use `sorryAx` from existing upstream obligations. No additional axiom appears.
   Scanned delivered Lean for forbidden declarations and sorry: none. Verdict:
   one local hole closed, zero holes added; this is not yet an axiom-free target
   because existing dependencies are still open. No data definition is introduced;
   K-flat witnesses are eliminated inside theorem proofs, and the derived-pullback
   comparison uses the counit of the already chosen, universally specified functor.
3. No statement was split off and no new public statement or node was introduced.
   Read all five proved private helpers and their dependency statements. Checked
   both directions of the model-vanishing equivalence, the isomorphism orientations,
   the empty scheme and empty open cases, and the fixed interval quantifiers.
   Verdict: the argument retains every hypothesis and conclusion. Independent
   LeanFinder search for exact open restriction versus derived pullback found
   `restrictFunctorIsoPullback`, which concerns Mathlib's different underived
   pullback, not the chosen tensorPullback/derivedPullback here. Repository searches
   and launcher grep confirmed the existing homology and open-cover APIs used.
   No shorter applicable theorem was found.
4. Read the proof from the target downward. It reduces to derived tensor homology,
   transports local vanishing through exact restriction, and applies the proved
   open-cover criterion. Each added import supplies a directly used declaration;
   the public statement import remains necessary. Compared old proof_deps with
   the new set: the three removed dependencies are all recorded under No longer
   needed, including the two that remain transitively needed. Read
   dag/units/sk-thm-picard-duality.json: its realized lists contain no occurrence
   of this item. Verdict: pruning is below the unit level and keeps its route.
5. Compared the node's proof steps, proof_deps and proof_origin with the Lean.
   The dependency set is exactly the union of the steps' uses; the steps describe
   the actual private comparisons and the final cover argument. Only permitted
   proof fields changed. Verified the restriction-adjunction dependency's Mathlib
   record. Checked [Stacks Tag 09U9](https://stacks.math.columbia.edu/tag/09U9):
   exactness, tensor compatibility and local detection of zero support this route.
   Verdict: Lean and DAG agree; no new-node fields are required.

Second reading changed only this report by adding the independent checks and
explicitly recording the remaining inherited `sorryAx`. No proof repair was needed.
