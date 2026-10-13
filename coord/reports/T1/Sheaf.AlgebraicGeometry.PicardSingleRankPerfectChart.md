## What changed

Proved AlgebraicGeometry.Scheme.exists_picardSingleRankPerfectChart with its original
signature and public imports unchanged. Added proof-only imports of the two new, proved
auxiliary modules PicardReferenceRankNeighbourhood and ProperFlatDirectImagePerfectChart,
plus the existing FiniteLocallyFreeStalkFinrank and upstream LocallyFreeRank API.

PicardReferenceRankNeighbourhood proves surjectivity and the fixed reference rank near
s. It uses a proof-only `import all Sheaf.AlgebraicGeometry.PicardFiberRankClopen`
to reuse that module's existing private local-rank declarations directly.
The tensor structure-sheaf comparison identifies the residue-fibre global-functions ring
with its residue field; the idempotent criterion gives connectedness.

ProperFlatDirectImagePerfectChart proves the nonnegative perfect chart directly from
exists_proper_flat_affine_cech_perfect_model. Bounded flat terms give K-flatness and
all-module tensor vanishing. The relative-flatness premise now uses the existing private
Modules.isFlatOver_of_isFiniteLocallyFree theorem via proof-only
`import all Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric`; the duplicate
finiteLocallyFree_flatOver helper is removed. The recorded K-flat derived-pullback counit and degree-zero
right-derived pushforward give the ordinary direct-image comparison.

The item's own proof forces the ranks in local witnesses to equal the reference rank
using surjectivity and stalk finrank, glues the restrictions, refines the rank neighbourhood,
and transports rank along the chart isomorphisms in both directions.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.Scheme.exists_picardSingleRankPerfectChart
(node lem-sc-picard-single-rank-perfect-chart): 1 of 1 original sorries closed.

Also proved AlgebraicGeometry.Scheme.exists_picardReferenceRankNeighbourhood
(node lem-sc-picard-reference-rank-neighbourhood) and
AlgebraicGeometry.Scheme.exists_properFlatDirectImagePerfectChart
(node lem-sc-proper-flat-direct-image-perfect-chart). Every private helper is proved.
No sorry remains in any of the three delivery modules. No new holes were added or split off.
Existing imported project declarations may still depend on project sorries; this delivery
proves the item from those existing statements and does not assert the whole target is axiom-free.

The repaired modules compile together through lcompile.py, in the supplied universes u,w.
The duplicate rank and relative-flatness declarations are removed, not renamed or restated. No existing module
is adapted and no existing signature or visibility changes.
Empty test schemes are covered by the empty indexed cover; no witness point is requested
when there is no test point. Rank zero uses the same stalk-finrank comparison. The perfect
chart takes the nonnegative natural-number Cech bound as an integer; no sign assumption is lost.

## No longer needed

Removed the duplicate private AlgebraicGeometry.Scheme.finiteLocallyFree_flatOver
from ProperFlatDirectImagePerfectChart. Removed its direct proof import of
WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine; the existing theorem
in PerfectCohomologyFromGeometric now supplies relative flatness. LocallyFreeAffine
remains transitively imported by that module, so this is no global closure pruning.

No original import of the item was removed: these imports support its unchanged statement.
In the new PicardReferenceRankNeighbourhood module, removed the now-unused direct imports
Sheaf.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank and
WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank. Their results are used internally
by the existing rank API; these modules remain in the transitive import closure.
The originally planned direct proof dependency lem-pc-rf-perfect-base-change,
module Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange, is not needed by this proof.
It has been removed from this node's proof_deps. The proof instead uses the existing
proper-flat affine Cech perfect-model route. This is pruning of this item's planned
proof dependency, not a claim that no other target importer needs that module.

The perfect-complex definition remains a statement dependency, and the single-rank
predicate, tensor pullback adjunction, fibre-rank clopen result and stalk-finrank theorem
remain needed, directly or through the proved auxiliary modules. The old direct proof dependency lem-sc-picard-fiber-rank-clopen is now used transitively
through PicardReferenceRankNeighbourhood; its module remains in the import closure.
The old direct proof dependency def-pc-perfect-complex remains a statement dependency
and is used by the chart auxiliary. These are relocations, not pruned modules.
No other planned module is declared unnecessary.

## Where the brief, the DAG or earlier work was wrong

The latest return identified another duplicate: finiteLocallyFree_flatOver restated
Modules.isFlatOver_of_isFiniteLocallyFree word for word. Repaired by removing its
declaration and applying the existing private theorem through import all. The chart
node records this dependency on
lem-sc-valuation-proper-coherent-higher-direct-images-perfectness, specifically its
relative-flatness helper; the cohomology-model theorem itself is not applied.
The earlier second-reading audit did not catch this duplicate. Its stale section
has been removed so the second reader can audit this repaired version.

The returned delivery copied eight private rank theorems from PicardFiberRankClopen,
which the import-pruning checker correctly rejected as duplicate statements. Removed
rank_unique, rank_restrict_le, localRank_unique, exists_localRank, localRank_isOpen,
localRank_isClopen, pullback_rank_iff and tensorPullback_rank_iff, together with the
copied localRank definition and restrictPullbackIso. The earlier second reading was
wrong to conclude that private helpers could not be reused across modules: Lean's
`import all` provides exactly this access. The repaired proof imports and uses the
existing declarations without changing that module or any signature.

No false statement or interface error was found. The original three-step plan is valid,
but did not expose the connected-fibre/rank-locality glue or the conversion from ordinary
bounded flat models to the derived chart. Both are now complete Lean proofs.
The affine Cech model avoids separately assembling the perfect direct-image base-change
statement and a fibre Tor-amplitude truncation. The unit and chapter route are preserved;
the unit's realized fields contain no node bypassed by this change.

LeanSearch was unavailable (Internal Server Error). LeanFinder/Loogle and Mathlib/library
source searches were used; the nodes record unavailable service results without inferring absence.

## New nodes

lem-sc-picard-reference-rank-neighbourhood, in
lean/Sheaf/AlgebraicGeometry/PicardReferenceRankNeighbourhood.lean: a proved geometric
rank-neighbourhood lemma with no second bundle, derived complex or rank predicate.

lem-sc-proper-flat-direct-image-perfect-chart, in
lean/Sheaf/AlgebraicGeometry/ProperFlatDirectImagePerfectChart.lean: a proved derived
chart lemma with no reference bundle or rank condition. Its proof is from the existing
Cech model and K-flat comparison declarations. Both nodes have exact Lean signatures,
source locations, proof steps, dependency lists and the three search kinds.

No signatures or definitions of existing public declarations changed; no change record
or forced adaptation is required.

## Second reading by T1

1. **Statements unchanged.** Compared each delivered module with the repository version. The existing declaration `AlgebraicGeometry.Scheme.exists_picardSingleRankPerfectChart` has the byte-for-byte original signature. The two auxiliary declarations are new nodes whose Lean statements match their DAG records exactly; no target hypothesis or conclusion changed.

2. **Proof and axioms.** Compiled all three modules with `lcompile.py --all`; compilation succeeds without warnings. A scratch axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound` for the reference-rank theorem. The chart theorems additionally inherit `sorryAx` only through pre-existing imported project declarations; no `sorry`, axiom, unsafe, opaque, extern, or implemented-by declaration occurs in the delivered sources, and no definition contains `sorry`.

3. **New statements.** Checked both auxiliary statements against their source arguments and edge cases (empty test schemes and rank zero). The reference-rank statement is the needed connected-fibre and clopen-rank reduction, while the direct-image statement contains no reference bundle or rank predicate. Searches found no duplicate library or Mathlib declarations. Their DAG nodes include source, proof steps, dependencies, Lean records, and search records.

4. **Route and pruning.** The item proof uses the two auxiliary reductions, preserves the unit's realized route, and transports ranks through the existing tensor-pullback and stalk-finrank APIs. The copied private rank helpers and duplicate relative-flatness helper were removed; `proof_deps` is the union of the actual proof steps. The unused direct dependency on `PerfectDirectImageBaseChange` is pruned and recorded above. Public imports needed by statements remain public; proof-only imports are plain imports (with `import all` only to access existing private proof declarations).

5. **DAG agreement.** Recomputed each node's proof-dependency union from its Lean proof plan and verified the delivered signatures against the node files. The existing item node changes only `proof`, `proof_deps`, and `proof_origin`; auxiliary node metadata agrees with their modules. No unit statement or realized step is bypassed.

Changed nothing during this second reading beyond this report section. The dry-run delivery and final delivery commands are run after this audit.
