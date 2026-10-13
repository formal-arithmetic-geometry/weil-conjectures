## What changed

Proved `AlgebraicGeometry.Scheme.picardUniversalRankMatch_residue_iff` in
`Sheaf.AlgebraicGeometry.PicardUniversalRankMatchResidueCriterion` without changing its
signature, visibility, or existing docstrings. Added only private, fully proved helpers
for rank reflection, ordinary flat base change, comparison of cartesian-square
models, and the empty-fibre case. Updated the existing node's proof route and dependencies.
No statement, definition, target, or other module was changed.

The shorter route uses Stacks [02KH](https://stacks.math.columbia.edu/tag/02KH), part (1),
in degree zero: every map to the residue-field spectrum is flat. The existing
`flatBaseChangeResolutionLift` and `flatBaseChangeResolutionBeta_isIso`, followed by
`Functor.rightDerivedZeroIsoSelf`, supply the ordinary-image comparison. The identity
test and `finiteLocallyFreeOfRank_stalk_finrank` recover the prescribed rank on a nonempty
fibre. Empty fibres give zero images and use the empty free module of rank zero.

Added proof-only imports:
- `Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionIso`;
- `Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsLift`;
- `Sheaf.AlgebraicGeometry.PicardPullbackLocalRanks` (`import all` for private `tensor_rank`);
- `Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFiniteRanks` (`import all` for private
  `finiteLocallyFreeOfRank_of_isEmpty`);
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank`.

The module compiles cleanly with `lcompile.py`, using the library's standard options.
No file-level elaboration options were added. The forward proof uses a fibre point only
in the nonempty branch. The rank-zero and empty-base cases require no such point.
The unit `sk-prop-av-cube` and its route were preserved; its realized lists contain
no mandatory internal step of this item.

Repair of the landing return at 84ed4e5b8: removed the duplicate private declarations
`empty_rank` and `tensor_rank`. The former call now uses the existing
`finiteLocallyFreeOfRank_of_isEmpty`; all tensor-rank calls use the existing `tensor_rank`.
Both imports are proof-only `import all`, which exposes the imported private lemmas
inside this file without changing their visibility or any other module. Checked both
import directions: neither creates a cycle. No other module was adapted. The second
reading below is the original review, before this repair; a new reader must review
these changes. The repaired module compiles with the standard options.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.picardUniversalRankMatch_residue_iff`
(node `lem-sc-picard-universal-rank-match-residue-criterion`).

One of one sorries closed in the item; zero new holes; zero split-off statements.
No `sorry` remains in the delivered module. This is a proof from existing declarations,
not a claim that all imported dependencies have been proved without `sorry`.
All added private lemmas and definitions are complete.

## No longer needed

Removed proof-only imports:
- `WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank` (its instances are available
  through the imported rank modules);
- `Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`, node
  `lem-pc-rf-perfect-base-change`;
- `Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel`, node
  `lem-sc-perfect-finite-free-residue-model`.

The proof does not require the original perfect-direct-image/minimal-residue-model
route, its derived-fibre Betti data, or truncation and differential calculations.
These two dependency edges were removed from the item's DAG node. Their own modules
and descendants may remain necessary elsewhere in the targets' closure; this report
claims pruning only from this item's route. No public imports were removed.

## Where the brief, the DAG or earlier work was wrong

The original delivery and second reading missed two duplicate private theorems.
The landing tool correctly rejected them. Both are now imported and reused, with
no signature or visibility changes to the existing library. No false statement was found. The DAG and existing theorem docstring
plan a longer perfect-complex argument. For this criterion it suffices to use ordinary
flat base change because every further map to a field spectrum is flat. The updated
node records the actual shorter proof; the existing docstring remains unchanged.
The source checked was Stacks 02KH, part (1), and 0BDP, first proof paragraphs.
There is no change to the theorem's interpretation and no forced adaptation.

## Earlier second reading (a previous round; superseded)

1. **Unchanged interface — pass.** Compared the complete delivered module with the
   repository by `diff`. Independently checked that the existing theorem signature
   and docstring are byte-for-byte identical. Only proof-only imports, private
   proved helpers, and the theorem proof changed. No definition used by another
   module, public import, visibility, or target statement changed. No change record
   or forced adaptation is required.

2. **Proof and axioms — pass.** Read every helper and both implications and compiled
   the module with `lcompile.py` without errors or warnings (21 seconds). A scratch
   copy prints axioms for all thirteen declarations, including the three private
   definitions. Every declaration uses only `propext`, `Classical.choice`, and
   `Quot.sound`, except `flat_image_iso`, `fibre_image_rank`, and the main theorem,
   which additionally inherit `sorryAx` from open dependencies. There is no local
   `sorry`, axiom, unsafe/opaque declaration, external implementation, or hollow
   definition. The chosen tensor adjunction is already proved; the comparison
   isomorphisms are universal-property transports of the explicit tensor functor.
   The augmented lift is eliminated inside a theorem, not used to define arbitrary
   data from an unproved existence statement.

3. **Split statements and edge cases — pass.** There are no new public statements,
   nodes, split-off statements, or holes. On an empty fibre, every further fibre
   is empty by the constructed projection, its image modules are zero of rank zero,
   and the coefficient rank is vacuous by the empty cover. On a nonempty fibre,
   equality of the two ranks uses a genuine point and the existing stalk-finrank
   theorem. Rank zero requires no positive-rank assumption. An empty further base
   has no test point. No connectedness, surjectivity, or cohomological-vanishing
   hypothesis was silently introduced.

4. **Shortest route, imports, and pruning — pass.** Read the ordinary rank predicate,
   fixed-rank pullback instance, tensor adjunction/composition results, augmented
   resolution lift, and flat-base-change isomorphism. Searched the source-library
   direct-image modules and Sheaf flat-base-change and rank modules under alternate
   terms; the other canonical counit comparison needs invertibility and positive
   cohomology vanishing, so does not shorten this general fixed-rank proof. Checked
   Stacks [02KH](https://stacks.math.columbia.edu/tag/02KH), part (1), for the chosen
   degree-zero comparison and [0BDP](https://stacks.math.columbia.edu/tag/0BDP) for
   context. Each added import supplies a theorem or instance used by the proof and
   is correctly private to it. The report's two removed dependency edges are exactly
   the old proof dependencies absent from the new proof. The unchanged unit
   `sk-prop-av-cube` has empty realized statement/step lists, so this internal
   shortening bypasses no mandated realized unit step. Pruning here means removal
   from this item's route, not a claim of whole-library unreachability.

5. **DAG agrees with Lean — pass.** Only `proof`, `proof_deps`, and `proof_origin`
   differ in the existing node. The dependency list is exactly the union of the
   proof steps' `uses`. The steps describe rank reflection and stalk comparison,
   zero images on empty fibres, degree-zero flat base change, and transport to
   further fibre products, matching the code. No new-node fields are needed.

Second reading changed only this report by recording the independent checks and
axiom audit; no Lean or DAG repair was necessary. One original hole closed, zero
holes added, and zero statements split off.

## Second reading by Q4

Independent reading of the repaired delivery, including the replacement of the
previous duplicate rank helpers by proof-only `import all` imports.

1. **Interface — pass.** Read the full repository/sandbox diff. Compared the sole
   existing theorem signature byte for byte, and compared all public imports.
   Both are unchanged, as are the existing module and theorem docstrings.
   Only the item's proof, private proved helpers, and proof imports differ.
   No change record or adaptation is required. The open coherent-cokernel change
   mentions this module only as a transitive import user and needs no edit here.

2. **Proof and axioms — pass.** Compiled the repaired module with `lcompile.py`
   cleanly (22.4 seconds). Rebuilt the stale scratch axiom audit from the repaired
   source and compiled it (30.2 seconds). Audited all ten local private declarations,
   both imported rank helpers, and the main theorem. All use only `propext`,
   `Classical.choice`, and `Quot.sound`, except `flat_image_iso`, `fibre_image_rank`,
   and the main theorem, which also inherit `sorryAx` from open dependencies.
   There is no local `sorry`, forbidden declaration, or hollow definition.
   `fibreMap` is explicitly constructed by `pullback.lift`. The chosen adjunction
   and composition isomorphisms are already proved universal-property comparisons
   of the constructed tensor pullback. The augmented resolution lift is eliminated
   within a theorem and supplies no definition of arbitrary unproved data.

3. **Split statements and edge cases — pass.** No new public statements or nodes,
   no split-off statements, and no added holes. Read the reused `tensor_rank` and
   `finiteLocallyFreeOfRank_of_isEmpty` proofs: rank transports across the pullback
   comparison, and the empty-source assertion uses an empty open cover. For a
   nonempty fibre the identity test and an actual stalk force the chosen rank to
   equal the prescribed rank. For an empty fibre the explicit projection makes
   every later fibre empty; additive direct image is zero and has rank zero.
   Rank zero and an empty further base require no additional hypotheses.

4. **Route and pruning — pass.** Read the imported resolution lift and isomorphism,
   tensor adjunction/composition, rank transport, stalk-finrank theorem, and rank
   predicate. Searched Mathlib through launcher grep and Loogle for derived degree
   zero/direct-image comparisons, and searched the source library and Sheaf under
   base-change/isomorphism and rank-transport terms. The proof already uses the
   Mathlib `rightDerivedZeroIsoSelf` returned by those searches. Checked Stacks
   [02KH](https://stacks.math.columbia.edu/tag/02KH), part (1), and
   [0BDP](https://stacks.math.columbia.edu/tag/0BDP): flat degree-zero base change
   suffices over the residue field. All added imports supply used declarations or
   instances and are proof-only; `import all` exposes the reused private helpers
   locally. The removed old dependency edges are exactly
   `lem-pc-rf-perfect-base-change` and `lem-sc-perfect-finite-free-residue-model`,
   both listed above. The unchanged unit `sk-prop-av-cube` has empty realized
   statement/step lists, so no mandated realized step is bypassed.

5. **DAG — pass.** Compared the existing JSON records: only `proof`, `proof_deps`,
   and `proof_origin` changed. Verified every dependency's recorded declaration,
   and that `proof_deps` equals the union of the steps' `uses`. The steps explicitly
   record the two reused private helpers, empty-fibre reduction, stalk rank
   comparison, degree-zero flat base change, and cartesian-square transport,
   agreeing with the repaired Lean. No new-node fields are needed.

This second reading changed only this report and the nondelivered scratch audit;
no Lean or DAG repair was necessary. Closed:
`AlgebraicGeometry.Scheme.picardUniversalRankMatch_residue_iff` (one original hole).
Added holes: none. Split-off statements: none. The imported dependencies remain
subject to their own proof work; this delivery does not claim their closure.
