## What changed

Replaced the sole `sorry` in `AlgebraicGeometry.Scheme.picard_diagonal_locally_closed`
with a complete Lean assembly of the four steps of Stacks Tag 0BDP. The original theorem
signature, universe, public imports, visibility and docstring are unchanged.

Three new modules isolate distinct unfinished parts of the argument:

- `Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus` defines the concrete universal
  direct-image rank/base-change condition and states its finitely presented immersion.
- `Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus` states the retrocompact open where
  the canonical evaluation counit becomes invertible, assuming the rank/base-change
  condition on the ambient scheme.
- `Sheaf.AlgebraicGeometry.PicardPullbackEvaluation` states the projection-formula
  implication from an actual pullback isomorphism to those necessary conditions.

The main proof composes the two immersions, obtains all four morphism properties from
Mathlib instances, and proves both directions of the factorization equivalence. In the
forward direction its descending module is the actual direct image `p_* q^* E`, and its
isomorphism is the inverse of `asIso` of the counit. In the reverse direction the two
representing properties give successive factorizations, whose composite is checked by
associativity. Existential representing schemes are used only as witnesses in a proof;
no definition chooses data from a mere existence theorem.

All four modules compile together through `lcompile.py`, in import order. The existing
node now records the actual three dependencies and the Lean assembly. The unit's theorem
of the cube and its route are retained: this reduction still supplies exactly the same
Tag 0BDP result to the general cube theorem.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.picard_diagonal_locally_closed`
(node `lem-sc-picard-diagonal-locally-closed`). The item's module has no remaining `sorry`.

Added three holes, each the whole proof of a public named theorem with a source, a full
natural-language proof, and its own DAG node:

- `AlgebraicGeometry.Scheme.exists_picardDirectImageRankLocus`
  (`lem-sc-picard-direct-image-rank-locus`).
- `AlgebraicGeometry.Scheme.exists_picardEvaluationOpenLocus`
  (`lem-sc-picard-evaluation-open-locus`).
- `AlgebraicGeometry.Scheme.picard_rankCondition_and_isIso_counit_of_pullback`
  (`lem-sc-picard-pullback-evaluation`).

This is a decomposition, not a proof without assumptions: one upper hole closed and
three lower holes added, a source-level net of -2. The new definition
`AlgebraicGeometry.Scheme.PicardDirectImageRankCondition` contains no hole.

The three lower statements are strictly parts of the argument. The rank-locus theorem
does not assert descent or evaluation invertibility. The evaluation theorem works only
inside an already rank-matched ambient scheme and constructs an open immersion. The
pullback-evaluation theorem constructs no locus and proves only necessary conditions.
The combination and the explicit construction of the descending module are proved here.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`.
- `Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`.

The first two remain needed in the rank-locus intermediate and are imported there;
their nodes `lem-pc-rf-perfect-base-change` and `lem-sc-perfect-h0-locally-closed` are
retained below it. The openness and closed-image Mathlib leaves
`lem-weil-pbc-flat-lfp-open` and `lem-weil-pbc-proper-closed-image` likewise remain
in that intermediate's plan.

`lem-pc-projection-formula` and its `Sections` declaration are not used by this reduction.
Its available Lean statement is only for invertible modules, whereas Tag 0BDP uses
finite locally free modules of arbitrary rank. The new necessary-condition theorem
uses the source's local finite-free calculation instead. No public import was removed.
No other node or module is asserted to leave the targets' entire import closure: the
maintainer's closure ledger decides that separately.

## Where the brief, the DAG or earlier work was wrong

The Lean declaration attached to `lem-pc-projection-formula`,
`Modules.nonempty_higherDirectImage_tensorObj_pullback_iso` in `Sections`, requires
`N.IsInvertible`. It therefore does not directly provide the arbitrary-rank finite
locally free case used in the item's third step. Stacks Tag 01E8 explicitly covers
finite locally free modules; the new source-backed implication records the local
finite-free unit calculation and its canonical-map compatibility instead of silently
applying the rank-one theorem.

The first two original geometric inputs have derived-category localization and
additivity instance parameters that are not supplied by the item's signature. The
rank-locus intermediate leaves the source's local perfect-complex construction and
its interface transport to a separately claimable item, retaining both existing inputs
in its plan. Neither original statement nor any dependency interface was altered.

The original fourth DAG step marked the entire determinant/pairing construction
`elementary: true`. It is substantive; it is now a separate sourced theorem with a
complete proof in words, while only the final composition and witness construction
are marked elementary.

Checked the new statements against the source's degenerate cases: rank zero gives
zero direct images and determinant 1, hence the whole rank-zero component; an empty
base has no rank-neighbourhood obligations; the identity morphism gives the whole base.
The rank condition checks every further base change, including nonreduced test schemes,
and explicitly requires the canonical base-change maps to be invertible. The dual
pullback calculation in the necessary-condition theorem uses the stated hypothesis
that E is finite locally free. No additional geometric assumption or target weakening
is introduced. Mathlib searches found only ring-rank, generic adjunction, or linear
perfect-pairing results. LeanSearch timed out and is recorded as unavailable.

## New nodes

`def-sc-picard-direct-image-rank-condition` records the concrete predicate used by the
three intermediate statements. It consists of actual direct-image finite local freeness,
universal common local ranks, and invertibility of actual canonical base-change maps.
It is a definition in `PicardDirectImageRankLocus`, with no chosen object and no `sorry`.

`lem-sc-picard-direct-image-rank-locus` records the rank decomposition and simultaneous
lowest-cohomology construction, the first two steps of the item's source proof. It
stops before any pairing or descent condition.

`lem-sc-picard-evaluation-open-locus` records the cup-product determinant open and the
identification of its universal property with counit invertibility, the last two
paragraphs of Tag 0BDP. It assumes the complete rank/base-change condition explicitly.

`lem-sc-picard-pullback-evaluation` records the projection-formula implication for an
actual pulled-back finite locally free module, including universal ranks and canonical
base-change maps. It follows the projection-formula paragraph of Tag 0BDP and the
finite-free local calculation of Tag 01E8.

No change record or forced adaptation is required: existing signatures, definitions,
public imports and visibility are unchanged, and no other existing module was edited.

## Second reading by Y2

1. **Visible declarations: pass.** Compared every delivered module with the read-only
   repository. Only the item already exists. Its theorem signature, universe, visibility,
   docstring and public imports are byte-for-byte unchanged; the diff changes its proof
   and three private proof imports. The other three modules and four associated nodes
   are new. No existing definition or statement is changed, so no change record is needed.
2. **Kernel and holes: pass as a decomposition.** All four files compile through
   `lcompile.py --all` without errors or warnings. A scratch module prints the axioms
   of the original theorem, the new definition and each intermediate theorem. Only
   `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx` occur; the
   definition has no `sorryAx`. The three named theorem bodies are the only delivered
   holes. No forbidden declaration mechanism occurs. The forward witness is an actual
   pushforward; no data definition selects an arbitrary witness of an unproved existence.
3. **Intermediate statements: pass.** Independently read Stacks
   [0BDP](https://stacks.math.columbia.edu/tag/0BDP),
   [0BDL](https://stacks.math.columbia.edu/tag/0BDL), and
   [01E8](https://stacks.math.columbia.edu/tag/01E8).
   Rank-locus representability, the evaluation determinant open, and the necessary
   conditions for a pulled-back bundle are distinct proper parts of that argument.
   Checked zero rank, empty bases, the identity morphism, varying ranks on disjoint
   base components, and arbitrary nonreduced further test schemes. The common local
   rank condition includes the pulled-back E on the full inverse image of the base
   neighbourhood, and both base-change maps are the actual adjoint-defined maps.
   Repeated searches with new wording through leanfinder, loogle and grep, and inspected
   the upstream ProjectionFormula module: its proved formula also assumes invertibility,
   so it cannot close the arbitrary-rank implication. No duplicate or quick complete
   replacement was found. Generic adjunction results cover only its categorical tail.
4. **Route and pruning: pass.** Read the proof from its final factorization equivalence
   down to the three supplied intermediates. No shorter proved library theorem was found.
   New public imports supply names used in public statements or the predicate; the two
   perfect-complex proof-plan imports are private. Every original proof dependency is
   accounted for under No longer needed: four remain in the rank-locus plan, and the
   invertible-only projection formula is replaced by the local finite-free calculation.
   The cube unit still reaches exactly the same Tag 0BDP statement through the general
   cube theorem. Its existing `realized` arrays are empty in the repository; this delivery
   leaves that pre-existing metadata untouched and does not replace a unit step.
5. **DAG: pass.** Checked each new Lean signature against its node record verbatim,
   the union of each proof's uses against proof_deps, and source, origin, chapter, unit,
   creation, blueprint provenance and search fields. The item node describes exactly the
   four Lean assembly steps. Each remaining hole has its own sourced node and a complete
   proof in words, rather than merely restating the item.

Second reading changed only the new rank-condition definition's documentation (added its
source and blueprint identifier), and the rank-locus theorem's proof docstring (made the
canonical base-change-map calculation explicit in the degree-zero free model). No Lean
proof or signature needed repair. Added this independent review; the result remains one
upper hole closed, three lower holes added, net -2, with no claim of completed proof.
