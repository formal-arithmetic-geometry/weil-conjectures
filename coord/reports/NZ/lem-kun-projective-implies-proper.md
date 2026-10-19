## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-projective-implies-proper.json` — statement, split; no new nodes.

## Attachments

None. The existing node `lemma-nagata-projective-space-base-change-proper` supplies the relative projective-space properness fact.

## WANTED

None.

## What was checked and corrected

The Lean source search covered `WeilConjectures/AlgebraicGeometry/ProjectiveSpace.lean`, especially the `ProjectiveSpace.instIsProper` instance (lines 163–176), and `WeilConjectures/AlgebraicGeometry/ChowLemma/ClosedModel.lean`. No declaration tagged `(blueprint: lem-kun-projective-implies-proper)` exists, and no sorry-free declaration states this item. The DAG definitions and properness lemmas were opened directly: `def-kun-projective`, `lem-weil-pbc-closed-immersion-proper`, `lemma-nagata-projective-space-base-change-proper`, and `lem-weil-pbc-proper-composition`.

The sole proof step now explicitly uses the projective factorization, properness of the closed immersion, properness of the relative projective-space structural map, and properness under composition. Each citation quote in `citations.json` is copied verbatim from the cited node. I checked that the projective definition supplies a finite index and closed immersion, that the relative-projective-space node has exactly the needed universal properness statement, and that the composition node concludes the stated morphism. The imported citation of `lem-chow-closed-model` was removed because that node concerns scheme-theoretic closures under extra affine and quasi-compact hypotheses and does not state the needed structural projection theorem. The omitted `lem-weil-pbc-proper-composition` dependency was added.

Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch (unavailable); the results support the underlying Proj and pullback properness but do not duplicate the relative projective-space statement. The existing Nagata blueprint node was found with `blueprint_refs.py` and reused, so no duplicate node was created. The projective-space theorem is recorded as an off-unit tool use because it is supplied by another unit's exact node.

## Review by NZ

I verified the item against the blueprint proof paragraph and the source definition of projective morphism. Step 1 cites only statements that provide its inputs: `def-kun-projective` gives the closed-immersion/structural-projection factorization; `lem-weil-pbc-closed-immersion-proper` gives properness of the first factor; `lemma-nagata-projective-space-base-change-proper` gives properness of the second factor for finite projective coordinates; and `lem-weil-pbc-proper-composition` gives properness of their composite. The finite-index and scheme hypotheses are exactly those in the cited statements. I checked the small edge case $N=0$: the projective-space theorem still applies, and the composition argument remains valid. The source and DAG contain no finished Lean declaration for this item. The only correction was replacing the unsuitable Chow-model citation and adding the missing composition citation.

## Source reading and blueprint equivalents

I read Stacks Tag 01WC in `literature/stacks-project/morphisms.tex`, label `lemma-locally-projective-proper` (lines 10580–10616): it reduces a closed immersion into relative projective space to properness of both factors and composition, and identifies projective space as a base change of its integral model. This is the same argument used here, with the existing exact Nagata projective-space node supplying that part. Its definition `def-nagata-projective-space-base-change` explicitly identifies the classical $\mathbf P^N_Y$ with the homogeneous-coordinate index set $\{0,\ldots,N\}$, so no coordinate-count or different projective-space convention is hidden. I also searched the whole blueprint for `projective-proper` and found `lem-pc-projective-proper`, whose main assertion is the same, with extra curve and field-base-change corollaries; it is recorded in `same_as`. No new nodes or Mathlib leaves were created, and there is no unfinished portion. The mathlib searches record the actual returned names and service notes; the first Loogle query had an unknown identifier, so a qualified query was run and read.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against the imported blueprint paragraph and Stacks 01WC (`morphisms.tex`, `lemma-locally-projective-proper`), together with `definition-projective`; PASS. The blueprint's projective convention is a global closed immersion into finite-dimensional projective space, called H-projective by Stacks. The split uses precisely that convention, not an unwarranted global factorization of a merely locally projective morphism. No statement change or dispute is needed.
- Step 1: opened the statements of `def-kun-projective`, `def-nagata-projective-space-base-change`, `lemma-nagata-projective-space-base-change-proper`, `lem-weil-pbc-closed-immersion-proper`, and `lem-weil-pbc-proper-composition`; PASS after adding the explicit coordinate-convention citation. The definition supplies N and the closed immersion over Y; the base-change definition identifies both the projective space and its projection; the proper-space theorem applies to the finite set {0,...,N} over the arbitrary scheme Y; clause (a) gives properness of i; composition applies to exactly X → P^N_Y → Y. The three parenthetical assertions are supplied individually by the three properness statements, without extra hypotheses. Compared the properness assertions with Stacks 01WC, 01W5 (`lemma-closed-immersion-proper`), and 01W3 (`lemma-composition-proper`); no unquoted non-elementary fact is used and the step is correctly non-elementary.
- New nodes: none; B1–B7 and duplicate/Mathlib searches for new nodes are vacuous. Opened the existing equivalent `lem-pc-projective-proper` (same main assertion, additional curve and base-change clauses), already recorded in `same_as`; the existing Nagata theorem supplies the needed tool without creating another node or moving the item's conclusion into a new node.
- Edge cases: N=0 uses one homogeneous coordinate and P^0_Y=Y; N=1 uses two coordinates. Over a field these are the point and projective line. Empty X gives a closed immersion with the same argument; empty Y forces X empty. No nonempty, Noetherian, field, affine, or positive-dimension assumption is used. PASS.
- Lean attachment check: read `WeilConjectures/AlgebraicGeometry/ProjectiveSpace.lean` in the read-only slopmaster2 source, especially the definition at lines 125–131 and `ProjectiveSpace.instIsProper` at lines 162–176, and searched the item id and projective/proper keywords across WeilConjectures and Comparator. The instance states the relative-space factor only; its docstring's projective-morphism consequence is not a declaration stating this entire item. The existing factor node already records this attachment. No compiler or Lean-writing action was taken.

Changes: added `def-nagata-projective-space-base-change` to step 1 and proof dependencies, with its verbatim statement in `citations.json`, so the homogeneous-coordinate identification is explicitly justified (C1/C4). Added the exact Stacks label to the item's external source (B5). Preserved the correct statement, argument, existing-node reuse, and all first-reader report sections.

## Repair of landing return

The landing was refused because `def-kun-projective` had changed after the reviewed delivery. I rebased the citation against the current DAG copy and re-read its complete statement. The verbatim quote in `citations.json` now includes the blueprint's explicit convention that `\mathbf P^N_Y=\mathbf P(\{0,\ldots,N\};Y)` and the structural projection, while retaining the finite closed-immersion factorization used by step 1. The proof and dependency list already use the current projective-space convention; no mathematical step needed changing. I rechecked all other cited nodes against the current DAG and found no further changes.

## Second reading by NZ

- Item statement: checked against the blueprint node and Stacks Tag 01WC, label `lemma-locally-projective-proper`; the projective factorization and all three parenthetical properness assertions agree hypothesis by hypothesis, including arbitrary schemes and $N=0$.
- Step 1: opened every cited node and checked that `def-kun-projective` supplies the finite closed immersion factorization, `def-nagata-projective-space-base-change` identifies the homogeneous-coordinate projective space, the Nagata properness node applies to its finite index set, the closed-immersion node gives properness of $i$, and the composition node gives properness of $q\circ i$; no uncited non-elementary fact remains.
- New nodes: none; B1–B7 are vacuous. The existing projective-space properness node was checked as the cross-unit tool, and the existing blueprint equivalent `lem-pc-projective-proper` was searched and recorded in `same_as`.
- Edge cases: checked $N=0$ and $N=1$, empty source or target, and field bases; no extra nonemptiness, finiteness, or characteristic hypothesis is introduced.
- Changes made: retained the repaired explicit base-change citation and proper-composition dependency, and retained the corrected Stacks label; no further mathematical or statement changes were needed.
