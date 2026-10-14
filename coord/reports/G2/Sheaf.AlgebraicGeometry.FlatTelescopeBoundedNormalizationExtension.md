## What changed

Reduced `AlgebraicGeometry.exists_flat_telescope_comparison_of_bounded_normalization`
to construction of forward morphisms and a separate invertibility propagation theorem.
The parent supplies bounded invertibility by rewriting the morphisms to the given
bounded isomorphisms, applies invertibility propagation, and packages each morphism
with `asIso`. Naturality and the equation for the unchanged `e` then remain the same
morphism equalities. The original signature and its public imports are unchanged.
The proved common-refinement
helper extends stage naturality to all homotopy maps between these representatives;
the parent uses that result as the naturality hypothesis of invertibility propagation.

The new modules are `Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationMorphisms`,
`Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationUnshiftedIsIso`,
`Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationIsIso`, and
`Sheaf.AlgebraicGeometry.FlatTelescopeStageNaturality`. The first two each have
one public named theorem left with `:= by sorry`, a complete argument in its
docstring, and a new DAG node. The third is proved: invertibility of a translated
component follows from the shift equation and cancellation of an invertible map. There are no new definitions or choices of permanent data.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_flat_telescope_comparison_of_bounded_normalization`
(node `lem-sc-flat-telescope-bounded-normalization-extension`).

Also proved `AlgebraicGeometry.flat_telescope_stage_naturality`
(`lem-sc-flat-telescope-stage-naturality`) by common-refinement localization
and cancellation; its actual module compiled locally in 3.7 seconds.

Added two holes:

- `AlgebraicGeometry.exists_flat_telescope_normalization_morphisms`
  (`lem-sc-flat-telescope-normalization-morphisms`): forward maps, bounded agreement,
  stage naturality, and the normalized shift square, without inverse maps.
- `AlgebraicGeometry.flat_telescope_normalization_unshifted_isIso`
  (`lem-sc-flat-telescope-normalization-unshifted-is-iso`): invertibility propagation
  only on literal unshifted telescope cones, for a supplied normalized stage-natural
  morphism family already invertible on bounded telescope models and natural
  for every homotopy map between the representatives.

Also proved the new
`AlgebraicGeometry.flat_telescope_normalization_isIso`
(`lem-sc-flat-telescope-normalization-is-iso`) from the unshifted invertibility
theorem and the supplied shift equation, using `IsIso.of_isIso_comp_right`.

This is a decomposition of one hole into two, not a net proof gain. The first
statement omits invertibility and the second proves only invertibility for supplied
maps. The combination in the parent is actual Lean, using bounded agreement and
`asIso`, rather than an application of a renamed copy of the original theorem.

Edge cases checked mathematically: zero towers and empty schemes give the unique
zero-object morphisms and their invertibility. Finite partial sums have stagewise
upper bounds; the full tower need not have a uniform bound. Translates are handled
by the explicit normalized shift equation, and no replacement for `e` is chosen.

## No longer needed

Removed the parent's direct proof imports
`Sheaf.Algebra.Homology.KFlatTelescopeClosure` and
`Sheaf.AlgebraicGeometry.FlatTelescopeStageMapRefinement`.
The old direct proof dependencies replaced in the parent are
`def-pc-derived-pullback`, `def-sc-flat-telescope-stage-map`,
`def-sc-scheme-canonical-shift-unit-iso`, `def-sc-scheme-canonical-tensor-shift`,
`lem-pc-kflat-closure`, and `lem-sc-flat-telescope-stage-map-refinement`.
They remain in the statements or in the lower proof plans; none is claimed
unreachable from the targets.

Their nodes remain needed by the two new intermediate theorems, which import them;
there is no whole-closure pruning claim. The parent now directly uses only
`lem-sc-flat-telescope-normalization-morphisms` and
`lem-sc-flat-telescope-normalization-is-iso`, and
`lem-sc-flat-telescope-stage-naturality`. No blueprint unit or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original dependencies provide K-flat closure and common refinements, but neither
states construction of the comparison for the supplied bounded normalization.
The old plan leaves that construction and its invertibility argument as prose;
this delivery separates those obligations rather than treating refinements as a
ready-made normalized comparison theorem.

[Stacks 06YS](https://stacks.math.columbia.edu/tag/06YS) gives termwise-flat K-flat
resolutions, and [Stacks 06YJ](https://stacks.math.columbia.edu/tag/06YJ) supplies
exact derived pullback and K-flat computation. The supplied-tensorator normalization
is an inherited agent expansion, not a theorem stated literally in those tags.

At the first local compile the shared build lacked
`Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization.olean`; its landed source
was present. No dependency was copied or redeclared to bypass the green-build rule.

## New nodes

`lem-sc-flat-telescope-normalization-morphisms` records the forward sum/cone map,
presentation independence, bounded agreement, and inherited shift square. Its
statement does not assert that these maps are invertible.

`lem-sc-flat-telescope-normalization-unshifted-is-iso` records propagation of bounded
invertibility through coproducts and transition-cone triangles, restricted to
literal unshifted telescopes. The final triangle argument uses Mathlib's
`CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂`; the model transports and
coproduct comparison remain to be formalized.

`lem-sc-flat-telescope-normalization-is-iso` records the proved passage from
unshifted invertibility to all representatives, including one-fold translates.

`lem-sc-flat-telescope-stage-naturality` is the proved common-refinement
cancellation argument for arbitrary target functors. It is used in the parent
to supply full naturality to the invertibility propagation theorem.

No change record is needed: no existing definition, signature, or visibility changes.

The resumed worker compiled all five delivery modules locally (2.8--9.6 seconds
each), corrected the unshifted node signature to omit docstring text, and tried
LeanSearch for all four new nodes. That service returned Internal Server Error;
the node records retain this as unavailable alongside their existing semantic,
type-pattern, and source searches. The required dry run is rerun after these repairs.

The current worker rechecked the unchanged parent signature, the two split statements,
and the proofs of stage naturality and translated invertibility. The original hole
is reduced to two holes; no claim of an axiom-free proof or net hole reduction is made.
The current dry run compiled the delivered set and passed preflight without pushing.
The inherited second-reading section was removed: the next independent reader must
write their own review.

## Second reading by G2

1. Compared the delivered parent with the repository using `diff -u` and compared
   its theorem signature byte for byte. Verdict: unchanged signature and public
   imports; only its proof and private proof imports change. The other four modules
   are new. No definitions, existing visibility, or target statements change.
2. Compiled all five delivered modules through `lcompile.py --all`: clean, with
   times 4.2--10.3 seconds. A scratch copy with explicit helper imports and
   `#print axioms` checked all five declarations: only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The latter is expected from the two split holes and
   still-open upstream statements; these are not axiom-free target proofs. There
   are exactly two named `sorry` theorems and no forbidden constructs or data
   definitions in the delivery. Removed the scratch copy after checking.
3. Read both split statements with their docstrings and dependencies. Forward-map
   construction supplies bounded agreement without an inverse; unshifted
   invertibility assumes an already supplied family and proves no construction or
   naturality. Both are strict parts of the argument, rather than renamed copies
   of the parent. Checked zero towers, empty schemes, bounded presentations,
   nonuniform stage bounds, and the separate one-fold translation case. The sum
   model needs transport through its split finite-partial-sum telescope; full
   homotopy naturality, explicitly supplied by the proved refinement helper,
   permits those transports. Repeated semantic searches using different wording,
   a type search for coproduct comparisons, and source searches in both library
   roots. No exact existing replacement was found. Loogle confirms
   `CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂` only closes the last triangle
   step, not either full split statement. Verified the cited Stacks pages:
   [06YS](https://stacks.math.columbia.edu/tag/06YS) supplies flat K-flat models,
   and [06YJ](https://stacks.math.columbia.edu/tag/06YJ) supplies exact derived
   pullback and its K-flat computation; the supplied-normalization extension is
   explicitly recorded as an inherited agent argument. Verdict: retain this
   decomposition with both obligations open; no additional hole was closed.
4. Read the parent downward, the refinement-cancellation proof, and the translated
   invertibility proof. The parent uses bounded agreement to establish bounded
   invertibility, full naturality for propagation, and `asIso` without changing
   either required equation. The helpers use localization cancellation and
   cancellation of an invertible shift comparison, respectively. Public imports
   supply signature notions; extra imports remain private. The split modules keep
   the original plan dependencies. Checked `sk-thm-picard-duality.json` and its
   `realized` record: no unit statement or step is replaced. Verdict: route kept;
   no entire module pruned. Expanded `No longer needed` to name every replaced
   old direct proof dependency, while recording its continuing lower-level use.
5. Compared every new node's verbatim Lean signature with its module, checked the
   required creation, source, search and blueprint fields, and checked that each
   `proof_deps` is the union of its proof-step uses. The existing node changes only
   `proof`, `proof_deps`, and `proof_origin`. Verdict: consistent after two prose
   repairs: the parent now says full naturality is an input to invertibility
   propagation, and the naturality node explicitly says both refinement arrows
   are stage maps. Recorded the independent semantic searches on the two split
   nodes. No change record is required.

Changes by this second reader: dependency accounting in the report, the two DAG
proof descriptions, independent search records, and this review. Lean proofs and
statements were retained. One original hole is closed syntactically and two are
added below it: this delivery is a decomposition with net hole count -1, not a
claim of net proof progress.
