## What changed

Proved `AlgebraicGeometry.exists_isFinite_morphismRestrict_baseChange_affine_open`
without changing its signature. Its only new import is the proof-only
`Sheaf.AlgebraicGeometry.DescendFiniteAffineBasePiece`. Relative to the current
repository, the item's proof-only imports of `LimitAffineTransition` and
`FiniteMapColimitDescent` are removed; ring descent is now imported by the new
affine-piece module instead.

The proof constructs affine neighbourhoods subordinate to affine base opens,
extracts a finite subcover using compactness of the original affine open, descends
finiteness separately on those pieces, takes a common upper bound, and glues.
The original theorem's requirement that every later stage work is proved: private
helpers construct the base-change comparison square, restrict it, and use stability
of finiteness under base change. Another proved private helper glues restrictions
over a cover of an arbitrary open, including the empty cover.

Added `DescendFiniteAffineBasePiece`, proved from the existing
`RingHom.exists_finite_tensorProductMap_of_colimit` and a new geometric
`AffineBasePieceTensorPresentation` lemma. The latter is the remaining work. It
supplies a diagram of coordinate rings, a finite type algebra map, and actual
arrow isomorphisms at the limit and all upper-tail stages. It assumes no finiteness
at the limit and asserts no finite stage, so it separates geometric comparison
from algebraic descent. The affine-piece proof transports finiteness across these
isomorphisms and applies the existing ring-colimit theorem.

All three modules compile cleanly with the prescribed local compiler. Sources read:
[Stacks 01ZO](https://stacks.math.columbia.edu/tag/01ZO),
[07RG](https://stacks.math.columbia.edu/tag/07RG),
[01YX](https://stacks.math.columbia.edu/tag/01YX), and
[01YW](https://stacks.math.columbia.edu/tag/01YW).

## Proved and sorry left

Proved the item's one original sorry:
`AlgebraicGeometry.exists_isFinite_morphismRestrict_baseChange_affine_open`
(node `lem-weil-pbc-descend-finite-affine-open`).

Also proved the new theorem
`AlgebraicGeometry.exists_isFinite_morphismRestrict_baseChange_affine_base_piece`
(node `lem-weil-pbc-descend-finite-affine-base-piece`) and the private helpers
`over_pullback_square`, `finite_restrict_baseChange_comp`, and
`isFinite_morphismRestrict_of_cover`.

The delivery leaves exactly one new sorry:
`AlgebraicGeometry.exists_affine_base_piece_tensor_presentation`
(node `lem-weil-pbc-affine-base-piece-tensor-presentation`). Its entire proof is
`by sorry`, with a complete construction in its docstring and DAG proof.

The existing imported theorem
`RingHom.exists_finite_tensorProductMap_of_colimit`
(node `lem-weil-pbc-colimit-finite-ring-map`) remains an upstream proof obligation;
it is used directly and is not copied or restated here.

Edge cases checked in the argument: the finite subcover may be empty, and the
common upper bound still exists because `k` witnesses nonemptiness of `I`;
locality proves finiteness over the empty open. The geometric statement allows
zero rings, empty source or target opens, a singleton index, and a directed
preorder without antisymmetry. No quasi-compactness or quasi-separatedness of
the original base, source, or target is added. No target or existing definition
was changed.

## No longer needed

Removed from the item's module the proof-only imports
`Sheaf.AlgebraicGeometry.LimitAffineTransition` and
`Sheaf.RingTheory.FiniteMapColimitDescent`. The latter remains imported by
`DescendFiniteAffineBasePiece`; the former's mathematical facts remain in the
geometric presentation node's proof plan. Neither module is claimed globally
unreachable from the targets.

The parent's direct proof dependencies are now the affine-open and affine
quasi-compactness facts, finite locality and permanence, the one-stage affine-piece
lemma, pullback pasting, the fibre-product notion, and the finite-morphism notion. Its former affine permanence, local finite
type base change, open fibre products, affine spectra, morphisms into affines,
affine-pairs criterion, colimits, affine-transition limits, Spec-colimit limits,
and finite-ring-map descent dependencies are accounted for in the two new nodes.
`def-weil-pbc-scheme-conventions` is no longer cited directly: it introduces no declaration
or separate mathematical obligation. There are no newly unreachable proof modules
to prune on the basis of this delivery.

For an exact accounting, the following old direct `proof_deps` are absent from
the parent's new direct dependency list. All except the conventions node are
still cited by the two new nodes, directly or through their stated dependencies:

- `pqf-def-affine-morphism`
- `lem-weil-pbc-affine-open-spec-points`
- `lem-weil-pbc-affine-morphism-permanence`
- `lem-weil-pbc-lft-base-change`
- `lem-weil-pbc-open-fibre-product`
- `lem-weil-pbc-morphism-into-affine-scheme`
- `lem-weil-pbc-lft-affine-pairs`
- `def-weil-pbc-category-colimit`
- `lem-weil-pbc-limit-affine-transition`
- `lem-weil-pbc-spec-colimit-limit`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-colimit-finite-ring-map`
- `def-weil-pbc-scheme-conventions`

## Where the brief, the DAG or earlier work was wrong

The original module did not yet import its planned proof dependencies. Their
signatures were read before adding new statements. The ring descent lemma supplies
one finite stage, which suffices: persistence at all later stages is proved here
from Mathlib pullback and base-change APIs. The existing dependencies provide the
individual affine and limit facts, but no declaration provides their simultaneous
tensor-product arrow presentation for this restricted family; that geometric
combination is the split-off obligation.

LeanSearch returned Internal Server Error on both attempts and is recorded as
unavailable. LeanFinder/Loogle and source grep found the component facts, not the
whole comparison or descent result. Blueprint searches for `01ZO`,
`tensor presentation`, and `affine base` found no duplicate of either new node.
The unit's realized statements and steps are unchanged. The final DAG check also
adds the existing Mathlib leaves `lem-weil-pbc-affine-scheme-qcqs` and
`lem-weil-pbc-finite-morphism-permanence`, explicitly accounting for compactness
and base-change stability used in the outer proof.

## New nodes

`lem-weil-pbc-descend-finite-affine-base-piece`, in
`Sheaf.AlgebraicGeometry.DescendFiniteAffineBasePiece`, states finiteness at one
stage for an affine target open mapping into one affine base open. It is proved
from the geometric presentation and the existing finite-ring-map colimit descent
lemma. This node carries the algebraic descent part of the original plan.

`lem-weil-pbc-affine-base-piece-tensor-presentation`, in
`Sheaf.AlgebraicGeometry.AffineBasePieceTensorPresentation`, states a simultaneous
Spec tensor-product presentation of the limit restriction and every stage above
`k`, for one finite type algebra map. It contains the sole new sorry. The node
spells out the affine upper-tail ring diagram, the limit comparison, construction
of the algebra map, and compatibility of the stage and limit arrow isomorphisms.
It carries the geometric part of original steps 1, 3, and 4.

Both nodes inherit the parent's chapter and unit and retain the original route.
There are no change records because no existing statement, definition, or public
import was changed.

## Second reading by U1

1. Compared every delivered module with the repository. Only
   `DescendFiniteAffineOpen` already exists there; its theorem signature and
   docstring are byte for byte unchanged. The other two modules are new.
   The existing public imports are unchanged, and both added Sheaf imports are
   proof-only. There are no changed definitions or undeclared statement changes.
   Verdict: pass.

2. Compiled the three modules in import order through `lcompile.py`: all passed
   without warnings, in 3.6, 4.3, and 3.9 seconds. Appended `#print axioms` to
   temporary copies and compiled all six declarations, including the three
   private helpers. The helpers use only `propext`, `Classical.choice`, and
   `Quot.sound`; the three public theorems additionally use `sorryAx`, accounted
   for by the named geometric obligation and the imported ring-descent theorem.
   There is exactly one delivered `sorry`, the entire proof of
   `exists_affine_base_piece_tensor_presentation`. No forbidden declaration,
   hollow definition, or overlong Lean line was found. Removed the probe copies.
   Verdict: pass with the explicitly reported open obligations.

3. Read Stacks [01ZO](https://stacks.math.columbia.edu/tag/01ZO),
   [07RG](https://stacks.math.columbia.edu/tag/07RG),
   [01YX](https://stacks.math.columbia.edu/tag/01YX), and
   [01YW](https://stacks.math.columbia.edu/tag/01YW), and matched both new
   statements against the affine calculation, hypothesis by hypothesis. In the
   geometric construction, affine transitions make the inverse images of both
   `V` and `W` at `k` affine; `haffine` makes the source affine. Local finite
   type gives the finite type ring map, without requiring finite presentation.
   The upper tail has the same limit: extend any cone on the tail to an index
   by choosing an upper bound with `k`; a further common upper bound makes the
   extension independent of the choice. Open-limit restriction then gives the
   limit base piece, and the Spec-colimit comparison and pullback projections
   give the asserted tensor-map arrows. Thus the docstring construction is a
   proof of the geometric statement, with no hidden qcqs hypothesis.

   Checked the singleton-index case (ordinary affine fibre products), empty
   `V` (zero target and source rings), empty `W` (forces empty `V`), empty source
   (zero source ring), and equivalent indices in a directed preorder (thinness
   makes the chosen comparison morphisms agree). Nothing excludes these cases.
   The geometric statement contains neither the finiteness hypothesis nor a
   finite-stage conclusion. The affine-piece theorem then genuinely uses 07RG;
   neither is a sorry restatement of the item. Repeated LeanFinder with
   "Coordinate rings of pullbacks of affine schemes along a filtered inverse
   system; Spec tensor product comparison and limit global sections", Loogle
   with `AlgebraicGeometry.pullbackSpecIso`, and source/DAG searches for
   `01ZO`, `07RG`, tensor presentations, and finite base-change limits. Found
   the existing component comparisons and descent theorem, but no duplicate
   simultaneous presentation. Closing the geometric construction requires the
   full diagram/limit and arrow comparison formalization, not a short repair.
   Verdict: pass; retain the one geometric split-off obligation.

4. Read the outer proof from the target downward. The basis and compactness
   arguments give a finite subordinate cover; restriction supplies each local
   finiteness hypothesis. The affine-piece proof uses the existing ring descent
   theorem directly. Pullback cancellation and open restriction prove
   persistence, and directedness and target locality finish the proof. The
   empty-cover branch is included because `k` supplies a nonempty index type.
   Found no shorter existing theorem with the same hypotheses. Imports expose
   the types used in the statements; the new geometric and ring-descent imports
   used only by proofs are plain imports. Checked `dag/units/sk-thm-p1.json`:
   none of its `realized` statements or steps is replaced or bypassed. Corrected
   the pruning report against the current repository and listed every old
   direct dependency absent from the new parent list. No module is asserted
   globally pruned without a target-closure check. Verdict: pass after repair.

5. Checked all three nodes' verbatim Lean signatures, proof steps, dependency
   unions, origins, chapter/unit, and the new-node creation, source, search,
   blueprint, and Lean records. Read the cited affine, limit, tensor-product,
   finite-locality, and permanence statements. Found one citation mismatch:
   the parent's first step used `lem-weil-pbc-affine-open-spec-points`, which
   identifies points of an already affine open, for existence of subordinate
   affine neighbourhoods. Replaced that proof citation and its `proof_deps`
   entry with the existing Mathlib leaf `lem-weil-pbc-affine-opens-basis`, whose
   statement gives precisely `exists_isAffineOpen_mem_and_subset`. The remaining
   steps take exactly the affine/limit, finite-Spec, colimit-descent, pullback,
   and locality facts their cited statements provide. Verdict: pass after repair.

Changed the parent's affine-basis DAG citation and corrected/expanded the
pruning report. No Lean proof, signature, definition, or public import was
changed by this second reading.
