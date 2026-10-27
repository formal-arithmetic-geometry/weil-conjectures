## What changed

Replaced the sole `sorry` in `Sheaf.Paper.RingedProjectionTensorExact` by a proof
from the existing K-flat fixed-tensor exactness and cochain tensor model rigidity
statements. The declaration signature and both public imports are unchanged. The
proved normalized comparison is in the new module
`Sheaf.Paper.RingedProjectionTensorModelIso`; the other helpers are private and
proved. The item's DAG proof now records this route.

Resolve the fixed derived object by a flat-term K-flat complex. Cochain rigidity
identifies the published derived tensor with the supplied `TensorModel`, normalized
on resolving pairs. Its representative comparison is exactly the one in the
K-flat exactness theorem: the quotient-to-derived comparison has identity
components. The second normalization equation of `TensorShifts` proves that the
specified representative comparison respects every integer shift. Restrict the
published fixed-factor comparison to resolving varying arguments, and cancel it
to obtain shift compatibility of the model isomorphism there. Essential
surjectivity of resolving localization and `NatTrans.CommShift.of_whiskerLeft`
give shift compatibility everywhere. Transport triangulatedness first to the
supplied model at the resolving fixed factor and then to the original derived
object using `sa.shifts`.

Sources read: Stacks `sites-cohomology.tex`, `lemma-K-flat-resolution` (06YS),
`definition-derived-tor` (06YU) and its preceding exact localization construction,
`lemma-pullback-tensor-product` (07A4); `more-algebra.tex`, `item-shift-tensor`
(0FNH). The proof uses the signed shift map in the existing tensor API. It uses
no boundedness, nonzero-coefficient, pullback or slice hypothesis.

Searches actually run with `msearch.py`: LeanFinder for a derived tensor
bifunctor normalized on K-flat representatives preserving distinguished
triangles (eight generic derived/triangulated hits); Loogle for
`CategoryTheory.Functor.IsTriangulated.of_iso` (no such identifier); grep for
`IsTriangulated.of_iso|isTriangulated_of_iso` (found the Mathlib transport lemma).
Direct source searches found the already proved cochain rigidity and K-flat
fixed-tensor theorem, and the related private published-model argument in
`ProjectionMateExact`. No new mathematical obligation is needed.

Validation: `lcompile.py --all` compiled the new model-comparison module in
23.0 seconds and the item module in 45.9 seconds, with no warnings or errors.
Both are below the unchanged 60-second limit. The original theorem statement
was compared textually with the starting file and is unchanged. There are no
profiling options or debug commands in the delivery.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.ProjectionRestriction.ringedProjectionTensorExact`
(node `lem-weil-pbc-ringed-projection-tensor-exact`), the item's one original hole.
Added: zero holes. Remaining in either delivered Lean module: zero.
The new `AlgebraicGeometry.Scheme.ProjectionRestriction.ringedProjectionTensorModelIso`
(node `lem-weil-pbc-ringed-projection-tensor-model-iso`) is proved completely;
it adds no hole and is not a split-off unfinished obligation.

## No longer needed

The direct proof dependencies
`lem-weil-pbc-resolving-representative-whiskering`
(`Sheaf.Paper.ResolvingRepresentativeWhiskering`) and
`lem-weil-pbc-derived-tensor-shift-descent`
(`Sheaf.Algebra.Homology.DerivedTensorShiftDescent`) are not used by this proof.
The proved cochain tensor model rigidity theorem supplies the normalized model
isomorphism, and the supplied second normalization equation plus essential
surjectivity proves the needed fixed-factor shift compatibility directly.
Neither of those two modules was imported in the starting file, so no existing
import was removed. These dependencies can still be needed by other consumers;
this delivery withdraws no module and changes no other node.

`lem-sf-cochain-tensor-model-rigidity` is used as a generic, already proved tool
for precisely its normalized isomorphism clause. This does not bypass any unit
statement or proof step. The tensor-colimits node is used for the published
isomorphism between sectionwise tensor-right and categorical tensor-right,
converting the resolution theorem's flatness assertion to `IsFlatOnSite`.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The DAG's full signed-shift descent theorem
is more than this fixed-factor exactness proof needs. Its normalization is
already supplied by `TensorShifts.second`, so the proof can verify compatibility
on the resolving full subcategory and reflect it along its essentially
surjective localization. The unit route and the unbounded, independent-universe
statement are preserved.


## New nodes

`lem-weil-pbc-ringed-projection-tensor-model-iso` records the proved normalized
bifunctor comparison, in `Sheaf.Paper.RingedProjectionTensorModelIso`. This is
only the model-identification step: it asserts no exactness and needs no shift
structure. Its proof applies the existing cochain rigidity theorem and proves
that its representative arrow equals the fixed K-flat theorem's
`representativeIso`. It is valid for the zero ring, empty site and unbounded
complexes because it is an unconditional specialization of that rigidity
statement. The new node's source is Stacks 06YU; its three searches were run
with `msearch.py` and recorded in the node. Blueprint search for “tensor model”
found no matching node; its blueprint ancestry follows the item's recorded
perfect-projection-formula ancestor.

The comparison was first implemented and type-checked in the item module.
Profiling found repeated elaboration and kernel comparison of the large
representative interfaces. Local irreducibility of the tensor, totalization and
localization definitions reduced unintended unfolding; the complete file still
exceeded 60 seconds. The self-contained proved comparison therefore has its own
module, following step 3a of the worker brief. The remaining exactness argument
uses it as a theorem. No time limit was increased, no shared definition was
changed, and no new `sorry` was introduced. No change record is needed.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
