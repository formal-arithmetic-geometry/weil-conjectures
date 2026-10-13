## What changed

Proved `AlgebraicGeometry.Scheme.hom_eq_of_finite_depth_two` in
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoFiniteHomEquality`, with its existing
signature and visibility unchanged. Added only proof imports:
`Sheaf.AlgebraicGeometry.Morphisms.DepthOneRestrictionInjective`,
`Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec`,
and `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.

Three proved private helpers handle invariance of depth under linear equivalence,
the linear equivalence between the structure-module stalk and the local ring, and
injectivity of structure-sheaf restriction. The main proof constructs the two
morphisms in the category of affine schemes over L. For every base open V,
`appLE_comp_appLE` turns equality on the source open into equality after composing
with its injective restriction map. Pointwise cancellation gives equality of
algebra-map components; faithfulness of the affine anti-equivalence gives f = g.
Updated the node's proof, proof_deps, and proof_origin to this shorter route.

Read Stacks Tags [0B3M](https://stacks.math.columbia.edu/tag/0B3M) and
[01SA](https://stacks.math.columbia.edu/tag/01SA). Positive depth excludes associated
boundary points, so 0B3M applies to the structure module; 01SA supplies the affine
anti-equivalence. Local source files for those tags were absent on this machine,
so the original Stacks pages were read. Searches via msearch.py (LeanFinder,
Loogle, grep), plus project/source searches, found no direct theorem without a
reducedness hypothesis. Mathlib's dominant-source extensionality requires a reduced
source, which the present statement does not assume.

The source is locally Noetherian because r is finite. The proof transports the
actual finite self-module of each local ring to the structure-module stalk, and
uses the bound 1 ≤ 2 ≤ depth. Neither target depth nor nontriviality is assumed.
The empty-open case is included: the restriction map is still injective and can
be cancelled. For U = top, the same argument applies. Empty schemes require no
special witness or exception. The unit structure module is finite on every affine
open. No data is chosen from an unproved existence statement; the only chosen
anti-equivalence comes from its defining full categorical specification, and is
used in a theorem proof.

## Proved and sorry left

Closed the single hole in
`AlgebraicGeometry.Scheme.hom_eq_of_finite_depth_two`
(node `lem-sbc-depth-two-finite-hom-equality`).
No sorry remains in the delivered module. No holes or new modules were added.
This closes its local proof hole using existing library declarations; the theorem
is not yet axiom-free because imported dependencies still contain proof holes.
The three private helpers are fully proved. This is a proof from existing library
declarations, not a decomposition into newly holed statements. Single-file
lcompile.py compilation succeeds without errors or warnings.

## No longer needed

Removed the trial proof import `Mathlib.RingTheory.Finiteness.Basic` after
confirming compilation without it. No original imports were removed: the original three public imports support the
unchanged statement. The planned proof dependency
`lem-sbc-depth-two-hartogs-restriction` and its module
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction` are not needed by
this item. This also avoids its surjectivity branch, including
`lem-sbc-depth-two-restriction-boundary-surjective` /
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoRestrictionBoundarySurjective` and
`lem-sbc-depth-two-affine-finite-quotient-depth` /
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoAffineFiniteQuotientDepth`.
The planned finite-local-algebra depth transfer (Tag 0AUK) is not used, nor is
`Sheaf.AlgebraicGeometry.Morphisms.FiniteStructureAlgebraDepth` needed here.
These are pruned from this proof only; other callers may still need them.
The positive-depth injectivity branch and the affine relative-spec node are retained.
The unit `sk-prop-input-spreading` has empty realized statement/step lists, and
none of its prescribed steps is bypassed by this local simplification.

## Where the brief, the DAG or earlier work was wrong

The statement is correct and unchanged. The original plan's finite-algebra depth
transfer and depth-two Hartogs isomorphism were stronger machinery than equality
needs. Restriction injectivity directly on F suffices, using only depth one.
The existing docstring and DAG proof have been adjusted to describe the compiled
argument. No interface changes, forced adaptations, disputed statements, or new
nodes are involved.


## Second reading by H2

1. Compared the complete delivered module and node with the repository versions.
   The existing theorem signature is byte for byte unchanged, including every
   hypothesis, conclusion, universe and visibility. No definition or other
   existing declaration changed. The added private helpers are proved theorems.
   Verdict: pass; no interface change record is needed.
2. Independently compiled the module with lcompile.py: clean, about six seconds.
   Scanned for sorry and forbidden declarations: none in the delivered module.
   A scratch-copy #print axioms check gives only propext, Classical.choice and
   Quot.sound for depth_eq_of_linearEquiv and structure_stalk_linearEquiv.
   structure_restriction_injective and hom_eq_of_finite_depth_two additionally
   depend on sorryAx through existing imported library proofs (the injectivity
   branch still reaches AffineSectionAssociatedStalk). No new axiom or hole is
   introduced. Verdict: pass as a local hole closure, conditional on existing
   library dependencies; not a completed axiom-free target proof.
3. No statements were split off and no new public statements or nodes were added.
   Read all three private helpers: ideal-smul and regular-sequence invariance
   justify depth transport, the stalk equivalence uses the actual filtered
   colimit comparison and proves linearity on germs, and the structure module
   satisfies the finite-section hypotheses. Checked the empty source, empty
   open and full open cases: no nonempty or nontrivial witness is assumed.
   The main proof chooses an equivalence only inside a theorem proof and uses
   its specified section maps; it constructs no arbitrary data definition.
   Verdict: pass.
4. Checked the source-level route and searched independently with Loogle and
   grep for scheme-hom injectivity, stalk-unit equivalences and depth invariance.
   Mathlib's dominant-source equality lemmas require IsReduced, which this
   statement does not assume. No applicable shorter theorem was found. Each
   added import was removed in a separate scratch copy; each removal fails
   compilation at exactly the declaration it supplies. Original public imports
   support the unchanged signature. The old sole non-affine proof dependency,
   DepthTwoHartogsRestriction, is fully listed under No longer needed. Read
   sk-prop-input-spreading and its realized record: this is a simplification
   within its depth-two uniqueness input, retaining the chapter/unit route.
   Verdict: pass.
5. Compared the node's proof steps, proof_deps and proof_origin with the Lean.
   They record positive-depth restriction injectivity, depth transport and
   affine relative-spec faithfulness, and omit the unused Hartogs-surjectivity
   route. The Lean record's statement agrees with the unchanged signature.
   Verdict: pass.

Second reading changed only this report: added the five-point independent review
and clarified that the local hole closure still depends on existing sorryAx.
The Lean proof and DAG update required no repair.
