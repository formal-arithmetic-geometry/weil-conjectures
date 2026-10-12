## What changed

Replaced the sole sorry in `AlgebraicGeometry.Scheme.exists_finiteEtale_completion_stage`
with a complete Lean reduction. The original signature and public imports are unchanged.
The proof first lifts V over the completion, then descends that cover to a finitely
presented A-algebra, takes k = j ≫ l, proves both projections, and composes the two
isomorphisms using `Over.pullbackComp` and `Functor.mapIso`.

Added `Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift`. Its theorem
`AlgebraicGeometry.Scheme.exists_finiteEtale_completion_lift` is proved from the existing
complete-case lifting theorem and completion Noetherianity. The proof takes J to be the
kernel of the completion projection, identifies J with IB, constructs B/J ≅ A/I by the
surjective first isomorphism theorem, and identifies the closed fibres by a pullback map
and `pullbackLeftPullbackSndIso`. It transports V, applies complete-case lifting, and
pulls the resulting isomorphism back. Both projections are proved explicitly.

Added `Sheaf.AlgebraicGeometry.FiniteEtaleAlgebraStage`, with the remaining general
algebra-stage descent statement. This is strictly the descent portion of the original
argument: its input is a cover over Y_B for an arbitrary A-algebra B; it mentions neither
an ideal nor a closed-fibre cover. The main proof supplies that input using the proved
completion-lifting lemma and performs the closed-fibre comparison itself.

All three modules compile together without errors or warnings using lcompile.py --all.
The declarations depend transitively on existing project sorries; this is a stage-3
reduction, not a claim that the complete dependency closure is axiom-free.

## Proved and sorry left

Proved (no sorry in either body):
- `AlgebraicGeometry.Scheme.exists_finiteEtale_completion_stage`
  (lem-weil-pbc-finite-etale-completion-stage).
- `AlgebraicGeometry.Scheme.exists_finiteEtale_completion_lift`
  (lem-weil-pbc-finite-etale-completion-lift).

Exactly one delivery theorem remains sorry:
- `AlgebraicGeometry.Scheme.exists_finiteEtale_algebra_stage`
  (lem-weil-pbc-finite-etale-algebra-stage), in its own new module. Its body is exactly
  `:= by sorry`. Its docstring and node give the finite-subalgebra limit construction,
  spreading out, separate finiteness and étaleness descent, common enlargement, and
  projection-compatible isomorphism. These are original plan steps 3 and 4 plus their
  base-change identification, not a restatement of the item.

The remaining statement was checked on the empty cover, zero algebra, and the nonempty
indexing system (including the empty finite subset). Completion lifting also works for
I = top: its closed fibre is empty. No nontriviality or henselian assumption was added.

## No longer needed

Removed direct proof imports from the item:
- `Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete`.
- `Sheaf.AlgebraicGeometry.DescendFinite`.
- `Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`.
- `Sheaf.RingTheory.AdicCompletionNoetherian`.
- `Mathlib.RingTheory.AdicCompletion.LocalRing`.
- `Mathlib.RingTheory.AdicCompletion.Completeness`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`.

These are factoring, not mathematical pruning: complete-case lifting, Noetherianity and
completion facts are used in the proved completion-lifting module. The finite/étale
stage-descent nodes, Spec-colimit and scheme-over-limit nodes, spreading-out node, and
property/convention nodes of original steps 3–4 remain in the plan of the algebra-stage
node. No original mathematical node or module has been shown unnecessary for the target
closure. No unit statement or realized step is bypassed. The item's immediate proof_deps
are now the two intermediate nodes and def-pc-fibre-product.

The remaining theorem's module imports only what its statement uses. Its intended proof
imports belong to the next worker; no unused proof imports were kept there.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox held only the unchanged source theorem, with no proof or report.

The record of thm-pd-spreading-out lists `exists_pullback_hom_of_isLimit` (Tag 01ZM part 2)
and the equality-descent declaration (part 3), whereas original step 4 needs part 1.
The same source module does provide `Scheme.exists_isPullback_of_finitePresentation`,
which is the correct declaration for that step. No dependency statement needs changing.

The local clone has literature lists but no downloaded `literature/stacks-project/pione.tex`.
I read the primary source online: [0GS2](https://stacks.math.columbia.edu/tag/0GS2),
[01ZM](https://stacks.math.columbia.edu/tag/01ZM),
[01ZO](https://stacks.math.columbia.edu/tag/01ZO), and
[07RP](https://stacks.math.columbia.edu/tag/07RP).
The new general-algebra statement is the finite-stage descent argument of 0GS2,
applied to an arbitrary algebra via these limit lemmas. The completion-specific and
henselian approximation steps are separate; neither is hidden in that remaining theorem.

Searches: LeanFinder returned finite-presentation algebra and ring base-change facts;
Loogle returned the completion projection identities and kernel identification used above;
grep of Mathlib, both library roots and the DAG found no direct theorem matching the
arbitrary-algebra stage statement. LeanSearch returned Internal Server Error; this
unavailability is recorded without treating it as evidence of absence.

## New nodes

`lem-weil-pbc-finite-etale-completion-lift` realizes original steps 1–2. Its new module
contains a complete Lean proof from the existing complete-case lifting theorem,
completion Noetherianity, and Mathlib pullback/completion machinery.

`lem-weil-pbc-finite-etale-algebra-stage` realizes original steps 3–4 for an arbitrary
A-algebra B, with the two stage-map projections and an isomorphism over Y_B. This is
the single new sorry obligation. Its dependencies preserve the original descent route.

Updated the original node's proof, proof_deps and proof_origin to match the implemented
composition. No definitions, existing statements, target signatures, or change records
were changed.

## Second reading by Q2

I checked the item and both new nodes against the repository declarations. The original
completion-stage theorem has the same signature and its proof compiles without `sorry`;
the completion-lift proof also compiles without `sorry`. The algebra-stage theorem is a
strictly intermediate descent statement, with no weakened hypotheses or altered target,
and its one remaining `sorry` is named and documented with node
`lem-weil-pbc-finite-etale-algebra-stage`. The completion-lift construction is valid in
the edge cases I = top, the empty cover, and the zero algebra. Imports used by proofs
are private where appropriate, and the completion-stage route still passes through the
unit's completion, descent, and pullback steps. The DAG proof and proof dependencies
match the Lean proof; the only remaining open obligation is the explicitly split
algebra-stage node.
