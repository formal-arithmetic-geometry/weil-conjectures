## What changed

Proved `AlgebraicGeometry.syntomic_locus_base_change` in
`Sheaf.TraceFormula.SyntomicLocusBaseChange`, preserving its signature and all three
public definitions verbatim. The proof follows Stacks 02V3: compare affine fibre
stalks under residue-field extension, obtain relative complete-intersection affine
neighbourhoods from the pointwise local model, and characterize the fibre condition
on an arbitrary source open by containment in the locus.

Private proved helpers transport the bundled local-ring condition across algebra
isomorphisms, relate it to the existing regular-sequence presentation convention,
and identify the scalar maps on affine sections, stalks, tensor products and fibre
opens. The chart argument explicitly handles the zero-ring clause; no nonempty
scheme or fibre hypothesis was added.

Added private proof imports of
`WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionBaseChange`
and `WeilConjectures.RingTheory.GlobalCompleteIntersectionPrincipalLocalization`.
Updated the item's proof record to name these existing inputs. No public import,
public signature, source-library file, definition body, or consumer was changed.
The cleaned complete module compiled through `lcompile.py` in 13.3 seconds with
exit code 0. Tensor-product notation and the elaboration transparency option are
scoped to individual declarations; the interface checker reports no changes. The delivery runs its own compile and preflight checks as well.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.syntomic_locus_base_change`
(node `lem-trf-syntomic-locus-base-change`). The item now has zero `sorry`.
Holes closed: 1. Holes added: 0. Statements split off: 0.
All private helper lemmas are proved; no new modules or axioms were introduced.

The proof uses the already stated
`AlgebraicGeometry.lci_pointwise_criterion` (node `lem-trf-lci-pointwise-criterion`),
`Algebra.isCompleteIntersectionLocal_fieldChange`
(node `lem-trf-lci-field-change-local`), and
`AlgebraicGeometry.syntomic_pointwise_local_model`
(node `lem-trf-syntomic-pointwise-local-model`). Their existing holes are unchanged;
they remain separate dependency items under the stage-3 rule.

## No longer needed

Removed redundant private imports of
`WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation`,
`Mathlib.RingTheory.Extension.Presentation.Basic`, and
`WeilConjectures.RingTheory.CompleteIntersectionOverField`.
The definitions of the two source-library modules remain available through the
used inputs' public imports. The presentation API is not used directly here.

Removed `lem-weil-pbc-presentation-base-change` from this node's direct proof
inputs. Its role is supplied by the stronger, already proved
`lem-weil-pbc-relative-global-complete-intersection-base-change`; that source
module still uses the presentation API internally. This does not withdraw that
node or any source-library declaration. No whole module or unit-route step is
pruned. The remaining declared proof dependencies are used by the argument.

## Where the brief, the DAG or earlier work was wrong

The two complete-intersection local-ring encodings require a bridge, as already
noted in the stage-2 review: one bundles localness and essential finite type,
whereas the other takes them as instances, and the pointwise criterion uses an
explicit regular-sequence quotient. The private equivalences prove these bridges,
including the maximal-ideal condition from properness of a regular-sequence ideal.
No mathematical statement needed correction.

The node `lem-weil-pbc-relative-global-complete-intersection-base-change` has a
stale Lean attachment naming `Sheaf.Paper.RelativeGlobalCompleteIntersectionBaseChange`.
Its existing proved declaration is actually
`Algebra.relativeGlobalCompleteIntersection_baseChange` in
`WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionBaseChange`,
which is the module imported here. Its signature provides exactly the required
quotient equivalence and preservation of the relative presentation condition.
The item's node is updated to describe the actual proof; unrelated attachments
are unchanged.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
