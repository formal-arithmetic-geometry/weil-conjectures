## What changed

Repair of the returned delivery a897b28b025. The return said that the item had
been quarantined after its previous base and required restoration from quarantine.
At this repair's start, current sheaf-dag already contained the restored module,
its quarantine file and rework row were absent, and the claim was still held by M7.
The restored module has a new coherence-based interface. The retained sandbox
has been ported to that interface, rather than repushed against the old base.

The current public import `Sheaf.Paper.SemilinearTensorCoherence`, the complete
`WeilConjectures.SemilinearSections.SystemCartesianHomEvaluation` structure and
the signature of `WeilConjectures.SemilinearSections.systemCartesianHomEvaluation_nonempty`
are preserved. The old sandbox's public theorem is not reintroduced. The current
theorem is proved by constructing the existing structure with its two fields.
The parent node was rebuilt from the current node, changing only its proof,
proof dependencies and proof origin. Current source, statement, Lean attachment,
blueprint and review metadata are preserved.

The private `evaluation_isRightAdjoint` transports the proved derived singleton
adjunction through the strict-system/sequence-site equivalence and the exact-functor
compositor. The structural ring-map identification is proved on sections. This uses
`SystemSingleDerivedExtension`, `SystemEvaluationTopos`, and the source library's
proved derived equivalence API, with no new existence hypothesis or hole.

The private `closed_evaluation_of_projection` proves the abstract argument.
It curries the fixed inverse tensor comparison, takes its inverse mate along the
evaluation adjunction, identifies that map with the unit-defined projection, and
uses Mathlib's `iterated_mateEquiv_conjugateEquiv` and `conjugateEquiv_iso` to prove
that its closed mate is invertible. `mateEquiv_counit` supplies the exact evaluation
equality on the whole derived category. Apply it using the supplied scalar and
tensor coherence fields for every M, hM and n, then assemble the isomorphisms and
the proved equations into the existing structure. The evaluation equation uniquely
determines each comparison by the tensor-Hom adjunction; no arbitrary unnormalized
object is selected from an unproved mere existence statement.

The geometric projection formula remains in the new module
`Sheaf.Paper.SemilinearCartesianProjection`, with one named theorem,
a source argument and its own DAG node. This is the projection step of the
original plan: invertibility of a specified tensor projection map, with no
internal-Hom comparison in its conclusion. The left adjoint and the formal
passage from projection to Hom are proved in the parent.

Source reading and searches from the retained proof work remain applicable:
Zheng Construction 4.1 (printed p.21), Lemma 4.10 (pp.23-24), and Proposition
4.17(a) and its proof (pp.25-26); LeanFinder, Loogle, LeanSearch and ripgrep.
The generic mate results are in Mathlib; no existing arbitrary-ring cartesian
projection result was found. `ClosedScalarHomComparison` has the wrong variance.

## Proved and sorry left

Closed the body hole of
`WeilConjectures.SemilinearSections.systemCartesianHomEvaluation_nonempty`
(node `lem-coef-semilinear-cartesian-hom-evaluation`) by a complete Lean reduction.
Both private helpers are proved. The supplied structure and its field types stay
unchanged; its fields contain no holes.

Added one named hole:
`WeilConjectures.SemilinearSections.semilinearCartesianProjection`
(node `lem-coef-semilinear-cartesian-projection`). Its proof is exactly `by sorry`.
There is no other sorry in the delivered modules. This is a decomposition:
one upper hole closed, one strictly smaller geometric projection obligation
added, net zero holes among the delivered declarations, not a completed proof
of the whole mathematical result.

Static checks preserve the current structure and theorem signature byte for byte,
verify every Lean line is at most 100 characters, verify proof-dependency lists
are the unions of proof-step uses, and check that the revised DAG is acyclic
through all 630 nodes below the parent.
The repair's `lcompile.py --all` run compiled the projection module in 7.6 seconds
and the parent in 14.7 seconds, without errors or warnings. The compiler supplied
the current scalar and tensor coherence dependencies in its private overlay.

The projection statement permits any left adjunction but specifies its actual
unit-defined map. Uniqueness of the unit-compatible adjoint comparison transports
the formula. Mathematical edge cases checked: n = 0, zero rings, zero P or M,
and the empty site. Cartesianness is essential: with a constant nonzero field
tower, n = 1, P the field, M_0 = 0 and M_q the field for q at least 1,
the projection at q = 0 is the map from the field to zero. This system fails
the required invertibility of the reduction from level 1 to level 0.

## No longer needed

No current public import is removed, no module is withdrawn, and no quarantine
archive is deleted or listed in deleted.txt. The current coherence interface and
its consumers are preserved without adaptation.

The parent no longer directly needs these nodes from the current proof plan:
`def-pc-cochain-complex-modules`, `lem-galois-yoneda-fully-faithful`,
`lem-pc-derived-adjoint-functors`, `lem-pc-kflat-resolution`,
`lem-pur-derived-change-of-rings`, `lem-pur-left-derived-from-kflat-class`,
`lem-sfb-ringed-derived-monoidal-comparisons`,
`lem-weil-pbc-exact-functor-derived-factorization`,
`lem-weil-pbc-exact-functor-derived-functor`,
`lem-weil-pbc-ringed-topoi-module-adjunction`,
`lem-weil-pbc-ringed-topos-kflat-pullback`, and
`lem-weil-pbc-site-derived-tensor-descent`.
The existing singleton extension supplies the adjunction; Mathlib's mate calculus
supplies the natural Hom comparison and counit equation. Some listed nodes remain
transitively needed by the singleton construction or the new projection lemma;
no globally pruned module or net proof gain is claimed.

The retained natural-bijection node is a Mathlib leaf whose match includes
`Adjunction.homEquiv_counit`, used to identify the projection component.
The proof-only imports added are `SemilinearCartesianProjection`,
`SystemSingleDerivedExtension`, `SystemEvaluationTopos`, and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.

## Where the brief, the DAG or earlier work was wrong

The return's quarantine condition has already been resolved on the current
branch. Its replacement interface must be respected: the previous sandbox
would have removed the current structure and broken its consumers. This repair
keeps that structure, its nonempty theorem and public import, and ports the proof
to use `SystemScalarCoherence` and `SystemTensorCoherence` directly. No manual
claim command was run: the live claim is already M7, and there is no current
rework row or quarantine file for this module to claim or copy.

The projection is defined using the adjunction unit and inverse transposition;
its uncurried formula also uses the counit. The parent docstring now says
"adjunction unit" for its construction. Existing singleton and sequence-site
infrastructure avoids deriving the evaluation adjunction a second time.

The strict-system tools belong to `sk-def-sf-operations`; their use supplies
ordinary-derived foundations without bypassing a unit statement or proof step.
The item's `sk-prop-sf-biduality-general` realized lists remain unchanged.
No tool approvals were added or edited.

## New nodes

`lem-coef-semilinear-cartesian-projection` records the geometric tensor projection
step, with the same site and coefficient universes, normalized scalar models and
representative tensor comparisons used by the current coherence interface.
It neither supplies the evaluation left adjoint nor asserts a Hom comparison.
The parent proves the adjoint construction, the mate argument and the structure
assembly. No existing signature, definition, consumer or source-library declaration
changed, so no change record or forced adaptation is required.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
