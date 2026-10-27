## What changed

Replaced the item's single sorry by an assembly through the full subcategory of
completed-coefficient objects whose underlying constant-coefficient complexes are
right orthogonal to all l-invertible complexes. The theorem's signature is unchanged.

The Lean proof pulls the global unit condition to X and its residue fields, uses
`pur_twist_sheaf_locally_free` for the actual root-limit line, and applies the same
completed-line completeness interface to that line and the regular unit. It proves
shift stability through the additive shift adjunction. A private categorical proof
shows that any additive right adjoint preserves the indicated orthogonality.
The exact pro-etale inverse-image adjunction applies this to constant-coefficient
derived direct image. A second private construction identifies the supplied p.Rf
with the usual total right derived functor by their universal cochain units.
The specified p.completed.iso then gives completeness of the actual source.
Full faithfulness on the complete full subcategory supplies the ambient Hom bijection.

Two new modules isolate the remaining coefficient arguments. They are independent
of the presentation, the direct image, the trace and the projective-line splitting.
The coefficient comparison treats arbitrary complete complexes; the completeness
lemma treats arbitrary locally free rank-one modules, without l invertible on the
scheme. This is a decomposition, not a fully closed proof of the coefficient theory.
No existing module other than the item, or definition or statement, is changed.

Validation: all three modules compile through lcompile.py. The final item compile
has no warnings and takes 7.7 seconds. The original theorem signature was compared
with the shared source and is unchanged; the added existing-library imports pass
import_direction.py. The existing node changes only proof, proof_deps and proof_origin.

## Proved and sorry left

Closed the existing hole in
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_completedHom_bijective`
(node `lem-sfb-diagonal-trace-completed-hom-bijection`) by a complete assembly.
The item has zero remaining holes. Its private adjunction-orthogonality lemma and
universal right-derived comparison are proved without sorry.

Added two named holes:

- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalCompleteScalarRestriction`
  (`lem-sfb-diagonal-complete-scalar-restriction`): the existing constant-completion
  equivalence transported to the actual diagonal coefficient encoding and the
  supplied localization choices, with the scalar-orthogonality criterion.
- `AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalCompletedLine_complete`
  (`lem-sfb-diagonal-completed-line-complete`): completeness of the actual completed
  Z_l regular module and descent along local rank-one trivializations, stated as
  orthogonality after the exact scalar restriction.

Thus one upper hole is closed and two genuine coefficient steps are added; the
closed-minus-added count is -1: the packet has two holes instead of one. This is a decomposition. Both holes have their
source and proof in words in their docstrings and matching new DAG nodes.

## No longer needed

The item no longer needs `prop-weil-pbc-direct-image-limits` or its module
`Sheaf.Paper.CompletedDirectImageLimits`: the additive derived inverse-image
adjunction proves preservation of completeness directly, in the constant encoding
already identified by p.completed.iso. No strict inverse-limit comparison or
perfect finite-coefficient projection formula is used for this Hom bijection.
The corresponding dependency is removed from this item's node. This does not
claim that other library consumers no longer need that module.

No existing Lean import is removed; the original file only publicly imported its
presentation. `lem-pur-twist-sheaf-locally-free` remains directly used, and
`lem-weil-pbc-constant-completion-equivalence` remains needed by the new coefficient
steps, so neither is pruned from the argument. All added proof imports are private.
No source-library declaration is removed or weakened.

## Where the brief, the DAG or earlier work was wrong

The original plan cites a general constant-completion equivalence, but its Lean
interface is on a small equal-universe site, over ring-sheaf modules and standard
localizations, with local internal-Hom completeness. The item's actual functor
also changes from constant-ring module sheaves to constant-coefficient module
sheaves and uses the supplied `DiagonalTraceLocalizations`. Its scalar-orthogonal
full-subcategory interface is therefore an additional comparison, rather than a
direct application of the existing equivalence. Similarly `completedLine_complete`
uses the completed O_E ring and a finite-field presentation of completeness;
it does not directly state completeness of the actual completed Z_l module in
the diagonal encoding. The two new statements expose precisely these remaining
coefficient interfaces. No disputed or false mathematical statement was found.

The new statements were checked on the empty scheme, the regular module, arbitrary
rank-one twists, zero test complexes and l-invertible test complexes. The scalar
comparison has no constructibility or boundedness restriction. The line result
does not assume l invertible on the scheme: that assumption is used only in the
main proof to supply Tate-line local freeness. The current blueprint paragraph (1)
and the unit route are preserved.

Tools from other units used by the new coefficient interfaces are the existing
constant-completion equivalence, flat ringed complete equivalence and the
weakly contractible sections theorem. They are coefficient/site tools, replacing
no geometric step of the diagonal unit. Their existing statements and modules
were read; maintainer tool-use approvals are left untouched.

## New nodes

`lem-sfb-diagonal-complete-scalar-restriction`, in
`lean/Sheaf/Paper/DiagonalCompleteScalarRestriction.lean`, is proof step (3) of the
original plan in the actual coefficient encoding. Its source is Stacks 099I/099L
and the trace paragraph (1). LeanSearch, LeanFinder and Mathlib grep found no exact
match; the existing project equivalence is the route for the remaining transport.

`lem-sfb-diagonal-completed-line-complete`, in
`lean/Sheaf/Paper/DiagonalCompletedLineComplete.lean`, is the rank-one coefficient
part of proof step (1). It contains no shift or direct image. Its proof uses the
regular finite quotient tower on weakly contractible pro-etale objects, local
triviality, and the principal orthogonal criterion. LeanSearch, LeanFinder and
Mathlib grep found no exact match. The source-completion criterion and the general
completed O_E line theorem were inspected to distinguish their encodings.

No change records are needed: all existing signatures and definitions are preserved.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
