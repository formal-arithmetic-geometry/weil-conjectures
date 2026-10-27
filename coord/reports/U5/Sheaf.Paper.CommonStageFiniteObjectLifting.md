## What changed

Proved `WeilConjectures.PurityCommonStageLifting.finite_object_lifting` in
`Sheaf.Paper.CommonStageFiniteObjectLifting`, preserving the elaborated theorem type,
definition and public import. Reused the object and representative specifications
of `commonStageDerivedPullback_existsUnique` for the first two conjuncts.

Constructed the exact compositum as the finite supremum of the component fields
joined with the supremum of the additional list. Mathlib proves its finite
dimensionality. Applied the assumed stagewise essential surjectivity at this
field and took the component isomorphisms. Constructed the required stage-change
isomorphisms from the specified transition identifications and unitor, using
`mkHom_comp_mkHom` and `id_eq_mkHom` to check both inverse equations. Included the
stagewise lifts into the pair categories and assembled the resulting component
isomorphisms with `Pi.isoMk` to obtain essential surjectivity.

Updated the existing node's proof, proof dependencies and proof origin to reflect
these calls, retaining the original source citation. Two proved private helpers abstract the generic representative-isomorphism
construction and its three-comparison formulas. No new modules, public
declarations, interface changes or consumer adaptations.
Explicit arguments replace inferred placeholders in the unchanged theorem type.
Local transparency settings retain the stage-system choice and normalized
comparisons behind their APIs during dependent elaboration; explicit wrapper
reductions identify the public component functors with those APIs. This packet
retains the current source, its Lean attachment and its statement dependencies.

## Proved and sorry left

Closed 1 of 1 holes: `WeilConjectures.PurityCommonStageLifting.finite_object_lifting`
(node `lem-pur-common-stage-finite-object-lifting`). Added 0 holes; 0 remain in the
item. No split-off theorems. The published pullback specification remains an
existing dependency with its own proof obligation; this is a proof from that
specification and the assumed stagewise essential surjectivity.

The empty family, empty additional list, repeated fields and identity stage
inclusions are covered by finite suprema and the same representative equations.
No nonempty-index assumption or extra extension is introduced.

## No longer needed

No existing import or module is removed. The public imports remain unchanged
because they are part of the published interface. No entire dependency module is
claimed globally pruned.

The node no longer needs `lem-pur-integral-operations-scalar-extension`,
`lem-weil-scalar-extension-composition` or `def-weil-rationalization-karoubi` as
separate proof dependencies: representative descent, scalar coherence and the
raw-stage constructions are already contained in the published pullback and
common-stage coefficient APIs. They remain statement dependencies, and their
modules remain public imports. The updated proof directly uses
`def-weil-derived-pullback-tensor-hom`,
`def-weil-algebraically-closed-coefficients` and
`def-weil-finite-subextension-directed-set`.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement change. The original DAG's explicit scalar
coherence calculations are unnecessary here because the actual pullback functor
already comes with the exact representative specification. The unit route stays
unchanged. The current item source is present and is preserved, not withdrawn.
The initial sandbox packet did not compile, despite its draft report: stage-system unfolding
and implicit wrapper conversions required elaboration repairs before delivery.

Validation: the complete proof compiled through lcompile.py in 12.1 seconds.
The generic private helper for the three-comparison formula avoids the expensive
coefficient-specific kernel conversion. The final delivery reruns compilation
and preflight after removing diagnostic traces.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
