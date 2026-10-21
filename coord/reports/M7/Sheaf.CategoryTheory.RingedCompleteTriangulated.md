## What changed

Proved `CategoryTheory.ringedCompleteTriangulated` in
`Sheaf.CategoryTheory.RingedCompleteTriangulated`, with its existing statement,
universes, hypotheses, visibility, definitions and public imports unchanged.
Added the proved private helper `CategoryTheory.exact_reflector`.

The shorter route first proves that the actual local completeness predicate is
closed under isomorphisms, zero, every integer shift and distinguished-triangle
extensions. On each slice it is the vanishing of exact derived internal Hom
from localization composed with exact derived restriction. These are the existing
`ringedInternalHom_exact` and `ringedDerivedRestriction` interfaces. The former is
publicly retained by the independent-universe module now recorded on its node;
no dependency record is rebound.

The existing `ringedKoszulCompletionReflector` supplies the actual strict Koszul
presentation, complete outputs, the Hom bijection and naturality of its prescribed
unit. The private helper constructs the adjunction to the complete full
subcategory from this bijection, proves that its unit is precisely the supplied
natural transformation, and applies Mathlib's left-adjoint shift and triangulated
APIs. Transport through `liftCompιIso` proves both exactness and `CommShift` for
the original completion functor and unit. No arbitrary object is selected from
a mere existence theorem to define data. No generating-list cases are excluded,
including the empty list, and no bounds or exactness-of-products hypotheses enter.

Replaced the obsolete proof plan in the docstring and node with this argument.
Added private proof imports of `RingedInternalHomExactRestriction` and
`Mathlib.CategoryTheory.Triangulated.Adjunction`. The unit route in
`dag/units/sk-lem-integral-models.json` is unchanged; this node is not itself one
of that unit's realized steps. The new cross-unit inputs are generic exactness,
restriction and adjoint tool results. The old `tool_uses` approvals are pruned
only; no approval is added or rebound.

Validation: `lcompile.py` compiled the entire module cleanly in 40.4 seconds,
with no errors or warnings. An earlier monolithic draft exceeded the limit;
proving the generic adjunction argument as a private helper avoids expansion of
the ringed-site constructions during that argument. The helper itself was also
compiled during development. The import-direction check reports no cycle.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.ringedCompleteTriangulated`
(node `lem-sfb-ringed-complete-triangulated`).

The item contains zero remaining `sorry`. Added zero holes and zero split-off
statements. `CategoryTheory.exact_reflector` is fully proved. The theorem uses
existing stated dependencies, in particular `ringedInternalHom_exact` and
`ringedKoszulCompletionReflector`; their existing proofs are outside this packet.
This is a proof from existing declarations, not a decomposition into new holes.

## No longer needed

Removed these four ordinary proof imports:

- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`

The following former direct proof dependencies are unnecessary for this node's
new argument and were removed from its `proof_deps`:

- `def-pc-flat-sheaf-modules`
- `lem-pc-bounded-above-flat-kflat-site`
- `lem-sf-triangle-two-out-of-three`
- `lem-weil-pbc-commshift-nattrans-triangle-morphism`
- `lem-weil-pbc-kflat-fixed-tensor-triangulated`
- `lem-weil-pbc-kinjective-shift`
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`
- `lem-weil-pbc-total-tensor-integer-shifts`
- `lem-weil-tower-category-levelwise-abelian`

Their obsolete entries in this node's `tool_uses` list are removed as well;
`def-pc-flat-sheaf-modules` never had a tool approval. The proof needs neither
finite-free Koszul term calculations, tensor-cone calculations, tower evaluation
nor the K-injective unit shift calculation. The strict tower and derived limit
remain fixed by `D` and the reflector theorem. All four existing public imports
are preserved as the module's public API, including the strict-tower and
triangle-morphism reexports. No declaration or module is withdrawn, and no claim
is made that these dependencies are globally unused by other declarations.

## Where the brief, the DAG or earlier work was wrong

The old seven-step tensor/limit proof plan was longer than necessary. The
paragraph after Stacks Definition 0999 establishes the complete locus directly
from local vanishing of derived internal Hom; the exact reflector follows from
its adjunction to the triangulated inclusion (Stacks derived.tex,
`lemma-adjoint-is-exact`, in the dual form implemented by Mathlib).

The theorem's Lean statement requests an existential shift structure compatible
with its prescribed unit; it does not require a separate chain-level tensor
shift witness. The docstring now describes the actual adjunction-induced
structure. The strict presentation and the unit are unchanged.

No false statement, definition repair, consumer adaptation, target change or
new node is needed. The existing small-site reflector is used directly, as
required by the node's current repair note; its independent-universe attachment
and all declarations in the adopted source tree remain intact.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
