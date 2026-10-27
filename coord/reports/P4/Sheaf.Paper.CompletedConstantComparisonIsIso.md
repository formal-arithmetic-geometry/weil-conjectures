## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.completedConstantComparisonMap_isIso` by a complete
finite-presentation argument, with its original statement and public import unchanged.
The comparison is the already constructed map, not a newly chosen isomorphism.

Added `Sheaf.Paper.CompletedConstantCompletionFunctor`: the actual quotient-tower
functor, its inverse-limit functor, their additivity, the scalar-realization functor,
preservation of finite colimits by realization, and the natural transformation whose
components are the fixed comparison maps. Quotient induction proves tower
functoriality and additivity; finite-projection naturality proves naturality of the
comparison. The existing ordinary coefficient adjunction proves right exactness on
the scalar-realization side. No new data is chosen from an unproved existence theorem.

The private finite-free argument is fully proved: coordinate projections p_i and
inclusions q_i have sum p_i q_i = id. The sum of G(p_i), the rank-one inverse, and
F(q_i) gives an explicit inverse on every finite free module. No positivity of the
rank is required. A finite free presentation of N then realizes N as a cokernel;
Mathlib's `isIso_app_coconePt_of_preservesColimit` transfers invertibility from its
two free vertices to N.

Added two strictly smaller pending statements, in separate modules:
`CompletedConstantRankOneComparison` fixes the single module C itself, and
`CompletedConstantCompletionRightExact` states an intrinsic cokernel-preservation
property of the completed-quotient functor, without any coefficient morphism phi or
comparison map. The argument combining them, including extension from rank one to
all finite free modules, is actual Lean and contains no sorry.

Validation: `lcompile.py --all` compiled all four files without diagnostics. Latest
per-file times were 4.5, 4.3, 6.5 and 8.0 seconds. No existing module other than the
item is changed; no shared signature, definition, instance or public import changes.
The source-library tree is untouched.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.completedConstantComparisonMap_isIso`
(node `lem-weil-pbc-completed-constant-comparison-is-iso`). There are zero sorries
in the item module and zero in `CompletedConstantCompletionFunctor`.

Added exactly two holes:

- `AlgebraicGeometry.Scheme.completedConstantComparisonMap_rankOne_isIso`, node
  `lem-weil-pbc-completed-constant-rank-one-comparison`.
- `AlgebraicGeometry.Scheme.CompletedConstantPresentation.completion_preservesCokernel`,
  node `lem-weil-pbc-completed-constant-completion-right-exact`.

This is a decomposition: one upper hole closed, two lower holes added (net -1).
It is not claimed as a proof without remaining obligations. Each new hole is a
public theorem with body exactly `:= by sorry`, source, full proof in words,
edge-case discussion and a matching node. The other new declarations are proved
or genuine constructions.

## No longer needed

No existing library module or node is pruned, and no original import is removed.

The former direct proof dependencies
`lem-weil-pbc-adic-completion-mod-power`,
`lem-weil-pbc-constant-module-section-properties`, and
`lem-weil-pbc-limit-flat-modules` are still needed by the two pending steps.
Their edges move below those steps; they are not claimed as unnecessary mathematics.
The original projection-map construction remains a statement dependency and is
used through the new natural-comparison interface. No adopted source declaration
is removed or weakened, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The previous proof plan suppresses two interfaces
that its existing declarations do not directly state: intrinsic right exactness of
the actual completed-constant quotient functor on finite modules, and identification
of its rank-one comparison with the scalar-extension unit calculation. These are
now separate precise tasks, rather than another renaming of the original finite-
module invertibility obligation.

The new route uses the finite-presentation argument of Stacks Tag 093K at the level
of a natural transformation. Tag 0912 and constant-section calculations remain in
the intrinsic right-exactness step. Searches found ordinary completion equivalences
and `ModuleCat.isIso_app_of_rankOne` for functors preserving arbitrary colimits;
the latter does not apply because completion only preserves the relevant finite-
module cokernels. We therefore proved the required finite-free argument directly.
The already proved parent finite-module comparison cannot be imported here because
it depends on this item.

The unit route in `sk-thm-properbasechange` is preserved. The ordinary coefficient
adjunction (`lem-pur-sheaf-ring-coefficient-ordinary-adjunction`) is used as a generic
tool solely for preservation of finite colimits by scalar extension and restriction;
it supplies no proper-base-change or finite-module comparison assertion.

## New nodes

`def-weil-pbc-completed-constant-completion-functor` records the constructed additive
quotient-tower and completion functors, the right-exact scalar realization, and the
proved natural comparison. Its module has no holes.

`lem-weil-pbc-completed-constant-rank-one-comparison` isolates only the free rank-one
normalization. Its proof uses evaluation quotient isomorphisms and scalar-extension
of the unit; it requires neither finite presentation of an arbitrary module nor
right exactness of completion.

`lem-weil-pbc-completed-constant-completion-right-exact` records preservation of the
cokernel of a map between finite completion modules. Its proof uses Noetherian
completion, equality of ideal-power quotients, constant-section properties and the
ordinary flat tensor-limit theorem, followed by tensor right exactness. It has no
phi or comparison-map hypothesis or conclusion. A coefficient-sized equivalent
site handles the pro-etale site's unequal universes.

No change record is required: all additional modules are new, and the only existing
node changes are the item's proof, proof_deps and proof_origin.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
