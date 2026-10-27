## What changed

Replaced the proof hole of
`AlgebraicGeometry.Scheme.relative_completed_module_realization_exact` without changing
its signature or existing public imports. Constructed the completion evaluation cone
and the projection-compatible inverse-image coefficient map. The inverse-image map
is obtained from the existing profinite coefficient theorem, through explicit
identity-component isomorphisms of the two quotient-tower presentations.

Proved exactness on **all** completion modules. For C = AdicCompletion(I,A) and J = IC,
completion evaluation is surjective with kernel J^n. Its quotient isomorphisms produce
an isomorphism of the C/J^(n+1) and A/I^(n+1) sheaf diagrams. Applying
`completed_constant_algebra_flat_quotients` to C,J proves exactness of the actual
scalar-extension functor. Constant-module sheafification is exact by evaluation
and sheafification exactness; both subsequent scalar restrictions are exact.
Additivity and absolute lissity of finite modules come from
`completed_constant_module_model`.

Added `Sheaf.Paper.AdicLisseRelativeRestriction` for the remaining geometric transport
step. Its hypothesis is an absolute adic-lisse module and a projection-compatible
coefficient map. It contains no completion-module realization or exactness assertion.
It is strictly one part of the argument, rather than the assigned theorem renamed.
The original theorem combines this step with the proved exactness and coefficient
construction. Its final comparison uses the ordinary scalar-restriction composition
isomorphism and cancellation of the inverse and forward coefficient isomorphisms.
Relative adic lissity is transported through that module isomorphism explicitly.

Only the assigned module, this new module and their own DAG nodes are changed.
No existing shared definition, statement, attribute or public import changes.

Verification: `lcompile.py --all` compiled both modules; the assigned proof took
26.7 seconds. Its theorem signature was compared with the repository text and is
unchanged. A local unused-variable linter scope preserves the original named
existential additivity witness `hc` without its unavoidable warning. The delivery
check recompiles this final packet.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.relative_completed_module_realization_exact`
(node `lem-weil-pbc-relative-completed-module-realization-exact`).
There are zero holes left in the assigned module.

Added one hole:
`AlgebraicGeometry.Scheme.adicLisse_relative_restrict`
(node `lem-weil-pbc-adic-lisse-relative-restriction`).
This delivery is a decomposition: one hole closed, one hole added, net zero.
The new hole is only the passage from absolute to relative local models; the
coefficient-map construction, exactness on all modules, additive composite and
cancellation of coefficient presentations have complete Lean proofs.

The existing dependency `completed_constant_module_model` remains a dependency;
its existing hole is neither changed nor newly added here.

## No longer needed

No existing import is removed: the two original public imports are required by the
unchanged theorem signature. New proof imports are private.

The former direct proof dependency
`lem-weil-pbc-completion-noetherian-quotient-noetherian`, module
`WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient`, is not needed by this
proof. The stronger general quotient-Noetherian criterion is unnecessary because A
is already Noetherian. Use the existing
`AdicCompletion.isNoetherianRing` in
`WeilConjectures.RingTheory.AdicCompletionNoetherian` instead.
This is pruning of this item's proof edge only; no claim of global unreachability
or withdrawal of the former dependency is made.

The other declared dependencies are retained. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The module-realization record supplies exactness only after restriction to finite
modules, while this theorem requires exactness on all modules. Its finite-exactness
field alone therefore does not prove this item. The independent flatness calculation
above fills this gap without strengthening that record or changing its consumers.

The existing DAG's final sentence refers to relative local models but has no theorem
for transporting the absolute adic-lisse model to the inverse-image coefficient
presentation. The new node isolates precisely that step. Its docstring gives the
constant-module diagram comparison, limit argument and projected scalar-linearity
argument, including the empty site, zero module/ring and I=0 or I=top cases.
No false statement or required interface repair was found.

## New nodes

`lem-weil-pbc-adic-lisse-relative-restriction`, module
`Sheaf.Paper.AdicLisseRelativeRestriction`, states the geometric local-model transport.
It keeps the same covering and complete A-module witnesses; natural constant-module
inverse-image comparisons identify the quotient diagrams, and scalar restriction
preserves their limits. The proof uses the projection equation to transport scalar
linearity. Source: Stacks Tags 09BT(3) and 00YV(2),(5),(6). No change record is needed:
no existing interface changes.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
