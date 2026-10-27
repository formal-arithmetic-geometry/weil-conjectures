## What changed

In `Sheaf.Paper.DerivedPullbackTensorHom`, replaced the proof of
`WeilConjectures.rationalDerivedPullback_existsUnique` with a complete Lean
construction and uniqueness argument. The new proof privately imports
`Sheaf.Paper.IntegralDerivedPullbackLinear` and the existing proved generic
`Sheaf.CategoryTheory.SemilinearScalarLocalization` API. Ambient additive and
constant-scalar linearity restrict to the full constructible subcategories.
A proved private generic helper uses semilinear localization with identity
coefficient map to construct the rational functor. Uniqueness follows from
tensor induction, including the object transports required by the existing
heterogeneous equality specification.

Added `Sheaf.Paper.IntegralDerivedPullbackLinear`, with one named theorem about
the existing normalized integral pullback. Its docstring and node give the
finite-reduction, Roos and localization proof. This is the integral linearity
step in the assigned rational argument; it does not assert existence or
uniqueness of the rational functor. Existing signatures, definitions and public
imports are unchanged. Updated the item node's proof metadata for this partial
realization.

The private tensor specification now uses a small proved `chosenUnique_spec`
helper to expose the specification at the existing named tensor functor without
repeating its full dependent proposition. Public definition bodies and inferred
types remain unchanged. Local transparency keeps the stage-system choice behind
its interface during elaboration, and sequential elaboration avoids concurrent
expansion of these large dependent types. The existing deeply nested coefficient
ring, uniformizer and absolute-value choices are locally irreducible; their
published algebraic interfaces suffice. This was the decisive optimization:
the final main module compiled cleanly in 52.7 seconds via `lcompile.py`.

Profiling identified 22.9 seconds in the final `privateModule` style linter,
which scans declarations despite the explicit public section. Disabled that
style-only scan outside the section so it also applies at end of input. Kernel
checking, axiom checks and delivery checks remain enabled. No compile limit was
raised and no file was split for performance. Final compilation and preflight
are recorded by `deliver3.py`.

## Proved and sorry left

Original holes: six. Closed one original hole, adding one smaller hole: this is
a decomposition, not a net proof gain. Net holes closed minus added: zero.

Closed in the assigned module:

- `WeilConjectures.rationalDerivedPullback_existsUnique`
  (`def-weil-derived-pullback-tensor-hom`), proved from integral scalar linearity
  and the already proved generic localization API.

Unchanged original holes, all attached to
`def-weil-derived-pullback-tensor-hom`:

- `WeilConjectures.rationalDerivedTensor_existsUnique`
- `WeilConjectures.rationalDerivedInternalHom_existsUnique`
- `WeilConjectures.commonStageDerivedPullback_existsUnique`
- `WeilConjectures.commonStageDerivedTensor_existsUnique`
- `WeilConjectures.commonStageDerivedInternalHom_existsUnique`

Added hole:

- `WeilConjectures.integralDerivedPullback_linear`
  (`lem-sf-integral-derived-pullback-linear`). Its proof is exactly `by sorry`;
  its source and complete proof in words are in its docstring and node.

There are five holes in the assigned module and one in the new module.
No definition contains a new hole. The rational functor is determined uniquely
by the theorem used to define it; no arbitrary witness data was introduced.

## No longer needed

None. No existing import, declaration, dependency module or DAG node is
withdrawn. The existing item node had no proof steps or proof dependencies to
prune. Its statement dependencies still describe the finite, integral, tensor,
internal-Hom and common-stage parts of the module and are retained. The new
private imports are both used. No unit statement or route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The assigned node has an empty proof list because it originated as a definition
split, but its Lean module has six existence/uniqueness holes. The rational
pullback docstring supplies the argument; this delivery makes the rational
localization and uniqueness portions actual Lean and isolates its missing
integral scalar-linearity step.

The current `literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-prop-sf-open-closed-triangle/def-weil-derived-pullback-tensor-hom.md` now
describes one condensed-ring derived construction at every coefficient stage,
and explicitly distinguishes it from constructing the operations by finite
reductions. The assigned DAG and Lean module instead still implement the older
finite/integral/rational/common-stage interface. This packet preserves those
existing statements and does not attempt a coefficient-model migration. The
new lemma serves the assigned node's explicit rational-linearity clause; its
proof is marked agent-written and follows the actual normalized Roos model,
with Stacks 099N(5) and Bhatt--Scholze 6.5.9(4) as source context.

Existing pullback-linearity declarations found in the project either impose
extra geometric hypotheses, concern another completed-pullback construction,
or already import the assigned module and would create an import cycle.
The generic semilinear scalar-localization module has no sorry and is used
only as a generic algebraic tool, with no geometric route substituted.

## New nodes

`lem-sf-integral-derived-pullback-linear`, in the assigned chapter and unit,
attaches `WeilConjectures.integralDerivedPullback_linear` in
`lean/Sheaf/Paper/IntegralDerivedPullbackLinear.lean`. It states ambient
additivity and linearity of the existing normalized integral pullback for its
published constant valuation-ring action. The three proof steps cover finite
scalar compatibility, the two Roos cone coordinates, and descent through the
good localization plus its natural comparison. Edge cases include zero objects,
zero scalars, identity maps and arbitrary scheme morphisms; none requires
coefficient flatness or extra scheme hypotheses. Searches of the entire
blueprint and local library found no matching usable general statement;
LeanSearch, LeanFinder and Mathlib grep searches are recorded. No existing
statement or definition changed, so no change record is required.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
