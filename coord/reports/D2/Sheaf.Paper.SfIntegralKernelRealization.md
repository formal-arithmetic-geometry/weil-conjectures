## What changed

Proved the unchanged body of `WeilConjectures.sfIntegralKernel_operation_realization`
in `Sheaf.Paper.SfIntegralKernelRealization` from two separate geometric comparison
steps, in new modules `SfIntegralOpenKernelCompactSupport` and `SfIntegralClosedKernelRoos`.
No existing signature, definition, public import, or target changed.

The proof uses the existing integral pullback constructibility theorem, obtains
open constructibility by comparison with the recorded compact-support value, and
obtains closed constructibility by the distinguished localization triangle and
triangulatedness. It proves module linearity directly by cancellation against the
monic open counit and epic closed unit. It then descends that linearity through
localization and checks that the scalar action is the published canonical action.
The literal full-subcategory restrictions inherit this linearity.

The open comparison asserts only the open vertex isomorphism, assuming the
constructibility of the recorded pullback. The closed comparison asserts only its
Roos vertex comparison, assuming completeness of K and its recorded pullback. It
needs neither an open complement nor constructibility. Their combination, the
constructibility argument and the scalar-action argument are complete Lean proofs.
The unit route (the actual sheaf localization sequence) is retained.

All three modules compile through lcompile. The item compiled in 9.8 seconds before
final import cleanup. New comparison statements were checked on zero objects and
empty complements: their assertions reduce to the corresponding zero Roos vertices.
For the closed statement the completeness of both inputs is explicit; the proof
never claims ordinary pullback preserves arbitrary derived completeness without the
immersion comparison. Stacks 09AH supplies the actual localization sequence and
099N(4) supplies the direct-image Roos description. The Mathlib and source-library
searches found localization linearity machinery but no complete operation comparison.

## Proved and sorry left

Original item: one hole closed, at
`WeilConjectures.sfIntegralKernel_operation_realization`; zero holes remain in its
module. This is a decomposition, not a net proof: zero of the original one hole is
fully discharged without new holes. Two holes are added, net increase one:

- `WeilConjectures.sfIntegralOpenKernel_compactSupport`, in
  `Sheaf.Paper.SfIntegralOpenKernelCompactSupport`, node
  `lem-sf-integral-open-kernel-compact-support`.
- `WeilConjectures.sfIntegralClosedKernel_roos`, in
  `Sheaf.Paper.SfIntegralClosedKernelRoos`, node
  `lem-sf-integral-closed-kernel-roos`.

The three private helpers in the original module are fully proved:
`linear_of_monic_counit`, `linear_of_epic_unit`, and `sfIntegralKernel_ambient_linear`.
The remaining holes are public theorem bodies exactly `:= by sorry`, each with a
source, natural-language proof and matching new node. No data is chosen from them
by any new definition.

## No longer needed

No original import was removed. A trial redundant proof import of
`Sheaf.Paper.SfIntegralConstructibleLinear` was removed: it is already publicly
available through the existing presentation data. The remaining proof imports are
`import all IntegralConstructibleLinear` for the canonical action comparison,
`IntegralOperationsPreserveConstructible`, and the two new comparison modules.

The assigned node no longer uses `lem-sf-finite-immersion-constructibility-interval`
(`Sheaf.Paper.FiniteImmersionConstructibilityInterval`) or
`lem-sf-integral-direct-image-constructible`
(`Sheaf.Paper.SfIntegralDirectImageConstructible`) on this route. Closed constructibility
follows by two-out-of-three in the original localization triangle. Neither node is
needed by either new comparison. No module is withdrawn: other consumers can still
need them.

The original direct dependency `lem-sf-open-finite-constructibility-interval`
(`Sheaf.Paper.OpenFiniteConstructibilityInterval`) is unnecessary in this argument:
constructibility is already part of the recorded compact-support value. It can still
be needed internally by the compact-support construction, so no global withdrawal is
claimed. The open quotient Koszul and semilinear tensor nodes are not direct steps
here; they remain behind the integral open reduction comparison. The immersion
comparison, integral pullback comparison, open reduction comparison, open adjunction
transport, ringed open Roos preservation, direct-image limit comparison and complete
direct-image reduction comparison move to the plans of the two new geometric steps.
The canonical integral constructible linearity node remains used directly.

## Where the brief, the DAG or earlier work was wrong

The original plan proved closed constructibility independently, but the latest
blueprint explicitly obtains it from triangulatedness once the open term is known.
Following that argument removes an unnecessary finite closed-image constructibility
step and its cohomological bound. The original docstring retains the earlier longer
proof plan; the updated node and the Lean proof record the shorter route.

No false statement, tool failure, definition repair or forced consumer adaptation was
found. The two unresolved comparisons still require transporting the canonical
coefficient maps and finite-tower transitions; merely invoking an unnormalized
object isomorphism would not supply those arguments. Those are the genuine geometric
steps split off here, rather than another copy of the entire realization obligation.

## New nodes

`lem-sf-integral-open-kernel-compact-support` identifies the open kernel with the
recorded compact-support value. It is strictly the open vertex part: it asserts no
preservation or linearity, and assumes constructibility of the recorded pullback.
Change record: `coord/changes/sfIntegralOpenKernel_compactSupport.md`.

`lem-sf-integral-closed-kernel-roos` identifies the ordinary closed composite with a
recorded direct-image Roos vertex. It is strictly the closed vertex part: it assumes
completeness of both relevant inputs and asserts no constructibility, complement,
linearity or localization triangle.
Change record: `coord/changes/sfIntegralClosedKernel_roos.md`.

Both records point to the current blueprint ancestor, inherit the assigned node's
unit, include three kinds of Mathlib search, and name their proof dependencies.
Whole-blueprint duplicate searches found no existing node stating either comparison.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
