## What changed

Replaced the proof hole of `CategoryTheory.CondensedBar.condensed_product_bar_resolution_model`
by a reduction that constructs both derived column comparisons on the given resolution,
proves their derived-unit normalization equations, proves compatibility with every pair
of simplex maps, and constructs and normalizes the derived invariants comparison.
The private derived-unit helpers follow the already proved single-bar helpers in
`CondensedBarTotalAugmentation`, without changing its public interface.

Separated the remaining underived coordinate construction and the actual diagonal
augmentation into two new modules. The first has no resolution or derived assertions.
The second is only the quasi-isomorphism of the component-prescribed augmentation and
has no currying, derived-column, operator-comparison or derived-invariant assertion.
Their docstrings give sources and complete proofs in words. The original model,
public definitions and theorem signature are unchanged.

## Proved and sorry left

Original holes: one. The original theorem now has a complete proof from the two
strictly smaller intermediate statements. This is a decomposition, not an unconditional
proof of the product model. Holes closed: one; holes added: two; net: minus one.

Remaining holes added by this delivery:

- `CategoryTheory.CondensedBar.exists_productBarCoordinates`, node
  `lem-sfb-condensed-product-bar-coordinates`.
- `CategoryTheory.CondensedBar.exists_productBarAugmentation`, node
  `lem-sfb-condensed-product-bar-augmentation`.

No hole remains in the assigned module. No definition contains a hole, and no object
is defined by selecting an arbitrary witness of an unproved existence theorem.
All existence witnesses are eliminated inside the original theorem proof.

Validation: server compilation succeeded for the coordinate module (42.0 s),
augmentation module (39.1 s), and the complete main proof (31.3 s during profiling).
All development profiler options have been removed. The delivery tool performs
the final clean compile and axiom/declaration checks on the complete packet.

## No longer needed

Removed the assigned module's private proof import
`Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom`; that dependency is now confined
to the coordinate construction where it is used. Existing public imports are preserved.

The original node no longer directly uses `lem-sfb-condensed-free-linearization-tensor`,
`def-sfb-modobj-internal-hom`, `def-sfb-condensed-equivariant-bar-data`,
`def-sp-double-complex-total`, `lem-sfb-condensed-product-action-inflation`,
`lem-sfb-condensed-injective-bar-rows`, or `lem-sfb-condensed-bar-total-augmentation`
as proof steps: the needed coordinate/augmentation arguments are explicitly assigned
to the two new nodes. These dependencies remain needed below them, or as statement
interfaces. No module or mathematical dependency is claimed globally pruned.
The parent product-bar-comparison theorem is never invoked.

## Where the brief, the DAG or earlier work was wrong

The single-group total-augmentation theorem is proved, but its useful generic derived
unit/operator helpers are private, and its conclusion is specialized to a single bar.
The product-model step therefore needs real unit transport and cancellation for the
product columns; the proof includes these rather than assuming a product specialization.
The product coordinate construction and normalization of the actual diagonal augmentation
are not supplied directly by any searched dependency theorem. Their remaining glue is
now separated as explicit proof steps, with no weakened claim.

The unit's `realized` record is empty; no unit statement or proof step is bypassed.
Trivial groups retain their unnormalized degrees; degree zero uses empty tuples.
The two new statements also include the zero ring, empty profinite parameters and
arbitrary resolutions of zero. No projective/free evaluation of sheafification is assumed.

## New nodes

`lem-sfb-condensed-product-bar-coordinates` states just the underived free-product,
currying, column and full diagonal coordinate identifications (steps 1–3 and 5 of the
original node). Searches used LeanSearch, LeanFinder, Loogle and source grep; ordinary
currying and ordinary representation bar resolutions do not provide this normalized
condensed-module statement. Its source is the original internal-bar expansion of latest
blueprint paragraph (3), marked as an agent argument.

`lem-sfb-condensed-product-bar-augmentation` states just the specified invariant inclusion
into the diagonal total and its quasi-isomorphism (step 6 of the original node).
Its proof uses the existing injective-row and single-bar total augmentation statements,
with product-coordinate transport. The same three search families found no direct
product augmentation theorem. Both nodes inherit the original chapter and unit.
No existing shared module or interface is changed, so no change record is required.

WANTED: an independent reference for ordinary condensed internal-module product bar
coordinates and their normalized invariant augmentation. The latest blueprint paragraph
(3) does not itself give this argument; the inherited expansion and both new nodes are
explicitly marked as written by an agent, as in the original node.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
