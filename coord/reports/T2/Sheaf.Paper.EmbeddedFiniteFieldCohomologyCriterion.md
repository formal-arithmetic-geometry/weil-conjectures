## What changed

`Sheaf.Paper.EmbeddedFiniteFieldCohomologyCriterion` now contains the complete
Lean combination of the coefficient presentation, exact-functor homology comparison,
Tor-amplitude transport, the coefficient-site K-flat tensor test, and
`Scheme.constant_field_finite_tor_amplitude_iff`. The existing theorem's signature,
public import and specified `finiteRealization` are unchanged.

Added `Sheaf.Paper.EmbeddedFiniteFieldPresentation` for the remaining comparison of
module presentations. Its conclusion supplies additive heart equivalences, a strong
monoidal structure for the embedded encoding, compatibility with the specified
realization, and the heart constructibility comparison. It has no derived object B,
Tor-amplitude condition, boundedness condition, or cohomological criterion. The main
proof uses it to derive those conditions, including normalization of an unordered
Tor witness to `[min a b,b]` and reflection of homology vanishing through the faithful
intrinsic equivalence. The witnesses are eliminated only inside a proposition; no
definition chooses data from this unproved existence theorem.

The node proof and dependencies follow this argument. The unit's required
constant-field theorem remains used.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.finiteFieldCohomologyCriterion`
(node `lem-sfb-embedded-finite-field-cohomology-criterion`). There are zero holes
left in the item module.

Added one hole in
`AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.finiteFieldPresentation`
(node `lem-sfb-embedded-finite-field-presentation`). Its proof is exactly `by sorry`,
with its source and full proof in words. Thus this delivery is a decomposition:
one hole closed, one strictly smaller structural obligation added, net zero holes.
The field Tor argument and its assembly with constructibility are written in Lean.

Validation: the complete sandbox compiled through `lcompile.py --all` with exit
code 0 and no warnings or errors. A direct signature comparison confirmed that
the original theorem statement is byte-for-byte unchanged.

## No longer needed

No original imports were removed and no modules or nodes are withdrawn. The original
finite-discrete-ring, section-tensor, intrinsic-module and generator comparison
steps remain needed inside the new presentation obligation. They are no longer direct
proof dependencies of the criterion; its direct dependencies are the presentation,
the coefficient flat-model comparison and the constant-field Tor theorem.

The normalized continuous-coefficient encoding modules were searched and read, but
are not imported by the criterion: their continuous coefficient object is different
from `discreteObj A`, and the missing normalization and intrinsic comparison belong
to the presentation obligation. No claim is made that these modules are globally
unused.

## Where the brief, the DAG or earlier work was wrong

The listed finite-discrete condensed-ring theorem provides existence of a ring-object
isomorphism, while `finiteRealization` is defined using the specified constant-function
map. Applying an arbitrary ring isomorphism does not by itself identify that derived
functor. The presentation obligation explicitly retains this compatibility rather
than silently substituting a different realization.

The blueprint ancestor tool returned `None` for this recently created nested item.
The new node uses the actual unit `sk-lem-integral-models`, whose first proof paragraph
was read in `literature/blueprint/latest/`; its constant-sheaf comparison is the source
of the remaining structural step. Searches of the blueprint found no identical
standalone statement.

## New nodes

`lem-sfb-embedded-finite-field-presentation` states the common heart presentation and
compatibility with the actual realization. It is the coefficient-comparison part of
the original first two proof steps, with no field Tor conclusion. Its source, proof
steps, existing dependencies, exact Lean statement and actual Mathlib search results
are recorded. Edge cases considered were the empty scheme, zero module and zero
complex; the finite field is nonzero, and no nonemptiness of X or boundedness of a
complex is assumed. No existing statement or definition changes, so no change record
or forced consumer adaptation is needed.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
