## What changed

Replaced the proof of `condensed_profinite_scalar_compatibility` without changing
its signature. The proof separates exact slice restriction from scalar
associativity, then uses the existing ringed K-flat scalar associator and the
proved constant-realization scalar comparison. A private derived-adjunction
argument identifies the cochain extension model with that comparison's chosen
left adjoint.

Added `CommutativeConstantSliceRestriction`, constructing actual restriction of
constant-ring module sheaves to a slice with coefficient transport, and proving
its compatibility with constant modules. The comparison is constructed from the
module-sheafification universal property; its underlying map is locally
bijective, and naturality is checked on the sheafification unit.

Added `ProfiniteCoefficientSliceBaseChange`, isolating the coefficient-extension
base-change step on arbitrary module sheaves, before ordinary-module constant
realization. Its direct scalar map and cochain model are actual constructions.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.condensed_profinite_scalar_compatibility`
is closed from the stated intermediate theorem.

`CategoryTheory.commutative_constant_slice_restriction` is proved with no new
holes. All private helpers, exactness instances, and new definitions are proved
or constructed without `sorry`.

One hole is added:
`AlgebraicGeometry.ProEtale.CondensedRing.profinite_coefficient_slice_base_change`
(node `lem-zl-profinite-coefficient-slice-base-change`). This is the coefficient
base-change square on arbitrary constant-ring module sheaves; it does not assert
the original scalar realization comparison, and contains neither the ordinary
scalar extension from point sections to slice sections nor its comparison with
constant realization. The remaining argument combining it with constant
restriction and scalar associativity is complete Lean.

This is a decomposition: one original hole closed, one smaller hole added, net
zero holes closed. There are zero holes in the assigned module and one in the
new module.

## No longer needed

No existing modules are withdrawn, and no existing public imports are removed.
The original node's direct K-flat pullback and tensor-descent dependencies move
to the coefficient base-change node; they are still needed there and are not
claimed as pruning. K-flat resolution and the constant-realization comparison
remain used. Scalar associativity is taken from the already proved
`RingedKFlatWord.scalar_associator`, rather than reconstructed on complexes.
No modules are claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan's first step combines two interfaces: restriction of constants
and derived base change for coefficient extension. Neither is supplied by the
listed generic K-flat preservation theorem alone. The new statements separate
these interfaces without changing the original statement or the unit route.
The original proof's balanced-tensor associativity step already has a proved
library implementation, which this delivery reuses.

The constant-restriction Mathlib/source leaf concerns sheaves in a general
coefficient category. It does not directly provide a linear isomorphism between
module sheaves over the two canonically identified constant ring sheaves. The
new proved theorem supplies that linearity and the exact restriction functor.

## New nodes

`lem-zl-commutative-constant-slice-restriction` records the proved linear
constant-module comparison under restriction to an arbitrary slice. Its
statement includes the actual constant-ring transport, and its proof uses the
local bijectivity of the sheafification unit.

`lem-zl-profinite-coefficient-slice-base-change` records the remaining derived
coefficient-extension base-change square, before constant realization. Its
source proof is restriction of balanced tensor products, followed by K-flat
resolution and localization. The empty slice causes no extra hypothesis: the
restricted sheaves and tensor identities remain valid there.

No existing definition or statement is changed; no change record or forced
adaptation is required.

Validation: all three modules were compiled individually through `lcompile.py`;
the main proof compiled in 19.7 seconds after explicit coefficient universe
annotations repaired the private adjunction helpers. The delivery tool performs
the final compile and axiom probes on the submitted packet.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
