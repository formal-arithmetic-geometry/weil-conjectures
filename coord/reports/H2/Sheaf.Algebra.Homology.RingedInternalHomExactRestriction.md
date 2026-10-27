## What changed

Decomposed `CategoryTheory.ringedInternalHom_exact` into its independent covariant and
contravariant cone-and-shift arguments. Two new public component theorems in separate
modules state those arguments, and the assigned theorem pairs their conclusions in Lean.
The original theorem signatures and all public imports are unchanged. The tensor adjunction,
six restriction instances, and restriction statement are untouched.

Each component has the source Tag 08JC, a complete proof in words, and a new DAG node.
Their edge cases include zero complexes, zero and identity chain maps, arbitrary shifts,
and unbounded complexes: each is a finite cone splitting, so no exactness of infinite
products or boundedness is assumed. The first variable uses the triangulated opposite
shift, with the signed coherent correction described in its docstring.

## Proved and sorry left

This is a decomposition, not a completed exactness proof. The original hole in
`CategoryTheory.ringedInternalHom_exact` is closed by combining two strictly smaller
claims, one per variable. One of two original holes is closed; two holes are added.
The packet therefore has three sorry declarations, a net increase of one:

- `CategoryTheory.ringedInternalHom_restriction`: unchanged original hole,
  `lem-weil-pbc-ringed-internal-hom-exact-restriction`.
- `CategoryTheory.ringedInternalHom_covariant_exact`: new component hole,
  `lem-weil-pbc-ringed-internal-hom-covariant-exact`.
- `CategoryTheory.ringedInternalHom_contravariant_exact`: new component hole,
  `lem-weil-pbc-ringed-internal-hom-contravariant-exact`.

No definition contains sorry. The previously proved declarations remain proved.

## No longer needed

No modules, declarations, or existing imports are withdrawn. The parent exactness proof
now imports only the two component modules; its cone and shift dependencies are attached
to those components. The parent node retains the separate normalized independent-universe
calculus and its dependencies because those declarations remain in the source library.
No pruning progress is claimed.

## Where the brief, the DAG or earlier work was wrong

The library already proves normalized covariant and contravariant exactness in
`RingedInternalHomShiftOfUniverses` and `SignedDerivedInternalHomExact`, but both modules
reach the assigned item through public compatibility imports. Direct reuse creates an
import cycle. An attempted extraction preserved their declarations but exposed expensive
elaboration: the unchanged original shift module also exceeded the fixed 60-second limit.
Profiling identified 31- and 21-second composite-shift instance searches; local explicit
instances and componentwise comparisons were explored. This extraction is not in the
packet, and none of its changes to other modules or records is submitted. It remains in
scratchpad for reference. The partial delivery instead makes the two distinct arguments
into parallel items as required by the brief. No source-library declaration is removed,
changed, or replaced by sorry.

## New nodes

`lem-weil-pbc-ringed-internal-hom-covariant-exact`: the fixed-first-variable functor has a
coherent target-shift structure and preserves distinguished triangles. Its proof is the
K-injective cone closure, finite Hom-cone splitting and localization argument of Tag 08JC.

`lem-weil-pbc-ringed-internal-hom-contravariant-exact`: the fixed-second-variable functor
from the triangulated opposite has a coherent signed shift structure and preserves
distinguished triangles. Its proof is the signed cone-to-inverse-rotation comparison,
coherence on product projections and localization argument of Tag 08JC.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
