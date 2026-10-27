## What changed

The statement of `AlgebraicGeometry.bertini_finiteCover_transverse_component` is
unchanged. Its proof now chooses a closed point outside the exceptional set by
using the generic point, preservation of coheight under an etale map, and
Jacobson density. A private, proved helper computes the coheight of a closed
point of the smooth connected affine base.

The proof then applies the new pointwise first-jet lemma and the new, completely
proved `AlgebraicGeometry.local_cotangent_pair_component`. The latter contains
the regular local quotient argument, the prime-height computation, contraction
to an affine coordinate ring, and the proof of maximality after taking closure.
In particular, the component construction has not been moved into another hole.
The main module imports these two modules and the existing regularity,
coheight, dimension and nonvanishing APIs privately. No existing public import,
statement, definition or source-library declaration was changed. No change
record or consumer adaptation is required.

## Proved and sorry left

Original holes removed: `AlgebraicGeometry.bertini_finiteCover_transverse_component`
(one of one). Its complete combining proof uses the remaining first-jet lemma.

New holes added: exactly one,
`AlgebraicGeometry.immersiveSystem_local_cotangent_pair`, node
`lem-zl-immersive-system-local-cotangent-pair`. Its proof is exactly `by sorry`
in its own module, with its source and full proof in words in the docstring.
There are zero holes in the item module and zero holes in
`Sheaf.AlgebraicGeometry.LocalCotangentPairComponent`.

This is a decomposition, not a net sorry closure: one original hole is replaced
by one strictly smaller local geometric step. The new pointwise statement
requires a specified closed point of cotangent dimension at least two and
concludes only independent coefficient germs. It assumes neither a finite
cover nor connectedness, affineness, smoothness, or pure dimension, and says
nothing about primes, components, maximality, or codimension. All those parts
of the original argument are now proved in Lean. The additional public theorem
`AlgebraicGeometry.local_cotangent_pair_component` and its private ring-theoretic
helpers are proved without adding any holes.

Edge cases checked: when the system has no generators, generation at the given
point is impossible; cotangent dimension zero or one is excluded explicitly.
For the component lemma the case of dimension two gives a maximal local pair
ideal of height two, while higher local dimension gives the same height-two
prime; neither case requires a nonzero-dimensional quotient. Global regularity
and noetherianity away from the chosen point are not used. For noncontainment,
the selected point belongs to the component and the first section is
nonvanishing there.

## No longer needed

No existing module is withdrawn, and no existing public import is removed.
Redundant proof imports `Mathlib.AlgebraicGeometry.Noetherian` in the item
and `Mathlib.RingTheory.Ideal.Height` in the component file were removed; their
APIs are already publicly imported by the regularity imports.
The new first-jet file omits the finite, smooth and zero-scheme imports copied
from the item's initial header, because its statement needs none of them.

The original plan's following direct dependencies are unnecessary for this route:

- `lem-sc-etale-local-dimension`: the proved scheme-level
  `lem-sbc-flat-locally-quasi-finite-coheight` supplies the dimension comparison.
- `lem-weil-pbc-regular-local-generators-regular-sequence`: the private quotient
  argument proves regularity directly by extending a cotangent basis and
  squeezing quotient dimension against embedding dimension. No regular-sequence
  assertion is needed, and its module is not imported.
- `lem-weil-pbc-spec-irreducible-components-minimal-primes`: the proof constructs
  the generic point of the minimal prime directly and proves maximality.
- `lem-weil-pbc-open-subspace-irreducible-closed-correspondence`: specialization
  and generic points give both maximality of the closure and preservation of
  coheight under the affine open immersion.

The finite-fibre counting argument is also unnecessary: the generic point
already proves that the inverse image of the good open is nonempty. First-jet
inputs (closed-point rationality, the generating-section criterion, projective
charts and the rational unramified cotangent criterion) remain dependencies of
the new first-jet node; they have not been claimed as pruned. Other original
regularity, cotangent, Nakayama, height, localization and zero-scheme inputs
remain where used by the main proof or the proved component theorem. Whether
other targets still need any of the omitted nodes is left to the global queue;
this packet deletes no modules.

## Where the brief, the DAG or earlier work was wrong

All three files passed the remote compiler without warnings (5.0 s, 9.0 s,
and 6.8 s). The node closure has no missing nodes or cycles, and both new node
attachments reproduce their Lean signatures verbatim.

No statement error was found. The original plan asked for a finite-fibre
argument and computations in both the base and the cover; only a point on the
cover and the base closed-point dimension computation are needed. Its general
regular-sequence route can also be replaced by the shorter cotangent-basis
quotient argument above. The unit's finite-cover Bertini step is preserved.

## New nodes

`lem-zl-immersive-system-local-cotangent-pair`, in
`Sheaf.AlgebraicGeometry.ImmersiveSystemLocalCotangentPair`, is the remaining
pointwise first-jet selection of paragraph 3 of the current blueprint proof.
Its three steps are rationality and a nonvanishing frame, spanning by projective
coordinate differences, and the etale cotangent map followed by selection of
two independent classes. Its source is the current blueprint together with
Stacks Tags 01NE, 01NF and 0B2G. It is strictly a part of the original argument.

`lem-zl-local-cotangent-pair-component`, in
`Sheaf.AlgebraicGeometry.LocalCotangentPairComponent`, is completely proved.
It formalizes the independent-parameter ideal and generic-point globalization
steps, using Stacks Tags 00NQ, 00NP, 00E3, 00ES and 02IZ. The original node's
proof, proof dependencies and proof origin now follow the supplied Lean proof.
The latest blueprint and DAG were searched for an existing identical statement;
no duplicate was found. Both nodes record three actual kinds of Mathlib search.
There are no change records.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
