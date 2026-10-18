## What changed

Proved `AlgebraicGeometry.proper_smooth_geometric_components_locally_constant` with its exact
original signature. Four private, fully proved helpers identify zeroth structure-sheaf
cohomology with the component count, compare the two geometric-fibre presentations, and
characterize connectedness by component count one. The final proof combines the existing
lower-semicontinuity theorem with cohomological upper semicontinuity and takes the open fibre
of the resulting locally constant count for the geometric-connectedness consequence.

Added the proof-only import
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChange` to use the already proved
`hFiber_pullback_of_isPullback` consequence of coherent flat base change. Import-direction
checking confirms that it is acyclic. Updated the existing node's proof, proof dependencies,
proof origin and obsolete tool-use approval to match the implemented argument. No public
signature, definition, target or unit route changed.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.proper_smooth_geometric_components_locally_constant`
(node `lem-weil-pbc-proper-flat-geometric-components-locally-constant`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
The imported lower-semicontinuity, product-of-fields and algebraic-closure criterion inputs
retain their pre-existing proof obligations. This is a proof from those declared inputs,
not a claim that their transitive obligations are closed.

Validation: the complete original-signature theorem and all four helpers compile through
`lcompile.py`, with no warnings. The empty-space case is included in the product finrank
argument, and the reverse connectedness implication explicitly requires nonemptiness from
`Nat.card = 1`. The base is arbitrary and may be empty or nonreduced.

## No longer needed

Removed direct proof-only imports:

- `Sheaf.AlgebraicGeometry.FieldExtensionFpqcCover`: no fpqc-cover witness is needed; the
  existing fibre-dimension base-change theorem already performs the field-extension comparison.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Semicontinuity`: supplied publicly
  by the newly used `DirectImage.BaseChange` module; its upper-semicontinuity theorem is still used.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`: likewise supplied by
  `DirectImage.BaseChange`; its flat cohomological base-change result remains used through the
  existing fibre-dimension comparison.

Pruned node `lem-pc-field-extension-fpqc-cover` from this item's direct proof dependencies and
its obsolete `tool_uses` entry. The module `Sheaf.AlgebraicGeometry.FieldExtensionFpqcCover`
is no longer required directly by this proof; this does not assert that other consumers
no longer need it. Pruned `def-weil-closed-immersion` from the direct proof dependencies:
properness and the existing base-change API already provide the required morphism instances,
so this proof never constructs or analyzes a diagonal. No blueprint unit is bypassed.
No other planned node or required dependency module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The stated plan's direct application of finite
cohomology and explicit tensor-basis comparison can be shortened by existing library API:
`hFiber_pullback_of_isPullback` and `hFiber_eq_finrankH` already implement the dimension
comparison. The product theorem's scalar-map clause is essential: a bare ring equivalence
would not justify the linear-equivalence finrank calculation. Unit-sheaf finite presentation
needs the explicit universe-specialized `IsFiniteLocallyFree.isFinitePresentation` instance.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
