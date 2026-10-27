## What changed

Replaced the proof hole of `AlgebraicGeometry.WeilSheaf.exists_clopen_return_restriction`
with an explicit powered geometric pullback and a proof of all its required properties
from the named subobject-lifting step. The original statement and all its public imports
are unchanged. Added three modules:

- `ClopenReturnData`: constructs the geometric map by the pullback universal property,
  and proves its Frobenius-return square.
- `ClopenReturnStalk`: proves actual Frobenius-module equivalences for the powered
  geometric pullback, using the existing iterated Weil-map square. The private transport
  and change-of-lift helpers retain complete proofs adapted from the native library.
- `ClopenReturnSubobject`: states the remaining geometric step: extend a lisse subobject
  on the distinguished return sheet, using its Frobenius translates, to a source
  lisse subobject whose restriction recovers the given injection.

The main proof uses source simplicity on that lifted subobject, exactness to preserve
zero objects and isomorphisms, and the proved stalk equivalence to establish nonvanishing.
The functor is the existing explicit `poweredGeometricPullback`; it is not an arbitrary
witness selected from an unproved existence theorem. No shared definition or interface
was changed, and no other existing module was adapted.

## Proved and sorry left

Closed the one original proof body:
`AlgebraicGeometry.WeilSheaf.exists_clopen_return_restriction`
(`lem-zl-clopen-return-restriction`). It now has a complete Lean proof from its imports.

Additionally proved:
`AlgebraicGeometry.WeilSheaf.exists_clopen_return_geometric_map`
(`lem-zl-clopen-return-data`) and
`AlgebraicGeometry.WeilSheaf.poweredGeometricPullback_stalkEquiv`
(`lem-zl-clopen-return-stalk`).

Added exactly one proof hole:
`AlgebraicGeometry.WeilSheaf.exists_lisse_subobject_clopen_return`
(`lem-zl-clopen-return-subobject`), whose proof is exactly `by sorry` in its own new module.
There are no proof holes in the item, geometric-map module, or stalk-equivalence module.
This is a decomposition, not a net reduction of holes: one upper hole closed and one
strictly smaller geometric lifting obligation added. The existing imported theorem
`poweredGeometricPullback_frobeniusPowStr` remains an existing stated dependency, with
its own node and proof plan; its body was not changed or duplicated.

Validation: the prescribed `lcompile.py --all` compiled all four modules in dependency
order successfully with no warnings. Profiling options were removed before this final
successful run. The required `deliver3.py` runs the delivery preflight before pushing.

## No longer needed

No existing modules or DAG nodes are withdrawn. No original public imports are removed.
Removed unused draft imports from new modules: `ConstantFieldRestriction` and
`StalkUpperStar` from the stalk module, and `StalkUpperStar` from the subobject module.
The final stalk module imports the narrower APIs actually used.
The proof needs the original three mathematical steps: powered restriction, local return
comparison, and induction of subobjects over the Frobenius orbit. It avoids rebuilding the
already available powered-pullback construction and its exactness/lissity proofs, and
uses a general positive residue-extension exponent instead of separately proving it is one
for this open immersion. The new stalk module does not import `PoweredGeometricPullbackStalk`: it proves the stronger
Frobenius-module equivalence directly from the iterate square. It does use the native
`StalkCharpoly` module for its proved change-of-lift and return-power APIs.

## Where the brief, the DAG or earlier work was wrong

The original statement and geometric proof plan are consistent. The original planned
constant-field API requires an isomorphism of whole geometric fibers and therefore cannot
be applied directly to one sheet. The native powered-geometric-pullback API provides the
required actual functor.

A preliminary, never-delivered split in this sandbox asserted simplicity for an arbitrary
exact lisse-preserving functor with pointwise power transport. That inference lacked a
subobject-lifting hypothesis. Both that draft statement and its node were removed before
this packet; they do not occur in the delivery. The remaining lifting statement is tied
to the actual geometric map by both pullback projections and to the explicit powered
pullback functor. It assumes neither simplicity nor a nonzero stalk and asserts neither
irreducibility nor pointwise transport.

## New nodes

`lem-zl-clopen-return-data`: the proved pullback construction of the geometric map and
its return-power Frobenius compatibility. The projection equations determine this map.

`lem-zl-clopen-return-stalk`: the proved Frobenius-module comparison, uniform in the source
constructible Weil sheaf. Its only unproved proof dependency is the already stated
iterated Weil-map square, not a new statement of this delivery.

`lem-zl-clopen-return-subobject`: the remaining induction-and-extension step for lisse
subobjects on the distinguished clopen sheet. Its docstring gives the full cyclic
transport, wraparound compatibility, extension by zero, lissity, and recovery argument.
The cases of zero subobject, whole subobject, empty complement and degree one are included.
No change records are needed because existing signatures and definitions are unchanged.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
