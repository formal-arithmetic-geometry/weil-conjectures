## What changed

Reused the proved independent-universe inverse-image tensor comparison from
`Sheaf.SecSmoothPurity.CochainInverseComparison` for the level comparison,
naturality and generalized pure-tensor normalization. The existing public signatures
and public import of the item are unchanged.

Constructed the system comparison from its explicit evaluation components. The
assembly proof checks vertical and horizontal naturality, reflects invertibility
through jointly faithful evaluations, derives naturality by composing natural
isomorphisms, and verifies the required evaluation equation by cancellation.

Proved the level K-flat clause using ringed-topos pullback and the identity scalar
extension unit. Proved the system K-flat clause using exact jointly faithful
evaluations, the evaluation/coextension adjunction and the tensor total comparison;
this avoids constructing a new inverse-image lift on the sequence topos.

Moved the completely proved assembly adapter into
`Sheaf.Paper.SemilinearSystemIsoAssembly`. Its private scalar-conversion maps are
irreducible and its transition compatibility proof uses a square of ordinary
functions. This avoids repeatedly unfolding the coefficient tower. The public
assembly theorem has no holes.

Moved the completely proved resolving-class argument into
`Sheaf.Paper.GeometricOrdinaryKFlat` so it compiles independently of the tensor
assembly. This adds no holes.

Added `Sheaf.Paper.GeometricTensorComponentHorizontal`, containing the explicit
component construction and the remaining horizontal compatibility equation. Its
statement concerns a fixed family of components and one equality of morphisms;
it asserts neither existence of system tensor isomorphisms nor any K-flat property.

Validation: `lcompile.py --all` compiled all four modules without warnings or
errors. Times were 4.0 s (K-flat support), 4.1 s (horizontal component statement),
48.8 s (system assembly), and 32.7 s (the item). Every file is below 60 s.

## Proved and sorry left

The original hole `WeilConjectures.SemilinearSections.geometricOrdinaryTensor_exists`
is replaced by a complete Lean proof from the horizontal component equation and
existing library declarations. The item's module has zero remaining holes.
`WeilConjectures.SemilinearSections.geometricOrdinary_kflat` is fully proved in the
new support module, which also has zero holes.
`WeilConjectures.SemilinearSections.systemIsoOfEvaluation_exists` is fully proved
and also adds zero holes.

One hole is added:
`WeilConjectures.SemilinearSections.geometricTensorComponent_horizontal`, node
`lem-coef-geometric-tensor-component-horizontal`. This is a decomposition: one
original hole closed, one strictly smaller hole added, net zero. In particular the
level tensor construction and both K-flat clauses are discharged without new holes.

## No longer needed

No original import was removed; the original public import is preserved.

The planned homogeneous-universe comparison
`lem-weil-pbc-algebraic-inverse-image-tensor-comparison`
(`Sheaf.Paper.RingedTopoiInverseImageTensorComparison`) is not needed by this proof:
the independent-universe comparison already proves precisely the required level
statement. No existing module or declaration is withdrawn.

The original plan's additional construction of a ringed-topos inverse image on the
sequence site is unnecessary for the K-flat clause. Exact tensor-preserving
evaluation detects the required acyclicity directly. No source-library declaration
has been changed or removed.

## Where the brief, the DAG or earlier work was wrong

The old plan suggested repeating the inverse-image pairing proof to accommodate
independent site universes. `CochainInverseComparison` already contains that proved
result. The dependency and proof records now cite it directly.

Horizontal compatibility requires an equality for the actual semilinear
transitions, not merely levelwise naturality. It is recorded explicitly as the
remaining step, with the original coefficient and underlying-sheaf normalizations.

## New nodes

`lem-coef-system-iso-assembly` is fully proved in
`Sheaf.Paper.SemilinearSystemIsoAssembly`. It converts compatible evaluation
isomorphisms into a system isomorphism and records its component equation. This
isolates the product-site morphism argument and adds no holes.

`lem-coef-geometric-ordinary-kflat` is fully proved in
`Sheaf.Paper.GeometricOrdinaryKFlat`. It supplies both resolving-class fields by
level pullback and exact evaluation; its statement has no tensor-comparison or
horizontal-compatibility obligation. This separates a self-contained proof after
profiling and replacing expensive scalar conversions by explicit APIs.

`lem-coef-geometric-tensor-component-horizontal` records horizontal compatibility
of the explicitly constructed tensor components (Zheng Construction 4.1 and Stacks
03EL). The pure-tensor normalization and the fixed `GeometryOrdinary` transition
equations identify both composites with the tensor of the two horizontal maps.
The statement is valid for zero modules and empty sites and does not assume flat
coefficient transitions or enough points. It is a proper substep of the original
argument. No unit route or target signature changes.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
