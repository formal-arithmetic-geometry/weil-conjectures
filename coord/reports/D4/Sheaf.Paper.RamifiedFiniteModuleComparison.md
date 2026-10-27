## What changed

Replaced the hole in
`WeilConjectures.RamifiedPullback.finiteModuleComparison_exists` by composition of
an isomorphism on the target coefficient site and two isomorphisms from
uniqueness of left adjoints. The item retains its exact signature, public
import, definitions, and normalized formula on all section tensor generators.

Added `Sheaf.Paper.RamifiedFiniteScalarComposition`. Its theorem
`WeilConjectures.RamifiedPullback.finiteScalarComposition_exists` is proved:
first commute reduction with finite scalar extension using the source
projection square, then commute finite scalar extension with geometric
pullback using naturality of the constant-section coefficient map. The
composite adjunction units prove both comparisons on generators. Tensor
linearity proves the complete formula with all three scalar factors. All
helpers in this module are private and proved. No target coefficient map or
coefficient isomorphism on X is required for this factor.

Added `Sheaf.Paper.RamifiedCoefficientModuleBaseChange`. Its remaining theorem
is the single-site balanced associativity factor for an arbitrary finite
coefficient module N. It involves no scheme morphism, no inverse image, and
no reduction of N. Its documented proof tensors the supplied coefficient
isomorphism with N, between the two explicitly described associators. The
original theorem composes this factor with the proved composition factor;
commutativity of multiplication gives exactly the original normalization.

Only the item, two new modules, their two new nodes, and the item's proof
record are changed. No existing consumer or source-library file is changed.
The two new modules compiled together in 6.0 and 30.0 seconds. Static checks
confirm the original theorem signature and both original definitions are
unchanged, the new node signatures agree with Lean, and all proof-dependency
lists agree with the proof steps. The delivery tool checks the complete packet.

## Proved and sorry left

The original hole in
`WeilConjectures.RamifiedPullback.finiteModuleComparison_exists`
(node `lem-weil-ramified-finite-module-comparison`) is closed by a complete Lean
proof from the factors. Its module has zero remaining holes.

`WeilConjectures.RamifiedPullback.finiteScalarComposition_exists`
(node `lem-weil-ramified-finite-scalar-composition`) and all its private helpers
are proved without any new holes.

One hole is added and remains:
`WeilConjectures.RamifiedPullback.coefficientModuleBaseChange_exists`, node
`lem-weil-ramified-coefficient-module-base-change`. It states just the
single-site coefficient factor, with its source, complete proof in words,
and edge-case discussion in the docstring. It does not restate the item's
comparison of geometric pullbacks. This delivery closes one upper hole and
adds one strictly smaller hole: a decomposition with net zero holes closed,
not a complete proof of the original mathematical obligation.

## No longer needed

The item does not use
`lem-weil-pbc-algebraic-inverse-image-tensor-comparison` or its module
`Sheaf.Paper.RingedTopoiInverseImageTensorComparison`. Composing the existing
scalar and geometric pullback adjunctions proves the needed composition
factor directly, without lifting the set inverse image to algebraic objects.

It also does not use `def-weil-pbc-ringed-tensor-section-calculus` or
`Sheaf.Paper.RingedTopoiTensorSections`: the existing normalized
`Sheaf.Paper.RamifiedFiniteTensorSections` gives the actual scalar adjunction
unit, and linearity of this unit supplies the source balancing equation.
Neither of those unused modules was an import in the item, so no import line
was removed; they are removed from its planned proof dependencies.

The original direct proof dependencies `def-weil-proetale-inverse-image`,
`def-pur-sheaf-tensor-product`, and `def-weil-ramified-pullback-tower-data`
remain needed through the new factors or the item's statement. No unit-level
statement or route is withdrawn, and no existing module is deleted.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed target was found. The planned geometric
inverse-image tensor calculation can be replaced by the shorter universal
property of the already existing module adjunctions. The coefficient factor
still needs balanced tensor associativity through sheafification; a plain
composition of scalar adjunctions alone does not prove it, because restriction
along the finite coefficient projection occurs between the left adjoints.

The remaining factor works for N=0, the zero coefficient ring, and an empty
site. Its argument uses no flatness or positivity of the index e. The proved
composition factor likewise uses only the stated projection square and
constant coefficient naturality, including when e=0.

## New nodes

`lem-weil-ramified-finite-scalar-composition` attaches to the proved theorem in
`Sheaf.Paper.RamifiedFiniteScalarComposition`. It records the two composition
identities and their adjunction-unit normalizations, followed by tensor
linearity. Its source is Stacks 03CZ/03EK/03EL; Mathlib supplies adjunction
uniqueness rather than this particular finite coefficient formula.

`lem-weil-ramified-coefficient-module-base-change` attaches to the one
remaining theorem in `Sheaf.Paper.RamifiedCoefficientModuleBaseChange`. It
records the strictly single-site associativity and coefficient-isomorphism
factor from step 2 of the original plan. Its source is Stacks 03EK/03EL.
Semantic, pattern, and text searches found general scalar adjunctions and
sheaf tensor cancellation, but no direct specialization with the supplied
coefficient isomorphism and its section normalization.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
