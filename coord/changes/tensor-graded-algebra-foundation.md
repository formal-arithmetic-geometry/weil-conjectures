# tensorGradedAlgebraMap, tensorGradedAlgebraSection, tensorGradedUnit

## Reason

The independent graded algebra and exactness lemmas must precede the presentation module,
so they cannot import that module. Move its three primitive definitions to
`Sheaf.AlgebraicGeometry.TensorGradedAlgebraData` and publicly reexport that module.
The existing qualified names, signatures, visibility, bodies, and meanings are unchanged.
The presentation structures and existence-theorem signatures are unchanged.
The separate repair of tensorGradedPresentation_core_multiply is recorded in
coord/changes/tensor-graded-core-multiply.md.
The target statements and the definitions they denote keep their meanings.

## Old

In `Sheaf.AlgebraicGeometry.SquareZeroTensorGradedPresentation`:

```lean
/-- The underlying module map, with its source and target stated explicitly.
Source: Stacks Project, Tag 09MS, the quotient in the graded ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-presentation). -/
def tensorGradedAlgebraMap {X : Scheme.{u}} {B C : X.CommAlgebraSheaf} (p : B ⟶ C) :
    commAlgebraSheafModule X.sheaf B ⟶ commAlgebraSheafModule X.sheaf C :=
  (commAlgebraSheafModuleFunctor X.sheaf).map p

/-- Read a section of the underlying module as a section of the algebra sheaf.
Source: Stacks Project, Tag 09MS, the graded ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-presentation). -/
def tensorGradedAlgebraSection {X : Scheme.{u}} (B : X.CommAlgebraSheaf) (U : X.Opens)
    (z : Γ(commAlgebraSheafModule X.sheaf B, U)) : B.right.obj.obj (op U) := z

attribute [local irreducible] tensorGradedAlgebraMap commAlgebraSheafModule

/-- The chosen tensor-pullback unit, with a compact explicit module-map type.
Source: Stacks Project, Tag 0096, the tensor-pullback adjunction.
(blueprint: lem-sc-square-zero-tensor-graded-presentation). -/
def tensorGradedUnit {X Z : Scheme.{u}} (j : Z ⟶ X) (M : X.Modules) :
    M ⟶ (pushforward j).obj ((tensorPullback j).obj M) :=
  (Classical.choose (exists_tensorPullbackAdjunction j)).unit.app M

attribute [local irreducible] tensorGradedUnit tensorPullback

```

## New

The exact definitions above are in `Sheaf.AlgebraicGeometry.TensorGradedAlgebraData`.
The presentation module contains:

```lean
public import Sheaf.AlgebraicGeometry.TensorGradedAlgebraData
```

The core assembly is a private definition accepting the algebra data, degree data,
and a square-zero proof explicitly. It selects no data from an existence theorem.
The two public existence proofs eliminate `Nonempty` only to prove `Nonempty`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SquareZeroTensorGradedBoundaryProjection | T2 | Its one use of tensorGradedAlgebraMap resolves through the same public name. No edit is necessary. |
| Sheaf.AlgebraicGeometry.TensorGradedCoefficientSheafAction | M3 | Its three uses of tensorGradedUnit resolve through the unchanged public reexport. The kernel types and coefficient maps have the same meanings. No edit is necessary. |
| Sheaf.AlgebraicGeometry.TensorBoundaryKernelMapNaturality | unclaimed | Its three uses of tensorGradedUnit resolve through the unchanged public reexport. The kernel types, comparison isomorphism, and transported maps have the same meanings. No edit is necessary. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorGradedProductProjection | unclaimed | Its unfolding of tensorGradedAlgebraSection resolves to the verbatim publicly reexported definition. No edit is necessary. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorGradedQuotientMultiply | U2 | Its three uses of tensorGradedAlgebraSection resolve to the same public name, type and body. No edit is necessary. |
| Sheaf.AlgebraicGeometry.TensorCoefficientActionSupport | P3 | Its two uses of tensorGradedUnit resolve to the same public name, preserving both kernel types. No edit is necessary. |
| Sheaf.AlgebraicGeometry.SquareZeroTensorGradedPresentation | N1 (this item) | The three primitive definitions are moved verbatim and publicly reexported; all internal uses retain the same names, types and meanings. |
| Sheaf.AlgebraicGeometry.TensorBoundaryKernelMapLocalMultiplication | D4 | Its four uses of tensorGradedUnit retain the same public reexport, section equation and kernel types. No edit is necessary. |
| Sheaf.AlgebraicGeometry.TensorGradedActionKernelSecondDiagonal | unclaimed | Its six uses of tensorGradedUnit retain the same chosen unit and kernel inclusions through the public reexport. No edit is necessary. |
| Sheaf.AlgebraicGeometry.TensorGradedQuotientActionHomogeneous | unclaimed | Its thirteen uses of tensorGradedUnit retain the same unit, kernel objects and kernel inclusions. No edit is necessary. |
| Sheaf.AlgebraicGeometry.TensorHomogeneousKernelAction | E4 | Its two uses of tensorGradedUnit retain the same source and target kernel types. No edit is necessary. |
| Sheaf.AlgebraicGeometry.TensorKernelSectionProduct | unclaimed | Its twelve uses of tensorGradedUnit retain the same kernel types and inclusion maps. No edit is necessary. |
| Sheaf.AlgebraicGeometry.TensorIdealSectionLocalMultiplication | unclaimed | Its local multiplication calculation uses tensorGradedUnit through the unchanged public reexport; the source and target kernel types and section equations keep the same meanings. No edit is necessary. |

Repair of landing-tool return at head 12f8c9a7a: the three specifically omitted
users are now listed above. A fresh repository-wide name scan also found the newer
TensorHomogeneousKernelAction and TensorKernelSectionProduct users; these are
included to make the list complete. The current downstream scan finds 183
transitive importers and eleven external primitive-definition users, plus the item.
The current claim files name D4 and E4; the other three added users are unclaimed.
All five additional sources were read: they refer to the unchanged definitions,
which remain publicly reexported, so their meanings and interfaces are preserved.
Compiled all five added users unchanged against the delivered `.lbuild` overlay
using lcompile.py: exit 0, no errors or warnings (3.2, 11.6, 10.6, 3.3, 7.4 seconds).
Earlier claim files identified U2 and P3; ProductProjection had no claim file.
The first three original users previously compiled unchanged against the delivery.
QuotientMultiply compiled unchanged against the repaired overlay (2.9 seconds).
ProductProjection could not be checked because its existing dependency
SquareZeroTensorSectionProductComparison has no compiled object in the baseline;
TensorCoefficientActionSupport imports ProductProjection. Both sources were read:
their uses retain the same definitions and require no adaptation. This missing
baseline artifact is not caused by the delivered changes.
No downstream source is adapted. The public reexport preserves the definitions
for all transitive importers. The original public imports stay in place.

Repair of landing-tool return at head a5a21609f: added
TensorIdealSectionLocalMultiplication, unclaimed in the current local claim snapshot.
The fresh primitive-name scan finds twelve external users; every one is listed in
the table above. Its source was read and compiled unchanged against the delivery
overlay with lcompile.py (9.0 seconds, exit 0). Its kernel types and local section
calculation retain exactly the same definitions; no adaptation is necessary.

## Status

landed 20261014T050528-L-1685784 2026-10-14 (merge of deliver/N1/Sheaf.AlgebraicGeometry.SquareZeroTensorGradedPresentation)
