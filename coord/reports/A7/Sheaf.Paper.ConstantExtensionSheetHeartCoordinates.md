## What changed

Decomposed the one hole in `WeilConjectures.constantExtensionSheetHeartCoordinates`
into geometric, coefficient-stage and common-stage statements, preserving the theorem's
signature. The theorem now combines these three strict constituent steps with a complete
categorical construction of its Weil-coordinate clause.

In the original module, `fixedPairTransportEquivalence` proves that transporting invertible
endofunctor algebras along an equivalence and a commutation isomorphism is an equivalence.
It explicitly lifts carrier morphisms and structure isomorphisms through the fully faithful
functor. `sheetComparison` assembles the specified successor and return maps componentwise.
`sheetWeilCoordinates` proves the standard-heart condition is detected componentwise,
restricts the fixed-pair equivalence to these full subcategories, and obtains finite-limit
and finite-colimit preservation from the resulting equivalence. Its identification is
reflexive, and its two normalization clauses use precisely the prescribed comparisons.

Extracted the 20 existing interfaces to `Sheaf.Paper.ConstantExtensionSheetHeartData`,
publicly re-exported by the original module to avoid the import cycle introduced by the
three new proof modules. A parser comparison verifies identical signatures and bodies for
all 20 interfaces. Their docstrings now name the interface node. No definition data is
chosen from a new existence assertion. No source-library module changes. The unit route
and every target statement are unchanged.

Change record: `coord/changes/A7-constant-extension-sheet-heart-interface.md`.

## Proved and sorry left

Original holes: 1. The body of
`WeilConjectures.constantExtensionSheetHeartCoordinates` is completed by a reduction.
This is a decomposition, not a net proof: 1 upper hole closed, 3 lower holes added,
net -2 holes. The original module and the interface module contain zero `sorry`.

Exactly three holes remain in the delivery:

- `WeilConjectures.constantExtensionSheetGeometry`, node
  `lem-zl-constant-extension-sheet-geometry`: only the tensor/clopen geometry and
  Frobenius identities, without any coefficient-category or Weil-coordinate conclusion.
- `WeilConjectures.constantExtensionSheetCoefficientEquivalences`, node
  `lem-zl-constant-extension-sheet-coefficient-equivalences`: only finite, integral and
  rational coefficient clauses, assuming the geometric package.
- `WeilConjectures.constantExtensionSheetCommonStageEquivalences`, node
  `lem-zl-constant-extension-sheet-common-stage-equivalences`: only common-stage clauses
  and coordinate factors, assuming the geometry and coefficient clauses.

Each new hole has a full source-based proof in its declaration docstring and matching
DAG steps. The existing dependencies are reused in their plans; the categorical portion
needs no new postponed statement. Edge cases checked in the mathematics: m=1, empty
X_0, zero objects, and the first finite coefficient level n=0. There is no claim that a
single-sheet restriction from a nonempty multi-sheet scheme is an equivalence; only the
product and the coordinate factor are equivalences.

## No longer needed

No mathematical dependency, source declaration or unit step is withdrawn or claimed as
pruned. The original theorem no longer directly needs the following proof imports; their
responsibilities move to the named constituent modules:

- `WeilConjectures.AlgebraicGeometry.FiniteGaloisTensorCoproduct`
- `Sheaf.AlgebraicGeometry.SpecFiniteProductFields`
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`
- `Sheaf.Paper.IsomorphismDerivedPullback`
- `Sheaf.Paper.IsomorphismFieldTransport`
- `Sheaf.Paper.FiniteClopenDerivedDecomposition`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.Paper.IntegralPullbackComposition`
- `Sheaf.Paper.PullbackIdentitiesScalarExtension`

The original node's direct proof dependencies now name the three constituent lemmas and
the unchanged interface node. Its former proof dependencies are retained by those nodes
where the corresponding argument is still needed. The original tool approvals are kept;
none is withdrawn. All six original public imports are preserved through the public
interface re-export, with no change to their availability.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. One planned interface is weaker than its prose suggests:
`AlgebraicGeometry.finiteGaloisTensorCoproduct` accepts the tensor algebra equivalence
as a hypothesis; it does not construct that equivalence. The geometry step must first
supply the algebra splitting (by the affine finite-Galois decomposition and scalar
extension, or Dedekind independence and a dimension count), then apply the coproduct
interface. The new geometry proof docstring explicitly keeps this algebra step. The seven-step proof
plan contains substantial geometric and coefficient-interface assembly; its declared dependencies do not directly instantiate
the current ZlSheet clause packages. The delivery makes those assembly steps explicit
items and proves the separate categorical argument. This does not bypass the parent or
the blueprint unit. The parent constantExtensionCyclicSheets theorem does not supply the
full geometry package's specified tensor splitting and coordinate data, and is not used
to introduce a circular dependency on the parent theorem node.

## New nodes

`def-zl-constant-extension-sheet-heart-data` owns the 20 unchanged interface declarations
in `Sheaf.Paper.ConstantExtensionSheetHeartData`. This import-cycle extraction has no hole.

`lem-zl-constant-extension-sheet-geometry` corresponds to original steps 1–2, with the
finite-field and affine-chart calculation documented fully in its theorem docstring.

`lem-zl-constant-extension-sheet-coefficient-equivalences` corresponds to the finite,
integral and rational parts of steps 3–4 and their scalar normalization from step 7.

`lem-zl-constant-extension-sheet-common-stage-equivalences` corresponds to passage of
those equivalences to common stages, the Frobenius equivalence and coordinate factors.

All new nodes keep the original chapter and unit. Blueprint searches for cyclic sheet,
clopen and common stage found no duplicate of these specialized assembly statements.
Each theorem node records fresh LeanSearch, LeanFinder/Loogle and source-grep searches.
The separate interface change record is
`coord/changes/A7-constant-extension-sheet-heart-interface.md`.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
