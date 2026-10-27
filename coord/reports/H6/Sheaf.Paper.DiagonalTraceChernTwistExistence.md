## What changed

Kept the signature and public import of
`AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceChernTwist` unchanged.
Its proof now constructs the actual tower Kummer maps and their exactness, obtains
integral reduction data, constructs scalar data using the existing
`semilinearScalarData`, proves its normalized coefficient-unit comparison, and
assembles the Chern record before applying separate finite-boundary and line-twist
steps. All added imports of the item are private proof imports.

The Kummer maps use the published root inclusions and positive-exponent power
maps. Naturality follows from the prime root-transition formula and multiplication
of powers; the zero composite is the kernel condition. Levelwise short exactness
comes from the already proved `cartierProKummer_exact`. Exact evaluation commutes
with homology, and vanishing of every component proves the system homology zero.
This supplies all the Kummer data rather than assuming their existence.

`TowerChernScalarUnit` proves `exists_normalizedScalarUnit`. The coefficient unit
in degree zero is K-flat by the tensor unitor. Its universal scalar counit and
ordinary multiplication supply the derived isomorphism. The ordinary adjunct is
identified sectionwise with `scalarGenerator`; the supplied representative
transpose equation and the exact single comparison give precisely the required
derived normalization. A generic private single-complex adjunct lemma keeps
that calculation independent of the large sheaf-category definitions. This proof
uses the actual scalar model and makes no flatness assumption on the coefficient
map.

Three new modules isolate the still-unformalized integral quotient construction,
finite evaluation calculation, and ordinary tensor/Hom equivalence. Their
statements are independent proper parts of the original argument: the first
contains no scalar extension, finite normalization or twist; the latter two start
with existing Chern data and construct no such data. Each has a complete source
proof and a matching node. No adopted source-library declaration, shared
interface, instance attribute, definition, target, or other existing module was
changed.

## Proved and sorry left

The original one local hole in
`AlgebraicGeometry.ProEtale.DiagonalTrace.exists_diagonalTraceChernTwist` is closed
by a complete combining proof. This is a decomposition, not a complete proof of
the mathematical existence theorem: three lower holes are added, so the local
hole balance is 1 closed minus 3 added = -2.

The new theorem
`AlgebraicGeometry.ProEtale.SpTowerClasses.exists_normalizedScalarUnit`
(`lem-sfb-tower-chern-scalar-unit`) has no local hole. The private coefficient
K-flatness proof and every private Kummer construction/proof have no holes.

Every remaining hole introduced by this delivery is the entire body of one named
public theorem:

- `AlgebraicGeometry.ProEtale.SpTowerClasses.exists_normalizedKummerReduction`
  in `Sheaf.Paper.NormalizedKummerReduction`, node
  `lem-sfb-normalized-kummer-reduction`.
- `AlgebraicGeometry.ProEtale.SpTowerClasses.finiteChernNormalization_of_normalized`
  in `Sheaf.Paper.NormalizedChernFiniteBoundary`, node
  `lem-sfb-normalized-chern-finite-boundary`.
- `AlgebraicGeometry.ProEtale.SpTowerClasses.nonempty_kummerLineTwisting`
  in `Sheaf.Paper.KummerLineTwisting`, node `lem-sfb-kummer-line-twisting`.

There is no `sorry` in the item, the scalar-unit module, a private declaration, or
a definition. The deferred theorems carry the empty-scheme, positive-exponent and
prime-two checks in their proof descriptions. No arbitrary object is defined by
choosing a witness of an unproved mere-existence statement.

## No longer needed

No original public import is removed, and no module is withdrawn. The new
integral-reduction and scalar-unit modules import `TowerClassCoefficients`
instead of the unnecessarily broader `TowerClassChern`. No global
pruning is claimed.

The item's former direct dependencies on `lem-amb-kummer-any-base`,
`lem-coef-semilinear-derived-sections`, `det-sp-coefficient-towers-abelian`,
`lem-pur-derived-change-of-rings`, and `lem-pur-twist-sheaf-locally-free` are
replaced by the actual proof dependencies. The first is reused transitively by
the existing pro-etale Kummer theorem, so it is not globally pruned.
The full geometric `semilinearDerivedSections` package is unnecessary for
constructing scalar data: its proved specialized `semilinearScalarData` suffices.
The abelian-system and derived-change-of-rings results remain ingredients of the
new integral reduction node; the stronger compatible primitive-root covering theorem
`det-def-sp-tate-twist-locally-free` replaces the isolated finite/completed
local-freeness package in the new twisting node. These results have been moved to the step where they are
needed, not discarded or imported merely to follow the old plan.

## Where the brief, the DAG or earlier work was wrong

The old proof plan names general Kummer exactness, system calculus and derived
change of rings. Their existing declarations do not themselves provide the two
specific adjunction-normalized integral reduction isomorphisms, nor the concrete
finite boundary equality or the complete `Twisting` record. The new nodes make
those missing bridges explicit, without weakening a statement or treating
levelwise equality of arbitrary derived arrows as equality of system arrows.

`CategoryTheory.Sheaf.ConstantResidue.kummer_derived_unit` and its isomorphic-kernel
variant were also inspected: they normalize reduction at one fixed modulus,
not the variable-modulus strict tower required by this item. The earlier
`diagonal_kummer_reduction` instead starts from a supplied diagonal-surface
reduction model and has different source data, so it is not a constructor for
this item on an arbitrary scheme. Neither is imported as a spurious solution.

The unit's simultaneous-reduction/Kummer/line-twist route is retained. The
original unit record and its realization fields are unchanged. The original
node already records `det-prop-diagonal-tower-trace` as its blueprint ancestor;
the new nodes retain that provenance through the item and identify the precise
construction step. Searches of the current blueprint found no duplicate of the
three missing bridges.

Generic tools used by the new nodes are `lem-pur-derived-change-of-rings`
(K-flat change of rings on the ringed sequence topos),
`lem-pd-sheaf-scalar-extension-constraint-coherence` (ordinary multiplication on
the scalar-extended unit), `det-def-sp-tate-twist-locally-free` clause (1) (a common covering
and compatible primitive-root generators), and `lem-pc-sheaf-modules-tensor-closed` (the ordinary sheaf
tensor/Hom adjunction). They supply general categorical or line tools, not a
replacement of the unit's geometric argument. No maintainer approval field has
been written by the worker.

## New nodes

`lem-sfb-normalized-kummer-reduction` states just the integral quotient-system
construction with its integer-generator and positive-boundary normalizations.
It is `Sheaf.Paper.NormalizedKummerReduction`. The explicit quotient resolution
has transition `(l, 1)`, and the boundary sign is fixed before finite evaluation.

`lem-sfb-tower-chern-scalar-unit` records the proved unit comparison in
`Sheaf.Paper.TowerChernScalarUnit`, including its exact adjunction normalization.

`lem-sfb-normalized-chern-finite-boundary` states just the finite compatibility
calculation for already normalized Chern data, in
`Sheaf.Paper.NormalizedChernFiniteBoundary`. Its conclusion is an equality of the
actual finite arrows with their specified endpoint transports.

`lem-sfb-kummer-line-twisting` states just the ordinary tensor/Hom equivalence for
the existing scalar-extended root line, in `Sheaf.Paper.KummerLineTwisting`.
Its inverse is the specified internal Hom and its section formulas are part of
the conclusion; it asserts no existence of Chern data.

All four nodes have genuine LeanSearch, LeanFinder and Mathlib-source grep
searches in the session search log. The Kummer helper declarations were independently compiled in a temporary probe
(7.1 seconds); the probe was removed and is not part of the delivery.

Validation: all five final modules compile together in import order through
`lcompile.py --all`, with no errors or warnings. The required delivery server
compile and preflight are the final checks.

No change record is required: the only
existing module changed is the item, with its existing signature and public
interface preserved.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
