## What changed

Proved the assembly of `WeilConjectures.fdWeilPullbackLocalFrobenius` without changing its
signature or `fdWeilLocalEigenvalues`. Added `Sheaf.Paper.WeilPullbackFibreReturn` with a
concrete natural comparison `fdWeilPullbackFibreComparison`, constructed by whiskering
the inverse normalized `zlPullComp` and transporting the specified geometric-point equality.
Its data is constructed directly; no existential witness of an unproved theorem is chosen.

The item proves the heart clause using `zlPull_mem`, proves the closed image and finite
positive residue degree using the finite base field and closed-point criterion, and proves
the residue-cardinality equation using `Module.natCard_eq_pow_finrank`. Two proved private
linear-algebra helpers triangularize the actual endomorphism, compute the diagonal of its
powers, and use conjugation invariance to deduce the multiset equality, retaining algebraic
multiplicity. The only split-off obligation is the closed return equation for the specified
comparison. Updated the parent DAG proof to match this assembly.

## Proved and sorry left

Closed the original hole in `WeilConjectures.fdWeilPullbackLocalFrobenius`
(node `lem-fd-weil-pullback-local-frobenius`), by decomposition.
Added one hole: `WeilConjectures.fdWeilPullbackFibreReturn`
(node `lem-fd-weil-pullback-fibre-return`). It states only the compatibility of the concrete
comparison with the closed return operators. It excludes the closed-image, residue-size,
heart-preservation and eigenvalue conclusions, all proved in the item. Thus one upper hole
is replaced by one strictly narrower obligation; net holes closed minus added is zero.
There are zero `sorry`s in definitions, private helpers, or the item module.

Proved private helpers: `roots_pow`, `closed_image`, `roots_conjugate_power`.
Constructed `fdWeilPullbackFibreComparison` with its naturality inherited from whiskering.

## No longer needed

Removed unused private proof imports from the item:
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`,
`Sheaf.Paper.ConstructiblePullbackTExact`, `Sheaf.Paper.PointSectionsScalarExtension`,
`Sheaf.Paper.IntegralPullbackComparisonRealization`,
`Sheaf.Paper.LocalFrobeniusTransportNormalization`, and
`Sheaf.SixFunctors.FrobeniusPointTransportNatural`.
Kept every original public import. The matrix proofs import only the existing
triangularization, triangular charpoly, and Mathlib conjugation modules.
The new statement-only theorem does not import its planned proof dependencies;
its future prover should import the four interfaces recorded in its DAG proof.

The parent directly needs `def-zl-weil-ind-sheaf-category`,
`lem-kun-closed-point-field`, the proved source-library triangularization tool
`p-linear-triangular`, and the new `lem-fd-weil-pullback-fibre-return` as proof nodes.
The old direct proof dependencies `def-weil-algebraically-closed-coefficients`,
`def-weil-derived-pullback-tensor-hom`, `def-weil-local-frobenius-trace`,
`lem-a1-constructible-pullback-t-exact`,
`lem-trf-integral-pullback-comparison-realization`,
`lem-fd-rational-pullback-fibre-comparison`, `lem-fd-pullback-weil-return-square`,
`lem-fd-rational-return-block-power` and `lem-fd-local-frobenius-coefficient-extension`
are no longer direct dependencies. The finite-stage comparison and return nodes remain
needed below the new statement. Heart t-exactness remains needed below `zlPull_mem`.
No module is withdrawn or claimed globally prunable.

Removed obsolete parent `tool_uses` entries for
`lem-a1-constructible-pullback-t-exact`,
`lem-trf-integral-pullback-comparison-realization`,
`lem-weil-point-sections-scalar-extension`,
`lem-weil-frobenius-point-transport-natural`,
`lem-trf-local-frobenius-transport-normalization`, and
`lem-fd-local-frobenius-coefficient-extension`: those interfaces are now indirect.
Retained the closed-point criterion approval.

## Where the brief, the DAG or earlier work was wrong

The original Lean proof imports predate the current DAG split. The DAG's rational return
square and block-power statements concern specified finite-stage comparison systems;
the actual common-stage heart uses `zlPullComp`, `wfWeilIterate` and `wfPointTransportIterate`.
Identifying their normalization and descending the finite-stage return square is substantive
glue, not a direct application. The new node records precisely this remaining step, with
its source and full proof in words. This delivery makes no claim to have completed it.

Edge cases checked: empty schemes are vacuous; zero fibres give an empty triangular basis;
repeated eigenvalues, including ones merging under powers, keep multiplicities; the matrix
argument also handles exponent zero, while the geometric residue degree is proved positive;
identity morphisms give degree one; no integral Weil-stable lattice, finite Tor-amplitude,
semisimplicity or finite-field assumptions on the coefficient closure are added.
No target, existing public signature, definition, or source-library module is changed.

## New nodes

`lem-fd-weil-pullback-fibre-return`, in
`dag/nodes/sec-deligne-laumon-a1/lem-fd-weil-pullback-fibre-return.json`, owns the concrete
comparison and its one remaining return-square theorem in `Sheaf.Paper.WeilPullbackFibreReturn`.
Its proof uses the existing rational fibre-comparison, same-length return-square, block-power
and coefficient-extension statements. Three logged Mathlib search kinds found no exact
statement. A whole-blueprint search found no matching blueprint node. This is part of
Step 2 of the unchanged realified-kernel route, not a replacement for that unit.
No definition/statement change record or forced adaptation is needed.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
