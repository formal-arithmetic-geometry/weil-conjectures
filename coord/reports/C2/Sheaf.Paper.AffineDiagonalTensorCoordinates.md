## What changed

Filled all three theorem proofs in
`lean/Sheaf/Paper/AffineDiagonalTensorCoordinates.lean`.

`projectionNextAnnihilator` multiplies the existing diagonal annihilator by the
coefficient prime, using the natural-number successor-power and cast identities.

`projectionTensorStep_existsUnique` takes the actual finite-scalar sheaf comparison
as its witness. All presentation parameters are identified using the specified
heterogeneous equalities, including the coefficient ring structure, both sheaves,
and their root-transition map. The resulting normalization is reflexive.
Specializing any other normalized candidate to this actual presentation proves
uniqueness.

`projectionTensorActionIso_existsUnique` specializes the published generic ordered
tensor recursion to the diagonal powers, shifted line, unit constraint and successor
constraints. Pointwise heterogeneous equality identifies the power and successor
families by function extensionality; the remaining normalization parameters are
substituted directly. Specializing any normalized candidate to this tuple proves
uniqueness. Endpoint identifications are definitional, including at degree zero.

All statements, definitions, attributes and public imports are unchanged. No new
imports or auxiliary declarations are needed. The route is exactly the existing
node statement and theorem docstrings, so no DAG changes are needed. The complete
module compiled through lcompile.py with exit code zero and no diagnostics.

## Proved and sorry left

Closed 3 of 3 existing holes, all in node
`def-pur-affine-diagonal-tensor-coordinates`:

- `WeilConjectures.PurityFiniteSetting.projectionNextAnnihilator`.
- `WeilConjectures.PurityFiniteSetting.projectionTensorStep_existsUnique`.
- `WeilConjectures.PurityFiniteSetting.projectionTensorActionIso_existsUnique`.

Zero holes remain in the item module. Zero holes added; zero statements split off.
The existing diagonal annihilator and normalized Tate-coordinate declarations
remain dependencies, with their own proof status unchanged.

## No longer needed

None. No imports removed, no nodes or modules withdrawn. The existing node has no
proof dependencies to prune. Its statement dependencies supply precisely the
coefficient, monoidal, root-line and action definitions used here.

## Where the brief, the DAG or earlier work was wrong

None. The existing pins on both sheaves in `IsProjectionTensorStep` are sufficient:
after substitution, the pinned root-map equality is homogeneous and determines the
raw comparison. No definition or statement repair was required.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
