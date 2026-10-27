## What changed

Replaced the hole in `completedCoefficientRootLineComparison_exists` by a categorical
inverse-limit argument. The existing statement, public import and definitions are unchanged.
Two new private proof imports state finite-level obligations in their own modules:
`Sheaf.Paper.CompletedRootProjectionLinear` and `Sheaf.Paper.BottomFiniteRootUnitIsIso`.
The proof constructs a cone of linear finite projections, lifts it using preservation of
limits by scalar restriction and the section-module equivalence, and identifies its
underlying map with the given `roots.hom` by the integral limit's universal property.
Naturality of free-module units gives an isomorphism of underlying towers. Its limit,
composed with the forgetful limit comparison, proves that this particular map is invertible.
Reflection of isomorphisms then supplies the required module isomorphism.

Validation: both new statement modules compiled through lcompile.py; the completed item
then compiled successfully against them in 24.0 seconds. The item has no remaining sorry.
This is a decomposition with two new finite-level holes, not a net hole reduction.

The finite-unit module imports only ProEtaleTateTwists and spells out the bottom
intermediate field, avoiding the large diagonal-diagram import closure. The finite-linearity
module imports DiagonalCoefficientMaps directly.

The new finite statements have been checked at n = 0 and on the empty scheme. The finite
unit assertion also holds without invertibility of l: roots are l^(n+1)-torsion regardless.
No primitive root or new coefficient model is chosen. The existing node's proof and proof
dependencies now describe the actual assembly. No other existing module or node changes.

## Proved and sorry left

One original hole is replaced by a complete assembly proof:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedCoefficientRootLineComparison_exists`.
There are zero holes left in the item module. Two holes are added, so this is a decomposition,
not a net proof of the mathematical obligation (one closed, two added, net minus one):

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedRootProjection_linear`, node
  `lem-diagonal-completed-root-projection-linear`, is the finite-projection scalar calculation.
  It asserts linearity to just one finite level and asserts no isomorphism or inverse limit.
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.bottomFiniteRootUnit_isIso`, node
  `lem-diagonal-bottom-finite-root-unit-is-iso`, is the finite torsion tensor identity. It
  mentions no coefficient completion isomorphism, completed line, or root-limit map.

The new holes have complete proof descriptions in their docstrings and DAG nodes.
The limit compatibility, map normalization and invertibility assembly are proved in Lean.

## No longer needed

No original Lean import was removed. The original public import remains necessary for the
statement. The following planned proof dependencies are unnecessary in the item proof:

- `lem-diagonal-integral-root-map` / `Sheaf.Paper.DiagonalIntegralRootMap`: existence and
  uniqueness of IntegralRoots are not needed because roots is an explicit parameter; its
  projection fields already give every normalization used in this proof.
- `lem-pur-twist-sheaf-locally-free` / `Sheaf.Paper.PurTwistSheafLocallyFree`: the assembly
  uses the finite bottom-coefficient torsion tensor identity rather than local generators.
  No compatible primitive-root cover or local-freeness theorem is used.
- `lem-diagonal-completed-coefficient-ring-comparison` /
  `Sheaf.Paper.CompletedCoefficientRingComparison`: the comparison's existence/uniqueness
  theorem is not used; e and he are parameters. Its statement dependency remains, and the
  finite linearity node uses its normalization. This module is not globally pruned.

`sk-def-sp-tate-twist`, the diagonal diagram definitions and the section-module equivalence
remain necessary. No library module is withdrawn, and no claim of global unreachability is
made for the dependencies above.

## Where the brief, the DAG or earlier work was wrong

A direct import of the newly split ProEtaleTateTwistLevels failed against the shared build:
its declarations were still owned by the compiled ProEtaleTateTwists module. The new finite
unit module therefore uses the established public ProEtaleTateTwists import.

The planned dependencies do not state a normalized linear lift to a finite free-root level,
nor invertibility of the actual finite free-module unit for the bottom coefficient field.
The general finite tensor comparison supplies an unnormalized isomorphism and therefore
cannot establish invertibility of the specified unit by itself. Local rank one likewise
does not identify this particular map. Those are the two smaller remaining steps.

The planned compatible-primitive-root-cover argument is unnecessary for the categorical
assembly: a tower of finite isomorphisms gives an isomorphism on limits directly. The unit's
route and every existing statement are preserved. There are no definition repairs, source
library modifications, shared interface changes or forced adaptations.

## New nodes

`lem-diagonal-completed-root-projection-linear`, in
`lean/Sheaf/Paper/CompletedRootProjectionLinear.lean`, isolates the coordinatewise scalar
calculation from step 1 of the original node. Its target is one finite level, and it has
no root-limit-map parameter and no invertibility conclusion. The source is the finite
scalar calculation implicit in paragraph (1) of the diagonal coefficient proof and the
coordinatewise twist construction.

`lem-diagonal-bottom-finite-root-unit-is-iso`, in
`lean/Sheaf/Paper/BottomFiniteRootUnitIsIso.lean`, isolates the finite torsion tensor identity
from step 2. It has no completion, e, he, Noetherian or invertibility hypotheses. Its source
is the finite-level tensor formula of sk-def-sp-tate-twist, specialized to the bottom field.

Both nodes record LeanSearch, Loogle/LeanFinder and source searches, including blueprint-wide
duplicate checks. No change record is needed because all existing signatures and definitions
are unchanged.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
