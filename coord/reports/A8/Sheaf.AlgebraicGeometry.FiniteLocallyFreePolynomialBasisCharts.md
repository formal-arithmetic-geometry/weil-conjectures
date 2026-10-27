## What changed

Replaced the single `sorry` in
`AlgebraicGeometry.finiteLocallyFree_polynomial_basis_charts` with a complete proof.
The theorem signature and public imports are unchanged. Three proved private helpers
handle the polynomial pullback, extension of a specified basis, and polynomial
localization with its formula on numerator polynomials.

The proof uses Mathlib's polynomial pushout, `polyEquivTensor_symm_apply_tmul`,
`Polynomial.isLocalization`, `IsLocalization.algEquiv`, and `IsBaseChange.basis`.
Localization compatibility is proved by `IsLocalization.ringHom_ext`, reducing the
square first to polynomial numerators and then to the coefficient-map equation
`IsLocalization.map_eq`. The unit-ideal assertion follows by applying `Ideal.map C`.
Finiteness, flatness and local finite presentation follow by base change, and the
source-library `Scheme.Hom.fiberDegree_of_isPullback` preserves the exact degree.

For the sheaf clauses, reuse the proved source-library declarations
`Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom` and
`Scheme.Modules.isFiniteLocallyFreeOfRank_pushforward_unit`, the latter belonging
to `lem-pc-flf-properties` (whose source-library audit is closed). This avoids
rebuilding the associated-sheaf comparison on every principal chart. The added
proof imports are `Mathlib.RingTheory.Localization.Algebra`,
`Mathlib.RingTheory.TensorProduct.IsBaseChangeFree`, and
`WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward`.

The item node's `proof`, `proof_deps`, and `proof_origin` follow this implementation.
No shared definition or interface was changed, and no other Lean module was edited.
The unit's statement and steps are unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.finiteLocallyFree_polynomial_basis_charts`
(node `lem-a1-finite-locally-free-polynomial-basis-charts`).
Added 0 holes; split off 0 statements. There are no `sorry`s left in the delivery.
The three private helpers are proved. The statement retains zero rings, empty
covers, rank zero, and zero or nilpotent localization parameters without any
extra hypotheses. The complete module compiled cleanly with `lcompile.py` in 7.3 seconds
(exit code 0, no warnings). The delivery command runs the remaining required checks.

## No longer needed

Removed the following unused proof imports:

- `Mathlib.RingTheory.TensorProduct.MvPolynomial`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.FlatRank`
- `Mathlib.LinearAlgebra.TensorProduct.Basis`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Mathlib.AlgebraicGeometry.Modules.Tilde`

The univariate polynomial APIs replace the multivariate specialization. The
remaining morphism and module facts are available through the statement imports
and the finite-pushforward module; the direct proof imports above are unnecessary.

Removed these proof dependencies from the item node:

- `lem-weil-pbc-finite-flat-rank-iso`: the exact fibre-degree formula is used directly,
  via affine fibre products and residue-field dimension invariance
  (`lem-pc-finrank-field-base-change`), avoiding a detour through morphism finrank.
- `lem-weil-pbc-principal-localization-open-immersion`
- `lem-weil-pbc-spec-tilde-free-module`
- `lem-weil-pbc-affine-tilde-gamma-adjunction`
- `lem-weil-pbc-pushforward-tilde-spec`
- `lem-weil-pbc-spec-module-tilde-sections`

The last five are unnecessary here because the proved finite locally free
pushforward theorem supplies the sheaf-rank clause and the affine pushforward
theorem supplies quasi-coherence. Their modules and nodes are not withdrawn:
other consumers may still need them.

The definition nodes `def-weil-module-base-change`, `def-weil-affine-spectrum`, and
`def-amb-finite-locally-free-module` remain statement dependencies, but need no
separate proof edges. No module is deleted and no public import is removed.

## Where the brief, the DAG or earlier work was wrong

No statement or source error was found. The planned construction was valid but
longer than needed: the existing source-library finite locally free pushforward
result already proves the sheaf-rank clause, and Mathlib's univariate pushout,
localization and basis APIs avoid repeating the tensor and denominator arguments.
The original theorem docstring describes the valid longer plan; the updated node
and this report record the shorter implemented proof.

Searches used `msearch.py` with LeanFinder, Loogle and grep, plus direct searches
of Mathlib and both project roots. No theorem combines the full conclusion, but
all the generic ingredients used above already exist.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
