## What changed

Replaced the sole `sorry` of `Sheaf.AlgebraicGeometry.GoodCurvesBoundaryQuasiFinite`
with a direct proof. The theorem signature and `goodCurvesBoundaryMap` are unchanged.
A private proved helper checks the component pullback squares and proves properness of
coproducts of proper maps over their coproduct bases. The existing finite-coproduct
finiteness instance then makes the whole curve family proper over the base.

For each curve fibre, smoothness over the residue field gives regularity; geometric
connectedness and local Noetherianity give integrality. The existing topological theorem
makes the complement of the nonempty open finite. A finite union over the finite fibres
of the finite base maps contains the boundary fibre. Properness gives the other four
properties, and finite scheme fibres are discrete, giving the required quasi-finiteness.
The node's proof, dependencies and origin now record this route.

## Proved and sorry left

`AlgebraicGeometry.good_curves_boundary_quasiFinite`: one original hole replaced by a
complete proof, verified by the remote compilation and axiom-probe gates of the delivery
dry run. No holes added or split off. The private
`proper_sigmaMap` helper is proved. There are zero textual `sorry` tokens in the module.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.GeometricRegularitySmoothFieldCriterion`: the proved source
  `IsRegular.of_smooth` works directly over arbitrary residue fields.
- `Sheaf.AlgebraicGeometry.RegularNormalDecomposition`: the proved source
  `IsRegular.isIntegral` gives irreducibility directly.
- `Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints`: the proved source topological
  complement-finiteness theorem combines the closed-point and finiteness steps.
- The duplicate non-public import of
  `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`; its original public
  import is retained because the boundary construction uses it.

The following former direct proof dependencies are no longer used separately:

- `def-weil-finite-type-morphism`
- `def-weil-closed-immersion`
- `lem-weil-pbc-proper-base-change`
- `lem-weil-pbc-geometric-regularity-smooth-field-criterion`
- `rem-pc-regular-normal`
- `lem-sc-scheme-sober`
- `lem-sc-dim-one-point-outside-open-closed`
- `lem-sc-noetherian-closed-points-finite`

The dimension-one closed-point argument and sobriety remain encapsulated in the proved
complement-finiteness theorem. The abstract geometric regularity criterion and full
normal decomposition are unnecessary. Proper base change is available directly through
Mathlib instances rather than a separate proof step. Definition nodes remain statement
dependencies where appropriate. Removed obsolete tool approvals for
`rem-pc-regular-normal` and `lem-sc-noetherian-closed-points-finite`; retained the
smooth-fibre criterion approval. No blueprint unit statement or realized step is bypassed.
No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or interface repair. The initial preserved draft had never compiled;
its coproduct-cover comparisons, fibre instances and set coercions needed elaboration
repairs. The initial delivery dry run and single-file compile received no compiler response
(205 and 198 seconds, respectively); a later dry run passed compilation and the axiom probe.
These availability failures did not establish any Lean compilation timeout.
The proof signature and boundary construction were compared with current sources
and are unchanged; the DAG proof dependency union and Lean line width were checked.
Two stale DAG step references and the finite coproduct instance name were corrected.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
