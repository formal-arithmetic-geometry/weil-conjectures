## What changed

Proved `WeilConjectures.integral_constructible_internalHom` in
`Sheaf.Paper.IntegralConstructibleInternalHom`, preserving its exact signature and public imports.
The proof uses `integralHomReduction`, the existing canonical comparison normalization,
and `residue_controlled_finite_homs`. Private proved helpers perform the tensor-unit test,
transport support and Tor amplitude through isomorphisms, and convert the legacy integral
predicate to `sfIntegralConstructible` via the existing completeness equivalence.

The existing DAG node now records the comparison normalization and completeness bridge
explicitly. No definition, instance, exported attribute, target or other module was changed.
The tensor-unit and support helpers locally disable two generic model instances
whose inferred coefficient universes otherwise remain ambiguous; each command is
scoped to that private theorem alone.
The unit's recorded route is preserved.

Validation: all added private imports pass `tools/import_direction.py may`; the theorem
signature is byte-for-byte unchanged, the source contains zero `sorry`, and every Lean
line is at most 100 characters. The final module compiled through `lcompile.py` in 31.3 seconds, exit code 0,
with no warnings. The delivery preflight provides the additional axiom checks.

## Proved and sorry left

Closed 1 of 1 original holes: `WeilConjectures.integral_constructible_internalHom`
(node `cor-coef-integral-internal-hom`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered module, including its four private helpers.
This is a proof from the existing declared dependencies; it does not claim those
dependencies' transitive holes are closed.

## No longer needed

Removed these redundant private imports from the item:

- `Sheaf.Algebra.Homology.DerivedTensor` (already available through the statement API).
- `Sheaf.Paper.IntegralResidueTor` (used inside the existing finite-Hom estimate).
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude` (unused alternative predicate).
- `Sheaf.Paper.FiniteConstructibleHom` (used inside the existing finite-Hom estimate).
- `Sheaf.Paper.SfIntegralConstructible` (re-exported by the finite-Hom estimate).
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`
  (the tensor-unit test uses the ringed cochain tensor already in the Tor predicate).

No mathematical dependency node or module is withdrawn: the extracted finite-Hom estimate
retains the residue-Tor and finite-constructible-Hom argument. The dimension-finiteness
tool remains necessary, including for the empty scheme. No top-level tool approval is removed.

## Where the brief, the DAG or earlier work was wrong

The module's docstring describes the original unextracted five-step proof, whereas the
current node uses the already stated `residue_controlled_finite_homs` to package the
finite-level estimates. The implemented proof follows that current node, without changing
the statement. The canonical comparison and legacy/intrinsic completeness APIs require
the existing normalization and equivalence theorems; the updated proof records these
explicitly. The old rework quarantine row is historical: the assigned module is present
in the current source and was copied intact before replacing its proof.

The tensor-unit support test works for zero inputs, and isomorphism transport places no
extra restrictions on test modules. All finite indices remain exponent n+1; index zero
is the residue. The output interval is ordered from a≤b, c≤e, d≥0.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
