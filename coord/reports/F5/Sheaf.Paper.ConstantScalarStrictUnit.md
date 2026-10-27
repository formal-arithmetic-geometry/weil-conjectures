## What changed

Proved `WeilConjectures.ConstantScalarStrictUnit.regular_scalar_strict_unit` in
`Sheaf.Paper.ConstantScalarStrictUnit`, retaining its statement and all existing public
definitions verbatim. Added proved private helpers for regular-module scalar multiplication,
finite and identity-extension reduction, compatible quotient coordinates, the strict
mapping-cocone lift, uniqueness, and linear normalization. The proof uses the existing
monoidal right unitor for K-flatness, sectionwise `AlgebraTensorModule.rid` followed by
sheafification for the scalar isomorphisms, and `mappingCocone.lift` for the strict unit.

Added the private proof import
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients` for the tensor functor
instances. All original public imports stay. Local reducibility attributes control repeated
elaboration of chosen reduction witnesses; no public interface changes. The derived clause
projects the recorded witness's K-flat computation property directly, reusing the expressions
of its goal to avoid expensive elaboration of nested dependent existential types. Its generated
term is checked by Lean's kernel.

Updated only `proof` and `proof_origin` of
`lem-weil-constant-scalar-strict-unit` to record these implementations of its original six
steps. No unit route changes, new public declarations, adapted consumers, or change records.

## Proved and sorry left

Closed one hole: `WeilConjectures.ConstantScalarStrictUnit.regular_scalar_strict_unit`
(node `lem-weil-constant-scalar-strict-unit`). All six conjuncts are proved. The item's
module contains zero `sorry`; zero holes added elsewhere and zero statements split off.
All new private helpers are proved. The complete module compiled cleanly through
`lcompile.py` with zero warnings; delivery runs a fresh compile and axiom probe.

## No longer needed

None. No original import, node, or module is withdrawn. The monoidal unitor implements the
regular-complex tensor calculation directly; no separate bounded-above-flat K-flat theorem
or exactness-of-products theorem is imported or needed. All declared dependencies still
provide the definitions used by the six proof steps.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The existing proof plan applies, including zero rings,
the first quotient (`n = 0`), and arbitrary schemes: none of the calculations assumes a
nonzero unit, surjectivity on global sections, exact products, or constructibility. The
scalar tensor API places the finite coefficient in the first tensor factor; the proved
section formulas use that convention. The derived comparison uses its own recorded witness,
without identifying it with an unrelated choice of ordinary scalar-extension functor.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
