## What changed

Proved `AlgebraicGeometry.Scheme.FieldConstructibleTensor.field_bounded_constructible_tensor`
in `Sheaf.Paper.FieldBoundedConstructibleTensor`. All existing declaration signatures, public
imports and definition bodies are unchanged. No source-library file is modified.

Private helpers prove the coefficient-sized versions of monoidal pullback, tensor closure of
finite local constant models, common constructible strata, and weak Serre closure. The chart
isomorphism uses the explicit tensor-product basis and `finProdFinEquiv`, including rank zero.
The arbitrary-site constant-ring module equivalence transfers the existing finite-type weak
Serre theorem to fixed-scalar sheaves; exact stratum pullback then transfers it to constructible
intrinsic modules. The normalized flat-single tensor cohomology theorem computes
`H^n(A ⊗ L[0])`. One finite Postnikov induction on the second input proves constructibility
and the support interval `[a+c,b+d]`, including empty input intervals.

Proof-only imports provide these existing interfaces. The original node's proof, proof_deps
and proof_origin now describe this argument. Its statement and Lean attachment are unchanged;
the integral tensor blueprint unit route is retained. There are no new public declarations,
new modules, forced adaptations or withdrawals. The proof-context change record is
`coord/changes/D7-field-constructible-tensor-proof-context.md`; it documents the added opens
and private local instance setup detected by preflight.

Validation: the assigned module compiled successfully through `lcompile.py` in 34.2 seconds;
the final cleaned module is checked again by the delivery command. The first delivery
preflight requested a proof-context change record and pushed nothing; that record is included,
and the private instance registrations are explicitly local to `section TensorProof`. A textual comparison also
verified every existing public import, declaration signature and definition body unchanged.
Every Lean line is at most 100 characters.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.FieldConstructibleTensor.field_bounded_constructible_tensor`
(node `lem-sfb-field-bounded-constructible-tensor`).

Zero holes remain in the item; zero holes were added or split off. All private helpers are
proved. This is a proof from the library's existing declarations, not a decomposition.

## No longer needed

The following original direct proof dependencies are replaced:

- `lem-pur-proetale-constant-module-pullback-composition` and
  `lem-sfb-proetale-fp-local-models-pullback`: use the published coefficient-sized finite-model
  pullback/composition theorem instead of the original-site intrinsic interface.
- `lem-pur-proetale-constant-coefficient-comparison` and
  `lem-weil-pbc-ringed-topoi-module-pullback-tensor`: use constant scalar restriction's
  monoidal equivalence and monoidal fixed-coefficient site pullback directly.
- `lem-sfb-discrete-noetherian-constructible-serre`: prove the coefficient-sized closure
  from the arbitrary-site finite-type locally constant weak Serre theorem, common strata,
  and global constructibility comparison. No coefficient universe equality is assumed.
- `lem-pc-bounded-above-flat-kflat-site`: the retained `singleComparison` already uses
  `lem-weil-pbc-independent-bounded-flat-kflat`; no second bounded-flat criterion is needed.
- `lem-weil-pbc-site-derived-tensor-descent` and `def-pc-tensor-complex-sheaves` are not
  separate proof steps here: the existing normalized single and flat-single comparisons
  provide the required computations. Their underlying constructions remain necessary
  transitively, and `def-pc-tensor-complex-sheaves` remains a statement dependency.

Removed the obsolete `tool_uses` entries for the eight replaced direct proof edges listed
above, retaining the order of the remaining approvals.

Removed proof-only imports:
`Sheaf.Paper.ProEtaleConstantModulePullbackComposition`,
`Sheaf.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModelsPullback`,
`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`,
`Sheaf.CategoryTheory.ModulePullbackTensorIso`,
`Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`,
`Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, and the direct Mathlib
homology-sequence import (provided by the more specific proved homology interfaces).
K-flat resolutions remain used through the published triangulated tensor interface's imports.

The second Postnikov induction is unnecessary: flat-single cohomology computes one variable
for arbitrary unbounded first input. No module or upstream declaration is withdrawn; removal
of these local proof edges does not assert that their modules are globally unused.

## Where the brief, the DAG or earlier work was wrong

The planned original-site discrete Noetherian weak Serre and pullback declarations use
coefficient universes that do not directly match this item's independent coefficient-sized
site. Their mathematics is sufficient, but direct application is not well typed. The existing
arbitrary-site weak Serre theorem and coefficient-sized pullback theorem give the required
interfaces without changing any definition or statement. The plan's two Postnikov inductions
can be shortened to one by the already proved flat-single cohomology comparison.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
