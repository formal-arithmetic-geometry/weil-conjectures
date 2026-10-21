## What changed

Proved all four remaining theorems in `Sheaf.Paper.WeilTensorProduct`.

- `wfRationalTensorHom_exists`: establish bilinearity of sheaf tensor, transport it
  through the homotopy quotient and the stated K-flat localization, prove linearity
  of completion from its reflector unit, and extend the resulting bilinear Hom map
  by tensor-product base change. Tensor induction proves the normalization and uniqueness.
- `wfPullbackCompletion_exists`: compare the actual and constant-presentation
  completeness predicates, including independence of representatives and generators.
  The existing unit-compatible direct-image/completion comparison and the
  automorphism pullback/direct-image adjunction then give preservation of complete
  objects. The reflector Hom bijection constructs the comparison and proves both
  inverse laws and uniqueness.
- `wfCompletePullback_linear`: check completed scalars at finite quotient
  projections, transport the equality to direct-image sections, and use linearity
  of the adjoint pullback and its exact derived functor.
- `wfConstructible_complete`: transport the supplied completeness witness through
  the coefficient equivalence and use the normalized Koszul/quotient comparison
  and tower completeness to reach the specified canonical representative.

All added helpers are private and proved. Existing public statements and public
imports are unchanged. The final Frobenius definition now applies a locally typed
generic construction of the same isomorphism; its hom and inv are identical after
unfolding, and its inverse laws agree by proof irrelevance. This avoids repeated
coefficient-category inference. The change record is
`coord/changes/wfTensorFrobenius-local-construction.md`. Local transparency settings
keep large coefficient and localization constructions behind their interfaces.
The full module compiles in 55.9 seconds with no warnings or errors. The existing
representative comparison now uses proved generic constructions for composition
and uniqueness, retaining its original route. The integral tensor comparison uses
the naturality of the whiskered comparison directly, without unfolding the model.
The scalar comparison simplifies only composition associations and retains the
inverse-image functor as a fixed functor.
The node `def-wf-tensor-product` retains its previous proof steps and records these
four additional arguments and their dependencies. No other module is adapted.
The restored `Sheaf.Paper.CompactSupportProjectionFormula` consumer was read and
compiled unchanged against this module in 57.3 seconds, with no warnings or errors;
its Frobenius-hom identification retains exactly the same meaning.

Added proof imports: `Sheaf.Paper.CompletedPullback`,
`Sheaf.Paper.PbcCompletedPullbackActual`,
`Sheaf.Paper.CompletedKoszulQuotientComparison`,
`Mathlib.CategoryTheory.Localization.Linear`,
`WeilConjectures.Algebra.Homology.BifunctorLinear`,
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Linear`, and
`WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor`.

## Proved and sorry left

Closed 4 of the 4 holes present in the assigned source, all belonging to
`def-wf-tensor-product`:

- `AlgebraicGeometry.Scheme.wfRationalTensorHom_exists`
- `AlgebraicGeometry.Scheme.wfPullbackCompletion_exists`
- `AlgebraicGeometry.Scheme.wfCompletePullback_linear`
- `AlgebraicGeometry.Scheme.wfConstructible_complete`

Added 0 holes; split off 0 statements. No `sorry` remains in the item, and no new
Lean module is delivered. These are complete proofs from the existing stated
library dependencies; this delivery does not claim to close their remaining holes.

## No longer needed

No original import, node, or module is pruned. All existing proof dependencies are
still used somewhere in this module. The completion comparison does not require
rebuilding the degreewise pullback of the Koszul tower here: it uses the existing
unit-compatible direct-image/completion comparison instead. That declaration and
its own proof dependencies remain needed. No unit statement or unit proof step is
bypassed.

## Where the brief, the DAG or earlier work was wrong

The current source contains four holes, rather than the earlier seven-hole count;
prior deliveries had already closed the other three. No mathematical statement
was found false or changed. The former docstring plan for
`wfPullbackCompletion_exists` can be shortened by the existing direct-image
comparison and the adjunction for an automorphism; its docstring and the node now
record that route. The unit is a recorded definition with no realized proof steps
to replace.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
